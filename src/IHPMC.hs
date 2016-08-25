--The MIT License (MIT)
--
--Copyright (c) 2016 Steffen Michels (mail@steffen-michels.de)
--
--Permission is hereby granted, free of charge, to any person obtaining a copy of
--this software and associated documentation files (the "Software"), to deal in
--the Software without restriction, including without limitation the rights to use,
--copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the
--Software, and to permit persons to whom the Software is furnished to do so,
--subject to the following conditions:
--
--The above copyright notice and this permission notice shall be included in all
--copies or substantial portions of the Software.
--
--THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
--IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
--FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
--COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
--IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
--CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

{-# LANGUAGE Strict #-}

module IHPMC
    ( ihpmc
    , ihpmcEvidence
    , untilFinished
    , heuristicsCacheComputations
    ) where
import Formula (Formula)
import qualified Formula
import HPT (HPT, HPTNode)
import qualified HPT
import BasicTypes
import Data.HashSet (HashSet)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import qualified Data.HashSet as Set
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import qualified GroundedAST
import GHC.Exts (sortWith)
import Interval (Interval, IntervalLimit(..), LowerUpper(..), (~>), (~<))
import qualified Interval
import Data.Maybe (fromMaybe)
import Control.Monad.State.Strict
import Data.List (maximumBy, subsequences)
import Data.Time.Clock.POSIX (getPOSIXTime)
import Exception
import Data.Foldable (foldl')
--import Exception
--import System.IO.Unsafe (unsafePerformIO)
--import Debug.Trace (trace)

-- number of rfs in primitives, split points + scores
data CachedSplitPoints = CachedSplitPoints Int (HashMap (GroundedAST.RFunc, SplitPoint) Double) deriving (Eq, Generic)
instance Hashable CachedSplitPoints
type FState = Formula.FState CachedSplitPoints

data SplitPoint = DiscreteSplit | ContinuousSplit Rational deriving (Eq, Show, Generic)
instance Hashable SplitPoint

untilFinished :: Int -> ProbabilityBounds -> Bool
untilFinished _ _ = False

ihpmc :: Formula.NodeRef
      -> (Int -> ProbabilityBounds -> Int -> Bool)
      -> Maybe Int
      -> Formula CachedSplitPoints
      -> ExceptionalT String IO [(Int,ProbabilityBounds)]
ihpmc (Formula.RefDeterministic v) _ _ _ = let p = if v then 1.0 else 0.0 in return [(1, ProbabilityBounds p p)]
ihpmc query finishPred mbRepInterval f = do
    t <- doIO getTime
    evalStateT (ihpmc' 1 t t $ HPT.initialNode query) f
        where
        ihpmc' :: Int -> Int -> Int -> HPTNode -> StateT (Formula CachedSplitPoints) (ExceptionalT String IO) [(Int,ProbabilityBounds)]
        ihpmc' i startTime lastReportedTime hptNode = do
            hpt <- state $ runState (ihpmcIterate hptNode 1.0)
            case hpt of
                (HPT.Finished _)              -> return [(i,HPT.bounds hpt)]
                (HPT.Unfinished hptNode' _ _) -> do
                    curTime <- lift $ doIO getTime
                    let bounds = HPT.bounds hpt
                    if finishPred i bounds (curTime - startTime)
                        then return [(i,bounds)]--return $ unsafePerformIO (runExceptionalT (HPT.exportAsDot "/tmp/hpt.dot" hpt >> Formula.exportAsDot "/tmp/f.dot" f) >> return [(i,bounds)])
                        else if case mbRepInterval of Just repInterv -> curTime - lastReportedTime >= repInterv; _ -> False
                            then ihpmc' (succ i) startTime curTime hptNode' >>= \bs -> return ((i,bounds) : bs)
                            else ihpmc' (succ i) startTime lastReportedTime hptNode'

ihpmcEvidence :: Formula.NodeRef
              -> HashSet Formula.NodeRef
              -> (Int -> ProbabilityBounds -> Int -> Bool)
              -> Maybe Int
              -> Formula CachedSplitPoints
              -> ExceptionalT String IO [(Int,ProbabilityBounds)]
ihpmcEvidence query evidence finishPred mbRepInterval f = do
    t <- doIO getTime
    let ((queryAndEvidence, negQueryAndEvidence), f') = runState (do
                qe  <- Formula.insert (Right (Formula.Conditions Map.empty Map.empty)) True Formula.And (Set.insert (queryRef True)  evidence)
                nqe <- Formula.insert (Right (Formula.Conditions Map.empty Map.empty)) True Formula.And (Set.insert (queryRef False) evidence)
                return (qe, nqe)
            )
            f
    evalStateT (ihpmc' 1 t t (initHPT queryAndEvidence) (initHPT negQueryAndEvidence)) f'
    where
    queryRef sign = case query of
        Formula.RefComposed qSign label                 -> Formula.RefComposed (sign == qSign) label
        Formula.RefBuildInPredicate prd prevChoicesReal -> Formula.RefBuildInPredicate (if sign then prd else GroundedAST.negatePred prd) prevChoicesReal
        Formula.RefDeterministic val                    -> Formula.RefDeterministic (val == sign)
    initHPT e = case Formula.entryRef e of
        Formula.RefDeterministic v -> HPT.Finished $ if v then 1.0 else 0.0
        ref                        -> HPT.Unfinished (HPT.initialNode ref) (ProbabilityBounds 0.0 1.0) 1.0

    ihpmc' :: Int -> Int -> Int -> HPT -> HPT -> StateT (Formula CachedSplitPoints) (ExceptionalT String IO) [(Int,ProbabilityBounds)]
    ihpmc' i startTime lastReportedTime qe nqe = lift (doIO getTime) >>= \curTime -> case (qe, nqe) of
        _ | finishPred i bounds (curTime - startTime) -> return [(i, bounds)]
        (HPT.Finished _, HPT.Finished _)              -> return [(i, bounds)]
        _ | HPT.maxError qe > HPT.maxError nqe -> do
            qe' <- iterate' qe
            recurse qe' nqe curTime
        _ -> do
            nqe' <- iterate' nqe
            recurse qe nqe' curTime
        where
        bounds = ProbabilityBounds (lqe / (lqe + unqe)) (uqe / (uqe + lnqe))
            where
            ProbabilityBounds lqe  uqe  = HPT.bounds qe
            ProbabilityBounds lnqe unqe = HPT.bounds nqe

        recurse qe' nqe' curTime =
            if case mbRepInterval of Just repInterv -> curTime - lastReportedTime >= repInterv; _ -> False
            then ihpmc' (succ i) startTime curTime qe' nqe' >>= \bs -> return ((i,bounds) : bs)
            else ihpmc' (succ i) startTime lastReportedTime qe' nqe'

    iterate' :: HPT -> StateT (Formula CachedSplitPoints) (ExceptionalT String IO) HPT
    iterate' (HPT.Unfinished hptNode _ _) = state $ runState (ihpmcIterate hptNode 1.0)
    iterate' (HPT.Finished _) = error "IHPMC.ihpmcEvidence"

ihpmcIterate :: HPTNode -> Double -> FState HPT
ihpmcIterate hptNode partChoiceProb = do
    (hptNode', bounds@(ProbabilityBounds l u), score) <- iterateNode hptNode partChoiceProb
    return $ if l == u then HPT.Finished l
                       else HPT.Unfinished hptNode' bounds score
    where
    iterateNode :: HPTNode -> Double -> FState (HPTNode, ProbabilityBounds, Double)
    iterateNode (HPT.ChoiceBool rFuncLabel p left right) partChoiceProb' = do
        (left', right') <- case (left, right) of
            (HPT.Unfinished hptNode' _ _, _) | HPT.score left > HPT.score right ->
                (,right) <$> ihpmcIterate hptNode' (probToDouble p * partChoiceProb')
            (_, HPT.Unfinished hptNode' _ _) ->
                (left,)  <$> ihpmcIterate hptNode' (probToDouble (1.0 - p) * partChoiceProb')
            _ -> error "finished node should not be selected for iteration"
        return (HPT.ChoiceBool rFuncLabel p left' right', combineProbsChoice p left' right', combineScoresChoice left' right')
    iterateNode (HPT.ChoiceReal rf p splitPoint left right) partChoiceProb' = do
        (left', right') <- case (left, right) of
            (HPT.Unfinished hptNode' _ _, _) | HPT.score left > HPT.score right ->
                (,right) <$> ihpmcIterate hptNode' (probToDouble p * partChoiceProb')
            (_, HPT.Unfinished hptNode' _ _) ->
                (left,)  <$> ihpmcIterate hptNode' (probToDouble (1.0 - p) * partChoiceProb')
            _ -> error "finished node should not be selected for iteration"
        return (HPT.ChoiceReal rf p splitPoint left' right', combineProbsChoice p left' right', combineScoresChoice left' right')
    iterateNode (HPT.Decomposition op dec) partChoiceProb' = do
        selectedChild <- ihpmcIterate selectedChildNode partChoiceProb'
        let dec' = selectedChild:tail sortedChildren
        return (HPT.Decomposition op dec', combineProbsDecomp op dec', combineScoresDecomp dec')
            where
            sortedChildren = sortWith (\c -> -HPT.score  c) dec
            selectedChildNode = case head sortedChildren of
                HPT.Unfinished hptNode' _ _ -> hptNode'
                _                           -> error "finished node should not be selected for iteration"
    iterateNode (HPT.Leaf ref) _ = do
        fEntry <- Formula.augmentWithEntry ref
        case Nothing of --decompose ref f of
            Nothing -> case splitPoint of
                DiscreteSplit -> case rfDef of
                    GroundedAST.Flip p -> do
                        leftEntry  <- Formula.conditionBool fEntry splitRF True
                        rightEntry <- Formula.conditionBool fEntry splitRF False
                        let left  = toHPTNode p leftEntry
                        let right = toHPTNode (1.0 - p) rightEntry
                        return (HPT.ChoiceBool splitRF p left right, combineProbsChoice p left right, combineScoresChoice left right)
                    _ -> error "IHPMC: wrong RF def"
                ContinuousSplit splitPoint' -> case rfDef of
                    GroundedAST.RealDist cdf _ -> do
                        leftEntry  <- Formula.conditionReal fEntry splitRF $ Interval.Interval curLower (Open splitPoint')
                        rightEntry <- Formula.conditionReal fEntry splitRF $ Interval.Interval (Open splitPoint') curUpper
                        let left  = toHPTNode p leftEntry
                        let right = toHPTNode (1.0 - p) rightEntry
                        return (HPT.ChoiceReal splitRF p splitPoint' left right, combineProbsChoice p left right, combineScoresChoice left right)
                            where
                            p = (pUntilSplit-pUntilLower)/(pUntilUpper-pUntilLower)
                            pUntilLower = cdf' cdf True curLower
                            pUntilUpper = cdf' cdf False curUpper
                            pUntilSplit = cdf splitPoint'
                            Interval.Interval curLower curUpper = Map.lookupDefault (Interval.Interval Inf Inf) splitRF rConds
                                where
                                Formula.Conditions _ rConds = Formula.entryChoices fEntry
                    _  -> error "IHPMC: wrong RF def"
                where
                ((splitRF@(GroundedAST.RFunc _ rfDef _), splitPoint), _) = maximumBy (\(_,x) (_,y) -> compare x y) candidateSplitPoints--(trace (show candidateSplitPoints) candidateSplitPoints)
                candidateSplitPoints = Map.toList pts where CachedSplitPoints _ pts = Formula.entryCachedInfo fEntry

                toHPTNode p entry = case Formula.entryNode entry of
                    Formula.Deterministic val -> HPT.Finished $ if val then 1.0 else 0.0
                    _                         -> HPT.Unfinished (HPT.Leaf $ Formula.entryRef entry) (ProbabilityBounds 0.0 1.0) (probToDouble p * partChoiceProb)
            Just _ -> undefined{-Just (origOp, decOp, sign, decomposition) -> do
                htps <- foldlM (\htps dec -> do
                        fresh <- if Set.size dec > 1 then
                                state $ \f -> first Formula.entryRef $ Formula.insert (Right conds) sign origOp dec f
                            else
                                let single = getFirst dec in
                                return $ if sign then single else Formula.negate single
                        return (HPT.Unfinished (HPT.Leaf fresh) (0.0,1.0) partChoiceProb:htps)
                    ) [] decomposition
                return (HPT.Decomposition decOp htps, (0.0,1.0), combineScoresDecomp htps)
                where
                    conds = Formula.entryChoices fEntry-}

combineProbsChoice :: Probability -> HPT -> HPT -> ProbabilityBounds
combineProbsChoice p left right = ProbabilityBounds ((leftLower - rightLower) * p + rightLower) ((leftUpper - rightUpper) * p + rightUpper)
    where
    ProbabilityBounds leftLower  leftUpper  = HPT.bounds left
    ProbabilityBounds rightLower rightUpper = HPT.bounds right

combineProbsDecomp :: Formula.NodeType -> [HPT] -> ProbabilityBounds
combineProbsDecomp Formula.And dec = foldl'
    (\(ProbabilityBounds l u) hpt -> let ProbabilityBounds l' u' = HPT.bounds hpt in ProbabilityBounds (l' * l) (u' * u))
    (ProbabilityBounds 1.0 1.0)
    dec
combineProbsDecomp Formula.Or dec  = ProbabilityBounds (1.0 - nl) (1.0 - nu)
    where
    ProbabilityBounds nl nu = foldl'
        (\(ProbabilityBounds l u) hpt -> let ProbabilityBounds l' u' = HPT.bounds hpt in ProbabilityBounds (l * (1.0 - l')) (u * (1.0 - u')))
        (ProbabilityBounds 1.0 1.0)
        dec

combineScoresChoice :: HPT -> HPT -> Double
combineScoresChoice left right = max (HPT.score left) (HPT.score right)

combineScoresDecomp :: [HPT] -> Double
combineScoresDecomp = foldl' (\score hpt -> max score $ HPT.score hpt) 0.0

{-decompose :: Formula.NodeRef -> Formula CachedSplitPoints -> Maybe (Formula.NodeType, Formula.NodeType, Bool, HashSet (HashSet Formula.NodeRef))
decompose ref f = Nothingcase Formula.entryNode $ Formula.augmentWithEntry ref f of
    Formula.Composed op children -> let dec = decomposeChildren Set.empty $ Set.map (`Formula.augmentWithEntry` f) children
                                in  if Set.size dec == 1 then Nothing else Just (op, decOp op, sign, dec)
    _ -> Nothing
    where
        decomposeChildren :: HashSet (HashSet Formula.RefWithNode) -> HashSet Formula.RefWithNode -> HashSet (HashSet Formula.NodeRef)
        decomposeChildren dec children
            | Set.null children = Set.map (Set.map Formula.entryRef) dec
            | otherwise =
                let first               = getFirst children
                    (new, _, children') = findFixpoint (Set.singleton first) (Formula.entryRFuncs first) (Set.delete first children)
                in  decomposeChildren (Set.insert new dec) children'

        findFixpoint :: HashSet Formula.RefWithNode -> HashSet RFuncLabel -> HashSet Formula.RefWithNode -> (HashSet Formula.RefWithNode, HashSet RFuncLabel, HashSet Formula.RefWithNode)
        findFixpoint cur curRFs children
            | Set.null children || List.null withSharedRFs = (cur, curRFs, children)
            | otherwise                                    = findFixpoint cur' curRFs' children'
            where
                (withSharedRFs, withoutSharedRFs) = List.partition (not . Set.null . Set.intersection curRFs . Formula.entryRFuncs) $ Set.toList children
                cur'      = Set.union cur $ Set.fromList withSharedRFs
                curRFs'   = foldr (\c curRFs -> Set.union curRFs $ Formula.entryRFuncs c) curRFs $ Set.fromList withSharedRFs
                children' = Set.fromList withoutSharedRFs
        decOp op
            | sign = op
            | otherwise = case op of
                Formula.And -> Formula.Or
                Formula.Or  -> Formula.And
        sign = case ref of
            Formula.RefComposed sign _ -> sign
            _                      -> error "nodes other than composed ones have to sign"-}

heuristicsCacheComputations :: Formula.CacheComputations CachedSplitPoints
heuristicsCacheComputations = Formula.CacheComputations
    { Formula.cachedInfoComposed      = heuristicComposed
    , Formula.cachedInfoBuildInPred   = heuristicBuildInPred
    , Formula.cachedInfoDeterministic = heuristicDeterministic
    }

heuristicDeterministic :: Bool -> CachedSplitPoints
heuristicDeterministic = const $ CachedSplitPoints 0 Map.empty

heuristicBuildInPred :: HashMap GroundedAST.RFunc Interval -> GroundedAST.BuildInPredicate -> CachedSplitPoints
heuristicBuildInPred prevChoicesReal prd =
        let predRfs = GroundedAST.predRandomFunctions prd
            nRfs    = Set.size predRfs
        in case prd of
            (GroundedAST.BuildInPredicateBool{}) -> CachedSplitPoints nRfs $ foldl' (\pts rf -> Map.insert (rf, DiscreteSplit) 1.0 pts) Map.empty predRfs -- TODO: weight for constraint with 2 boolean vars
            (GroundedAST.BuildInPredicateStr{}) -> error "IHMC: string-valued random functions not supported"
            (GroundedAST.BuildInPredicateInt{}) -> error "IHMC: integer-valued random functions not supported"
            (GroundedAST.BuildInPredicateReal rPrd) -> case rPrd of
                (GroundedAST.Equality{}) -> error "IHPMC: real equality not implemented"
                (GroundedAST.Constant _) -> CachedSplitPoints nRfs Map.empty
                (GroundedAST.Ineq op exprX exprY) -> CachedSplitPoints
                    nRfs
                    ( snd $ foldl'
                        (\(nSols, splitPs) (rfs, nSols', splitPs') -> if any (\rf -> Map.lookupDefault nRfs rf nSols < length rfs) rfs
                                                                      then (nSols, splitPs)
                                                                      else (Map.union nSols nSols', Map.unionWith (+) splitPs splitPs')
                        )
                        (Map.empty, Map.empty)
                        (splitPoints <$> subsequences (Set.toList predRfs))
                    )
                    where
                    equalSplits = Map.fromList [(rf,equalSplit rf) | rf <- Set.toList predRfs]
                        where
                            equalSplit rf@(GroundedAST.RFunc _ rfDef _) = case rfDef of
                                GroundedAST.RealDist cdf icdf -> icdf ((pUntilLower + pUntilUpper) / 2.0)
                                    where
                                    pUntilLower = cdf' cdf True  curLower
                                    pUntilUpper = cdf' cdf False curUpper
                                    Interval.Interval curLower curUpper = Map.lookupDefault (Interval.Interval Inf Inf) rf prevChoicesReal
                                _ -> error "IHPMC.equalSplit failed"
                    splitPoints rfs
                        | null rfs || null result = (rfs, Map.empty,                             result)
                        | otherwise               = (rfs, Map.fromList [(rf, nRfs') | rf <- rfs], result)
                        where
                        result = Map.filterWithKey notOnBoundary $ foldl'
                            (Map.unionWith (+))
                            Map.empty
                            [ Map.fromList [ ((rf, ContinuousSplit $ splitPoint rf corner), probToDouble $ reduction rfs corner prevChoicesReal)
                                           | rf <- rfs
                                           ]
                            | corner <- remRfsCorners
                            ]

                        notOnBoundary (rf, ContinuousSplit p) _ =    (Interval.rat2IntervLimPoint p ~> Interval.toPoint Lower lower) == Just True
                                                                  && (Interval.rat2IntervLimPoint p ~< Interval.toPoint Upper upper) == Just True
                            where
                            Interval.Interval lower upper = Map.lookupDefault (Interval.Interval Inf Inf) rf prevChoicesReal
                        notOnBoundary (_, DiscreteSplit) _ = error "IHPMC.heuristicBuildInPred.notOnBoundary"

                        reduction [] _ choices
                            | all ((==) $ Just True) checkedCorners || all ((==) $ Just False) checkedCorners = product [pDiff rf choices | rf <- Set.toList remainingRfs]
                            | otherwise                                                                       = 0.0
                                where
                                extremePoints  = Set.map (\rf' -> (rf', Map.lookupDefault (Interval.Interval Inf Inf) rf' choices)) predRfs
                                corners        = Interval.corners $ Set.toList extremePoints
                                checkedCorners = map (GroundedAST.checkRealIneqPred op exprX exprY) corners
                        reduction (rf:rfs') corner choices = pDiff rf chLeft * reduction rfs' corner chLeft + pDiff rf chRight * reduction rfs' corner chRight
                            where
                            splitP  = splitPoint rf corner
                            Interval.Interval curLower curUpper = Map.lookupDefault (Interval.Interval Inf Inf) rf choices
                            chLeft  = Map.insert rf (Interval.Interval curLower (Open splitP)) choices
                            chRight = Map.insert rf (Interval.Interval (Open splitP) curUpper) choices

                        splitPoint rf remRfsCornerPts = (   (fromIntegral nRfs' - 1.0)*equalSplit rf
                                                          + (if rfOnLeft then 1.0 else -1.0) * (sumExpr exprY evalVals - sumExpr exprX evalVals)
                                                        ) / fromIntegral nRfs'
                            where
                            evalVals = Map.union remRfsCornerPts equalSplits
                            rfOnLeft = Set.member rf $ GroundedAST.exprRandomFunctions exprX
                            equalSplit rf' = Map.lookupDefault (error "IHPMC.splitPoint") rf' equalSplits

                            sumExpr :: GroundedAST.Expr GroundedAST.RealN -> Map.HashMap GroundedAST.RFunc Rational-> Rational
                            sumExpr (GroundedAST.ConstantExpr (GroundedAST.RealConstant c)) _ = c
                            sumExpr (GroundedAST.RFuncExpr rf') vals
                                | rf' == rf = 0
                                | otherwise = fromMaybe (error "IHPMC.sumExpr: Just expected") $ Map.lookup rf' vals
                            sumExpr (GroundedAST.Sum x y) vals = sumExpr x vals + sumExpr y vals

                        nRfs' = length rfs

                        remRfsCorners = foldl'
                            (\corners rf -> let Interval.Interval l u = Map.lookupDefault (Interval.Interval Inf Inf) rf prevChoicesReal
                                                mbX                   = Interval.pointRational (Interval.toPoint Lower l)
                                                mbY                   = Interval.pointRational (Interval.toPoint Upper u)
                                                add mbC               = case mbC of
                                                                           Nothing -> []
                                                                           Just c  -> Map.insert rf c <$> corners
                                            in  add mbX ++ add mbY
                            )
                            [Map.empty]
                            remainingRfs

                        remainingRfs = Set.difference predRfs $ Set.fromList rfs

                    pDiff rf@(GroundedAST.RFunc _ rfDef _) choices = pUntilUpper - pUntilLower
                        where
                        pUntilLower = cdf' cdf True  curLower
                        pUntilUpper = cdf' cdf False curUpper
                        Interval.Interval curLower curUpper = Map.lookupDefault (Interval.Interval Inf Inf) rf choices
                        cdf = case rfDef of
                            GroundedAST.RealDist cdf'' _ -> cdf''
                            _ -> error "IHPMC.heuristicBuildInPred.cdf"

heuristicComposed :: HashSet CachedSplitPoints -> CachedSplitPoints
heuristicComposed = foldr
                        ( \(CachedSplitPoints rfsInPrims splitPoints) (CachedSplitPoints rfsInPrims' splitPoints') ->
                          CachedSplitPoints (rfsInPrims + rfsInPrims') $ combineSplitPoints splitPoints splitPoints'
                        )
                        (CachedSplitPoints 0 Map.empty)
    where
    combineSplitPoints :: HashMap (GroundedAST.RFunc, SplitPoint) Double
                       -> HashMap (GroundedAST.RFunc, SplitPoint) Double
                       -> HashMap (GroundedAST.RFunc, SplitPoint) Double
    combineSplitPoints = Map.unionWith (+)

cdf' :: (Rational -> Probability) -> Bool -> IntervalLimit -> Probability
cdf' _ lower Inf      = if lower then 0.0 else 1.0
cdf' cdf _ (Open x)   = cdf x
cdf' cdf _ (Closed x) = cdf x

getTime :: IO Int
getTime = (\x -> fromIntegral (round (x*1000)::Int)) <$> getPOSIXTime
