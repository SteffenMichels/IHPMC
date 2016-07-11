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
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as Map
import qualified AST
import GHC.Exts (sortWith)
import Interval (Interval, IntervalLimit(..), LowerUpper(..), (~>), (~<))
import qualified Interval
import Data.Maybe (fromMaybe)
import Control.Monad.State.Strict
import Data.List (maximumBy, subsequences)
import Data.Time.Clock.POSIX (getPOSIXTime)
--import Exception
--import System.IO.Unsafe (unsafePerformIO)
--import Debug.Trace (trace)

type CachedSplitPoints = (Int, HashMap (RFuncLabel, SplitPoint) Double) -- number of rfs in primitives, split points + scores
type FState = State (Formula CachedSplitPoints)

data SplitPoint = DiscreteSplit | ContinuousSplit Rational deriving (Eq, Show, Generic)
instance Hashable SplitPoint

untilFinished :: Int -> ProbabilityBounds -> Bool
untilFinished _ _ = False

ihpmc :: Formula.NodeRef -> (Int -> ProbabilityBounds -> Int -> Bool) -> Maybe Int -> HashMap RFuncLabel [AST.RFuncDef] -> Formula CachedSplitPoints -> IO [(Int,ProbabilityBounds)]
ihpmc query finishPred mbRepInterval rfuncDefs f = getTime >>= \t -> evalStateT (ihpmc' 1 t t $ HPT.initialNode query) f where-- $ unsafePerformIO (runExceptionalT (Formula.exportAsDot "/tmp/o.dot" f) >> return f) where
    ihpmc' :: Int -> Int -> Int -> HPTNode -> StateT (Formula CachedSplitPoints) IO [(Int,ProbabilityBounds)]
    ihpmc' i startTime lastReportedTime hptNode = do
        f       <- get
        (hpt,f) <- return $ runState (IHPMC.iterate hptNode 1.0 rfuncDefs) f
        put f
        case hpt of
            hpt@(HPT.Finished _)              -> return [(i,HPT.bounds hpt)]
            hpt@(HPT.Unfinished hptNode' _ _) -> do
                curTime <- lift getTime
                let bounds = HPT.bounds hpt
                if finishPred i bounds (curTime - startTime)
                    then return [(i,bounds)]--return $ unsafePerformIO (runExceptionalT (HPT.exportAsDot "/tmp/hpt.dot" hpt >> Formula.exportAsDot "/tmp/f.dot" f) >> return [(i,bounds)])
                    else if case mbRepInterval of Just repInterv -> curTime - lastReportedTime >= repInterv; _ -> False
                        then ihpmc' (i+1) startTime curTime hptNode' >>= \bs -> return ((i,bounds) : bs)
                        else ihpmc' (i+1) startTime lastReportedTime hptNode'

ihpmcEvidence :: Formula.NodeRef -> Formula.NodeRef -> (Int -> ProbabilityBounds -> Int -> Bool) -> Maybe Int -> HashMap RFuncLabel [AST.RFuncDef] -> Formula CachedSplitPoints -> IO [(Int,ProbabilityBounds)]
ihpmcEvidence query evidence finishPred mbRepInterval rfuncDefs f = getTime >>= \t -> evalStateT (do
        queryAndEvidence    <- state $ Formula.insert (Right (Map.empty,Map.empty)) True Formula.And (Set.fromList [queryRef True,  evidence])
        negQueryAndEvidence <- state $ Formula.insert (Right (Map.empty,Map.empty)) True Formula.And (Set.fromList [queryRef False, evidence])
        ihpmc' 1 t t (initHPT queryAndEvidence) (initHPT negQueryAndEvidence)
    ) f where
    queryRef sign = case query of
        Formula.RefComposed qSign label                  -> Formula.RefComposed (sign == qSign) label
        Formula.RefBuildInPredicate pred prevChoicesReal -> Formula.RefBuildInPredicate (if sign then pred else AST.negatePred pred) prevChoicesReal
    initHPT nwr = HPT.Unfinished (HPT.initialNode $ Formula.entryRef nwr) (0.0,1.0) undefined

    ihpmc' :: Int -> Int -> Int -> HPT -> HPT -> StateT (Formula CachedSplitPoints) IO [(Int,ProbabilityBounds)]
    ihpmc' i startTime lastReportedTime qe nqe = lift getTime >>= \curTime -> case (qe, nqe) of
        _ | finishPred i bounds (curTime - startTime) -> return [(i, bounds)]
        (HPT.Finished _, HPT.Finished _)              -> return [(i, bounds)]
        _ | HPT.maxError qe > HPT.maxError nqe -> do
            qe' <- iterate qe
            recurse qe' nqe curTime
        _ -> do
            nqe' <- iterate nqe
            recurse qe nqe' curTime
        where
            bounds = (lqe/(lqe+unqe), uqe/(uqe+lnqe)) where
                (lqe,  uqe)  = HPT.bounds qe
                (lnqe, unqe) = HPT.bounds nqe

            recurse qe nqe curTime =
                if case mbRepInterval of Just repInterv -> curTime - lastReportedTime >= repInterv; _ -> False
                then ihpmc' (i+1) startTime curTime qe nqe >>= \bs -> return ((i,bounds) : bs)
                else ihpmc' (i+1) startTime lastReportedTime qe nqe

    iterate (HPT.Unfinished hptNode _ _) = do
        f <- get
        (hpt',f) <- return $ runState (IHPMC.iterate hptNode 1.0 rfuncDefs) f
        put f
        return hpt'

iterate :: HPTNode -> Double -> HashMap RFuncLabel [AST.RFuncDef] -> FState HPT
iterate hptNode partChoiceProb rfuncDefs = do
    (hptNode', bounds@(l,u), score) <- iterateNode hptNode partChoiceProb
    return $ if l == u then HPT.Finished l
                       else HPT.Unfinished hptNode' bounds score
    where
        iterateNode :: HPTNode -> Double -> FState (HPTNode, ProbabilityBounds, Double)
        iterateNode (HPT.ChoiceBool rFuncLabel p left right) partChoiceProb = do
            (left, right) <- case (left, right) of
                (HPT.Unfinished hptNode _ _, _) | HPT.score left > HPT.score right ->
                    (,right) <$> IHPMC.iterate hptNode (probToDouble p * partChoiceProb) rfuncDefs
                (_, HPT.Unfinished hptNode _ _) ->
                    (left,)  <$> IHPMC.iterate hptNode (probToDouble (1-p) * partChoiceProb) rfuncDefs
                _ -> error "finished node should not be selected for iteration"
            return (HPT.ChoiceBool rFuncLabel p left right, combineProbsChoice p left right, combineScoresChoice left right)
        iterateNode (HPT.ChoiceReal rf p splitPoint left right) partChoiceProb = do
            (left, right) <- case (left, right) of
                (HPT.Unfinished hptNode _ _, _) | HPT.score left > HPT.score right ->
                    (,right) <$> IHPMC.iterate hptNode (probToDouble p * partChoiceProb) rfuncDefs
                (_, HPT.Unfinished hptNode _ _) ->
                    (left,)  <$> IHPMC.iterate hptNode (probToDouble (1-p) * partChoiceProb) rfuncDefs
                _ -> error "finished node should not be selected for iteration"
            return (HPT.ChoiceReal rf p splitPoint left right, combineProbsChoice p left right, combineScoresChoice left right)
        iterateNode (HPT.Decomposition op dec) partChoiceProb = do
            selectedChild <- IHPMC.iterate selectedChildNode partChoiceProb rfuncDefs
            let dec' = selectedChild:tail sortedChildren
            return (HPT.Decomposition op dec', combineProbsDecomp op dec', combineScoresDecomp dec')
            where
                sortedChildren = sortWith (\c -> -HPT.score  c) dec
                selectedChildNode = case head sortedChildren of
                    HPT.Unfinished hptNode _ _ -> hptNode
                    _                          -> error "finished node should not be selected for iteration"
        iterateNode (HPT.Leaf ref) partChoiceProb = do
            fEntry <- state $ Formula.augmentWithEntry ref
            case Nothing of --decompose ref f of
                Nothing -> case splitPoint of
                    DiscreteSplit -> case Map.lookup splitRF rfuncDefs of
                        Just (AST.Flip p:_) -> do
                            leftEntry  <- state $ Formula.conditionBool fEntry splitRF True
                            rightEntry <- state $ Formula.conditionBool fEntry splitRF False
                            let left  = toHPTNode p leftEntry
                            let right = toHPTNode (1-p) rightEntry
                            return (HPT.ChoiceBool splitRF p left right, combineProbsChoice p left right, combineScoresChoice left right)
                        _ -> error ("undefined rfunc " ++ splitRF)
                    ContinuousSplit splitPoint -> case Map.lookup splitRF rfuncDefs of
                        Just (AST.RealDist cdf _:_) -> do
                            leftEntry  <- state $ Formula.conditionReal fEntry splitRF (curLower, Open splitPoint)
                            rightEntry <- state $ Formula.conditionReal fEntry splitRF (Open splitPoint, curUpper)
                            let left  = toHPTNode p leftEntry
                            let right = toHPTNode (1-p) rightEntry
                            return (HPT.ChoiceReal splitRF p splitPoint left right, combineProbsChoice p left right, combineScoresChoice left right)
                            where
                                p = (pUntilSplit-pUntilLower)/(pUntilUpper-pUntilLower)
                                pUntilLower = cdf' cdf True curLower
                                pUntilUpper = cdf' cdf False curUpper
                                pUntilSplit = cdf splitPoint
                                (curLower, curUpper) = Map.lookupDefault (Inf, Inf) splitRF $ snd $ Formula.entryChoices fEntry
                        _  -> error ("undefined rfunc " ++ splitRF)
                    where
                        ((splitRF, splitPoint), _) = maximumBy (\(_,x) (_,y) -> compare x y) candidateSplitPoints--(trace (show candidateSplitPoints) candidateSplitPoints)
                        candidateSplitPoints = Map.toList $ snd $ Formula.entryCachedInfo fEntry

                        toHPTNode p entry = case Formula.entryNode entry of
                            Formula.Deterministic val -> HPT.Finished $ if val then 1.0 else 0.0
                            _                         -> HPT.Unfinished (HPT.Leaf $ Formula.entryRef entry) (0.0,1.0) (probToDouble p * partChoiceProb)
                Just (origOp, decOp, sign, decomposition) -> undefined {-do
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

combineProbsChoice p left right = ((leftLower-rightLower)*p+rightLower, (leftUpper-rightUpper)*p+rightUpper) where
    (leftLower,  leftUpper)  = HPT.bounds left
    (rightLower, rightUpper) = HPT.bounds right
combineProbsDecomp Formula.And dec = foldr (\hpt (l,u) -> let (l',u') = HPT.bounds hpt in (l'*l,u'*u)) (1.0, 1.0) dec
combineProbsDecomp Formula.Or dec  = (1-nl, 1-nu) where
    (nl, nu) = foldr (\hpt (l,u) -> let (l',u') = HPT.bounds hpt in (l*(1.0-l'), u*(1.0-u'))) (1.0, 1.0) dec

combineScoresChoice left right = max (HPT.score left) (HPT.score right)
combineScoresDecomp            = foldr (\hpt score -> max score $ HPT.score hpt) 0.0

decompose :: Formula.NodeRef -> Formula CachedSplitPoints -> Maybe (Formula.NodeType, Formula.NodeType, Bool, HashSet (HashSet Formula.NodeRef))
decompose ref f = Nothing{-case Formula.entryNode $ Formula.augmentWithEntry ref f of
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
                curRFs'   = Set.foldr (\c curRFs -> Set.union curRFs $ Formula.entryRFuncs c) curRFs $ Set.fromList withSharedRFs
                children' = Set.fromList withoutSharedRFs
        decOp op
            | sign = op
            | otherwise = case op of
                Formula.And -> Formula.Or
                Formula.Or  -> Formula.And
        sign = case ref of
            Formula.RefComposed sign _ -> sign
            _                      -> error "nodes other than composed ones have to sign"-}

heuristicsCacheComputations rfDefs = Formula.CacheComputations
    { Formula.cachedInfoComposed      = heuristicComposed
    , Formula.cachedInfoBuildInPred   = heuristicBuildInPred rfDefs
    , Formula.cachedInfoDeterministic = heuristicDeterministic
    }

heuristicDeterministic :: Bool -> CachedSplitPoints
heuristicDeterministic = const (0, Map.empty)

heuristicBuildInPred :: HashMap RFuncLabel [AST.RFuncDef] -> HashMap RFuncLabel Interval -> AST.BuildInPredicate -> CachedSplitPoints
heuristicBuildInPred rfDefs prevChoicesReal pred =
        let predRfs = AST.predRandomFunctions pred
            nRfs    = Set.size predRfs
        in case pred of
            (AST.BoolEq{})                -> (nRfs, Set.foldr (\rf -> Map.insert (rf, DiscreteSplit) 1.0) Map.empty predRfs) -- TODO: weight for constraint with 2 boolean vars
            (AST.Constant _)              -> (nRfs, Map.empty)
            (AST.RealIneq op exprX exprY) -> (nRfs, snd $ foldl
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
                            equalSplit rf = case Map.lookup rf rfDefs of
                                Just (AST.RealDist cdf icdf:_) -> icdf ((pUntilLower + pUntilUpper)/2)
                                    where
                                        pUntilLower = cdf' cdf True  curLower
                                        pUntilUpper = cdf' cdf False curUpper
                                        (curLower, curUpper) = Map.lookupDefault (Inf, Inf) rf prevChoicesReal
                                _ -> error "IHPMC.equalSplit failed"
                    splitPoints rfs
                        | null rfs || null result = (rfs, Map.empty,                             result)
                        | otherwise               = (rfs, Map.fromList [(rf, nRfs) | rf <- rfs], result)
                        where
                            result = Map.filterWithKey notOnBoundary $ foldr (Map.unionWith (+)) Map.empty [Map.fromList [((rf, ContinuousSplit $ splitPoint rf corner), probToDouble $ reduction rfs corner prevChoicesReal) | rf <- rfs] | corner <- remRfsCorners rfs]

                            notOnBoundary (rf, ContinuousSplit p) _ = (Interval.rat2IntervLimPoint p ~> Interval.toPoint Lower lower) == Just True && (Interval.rat2IntervLimPoint p ~< Interval.toPoint Upper upper) == Just True where
                                (lower,upper) = Map.lookupDefault (Inf,Inf) rf prevChoicesReal

                            reduction [] _ choices
                                | all ((==) $ Just True) checkedCorners || all ((==) $ Just False) checkedCorners = product [pDiff rf choices | rf <- Set.toList remainingRfs]
                                | otherwise                                                                       = 0.0
                                    where
                                        extremePoints  = Set.map (\rf' -> (rf', Map.lookupDefault (Inf,Inf) rf' choices)) predRfs
                                        corners        = Interval.corners $ Set.toList extremePoints
                                        checkedCorners = map (AST.checkRealIneqPred op exprX exprY) corners
                            reduction (rf:rfs) corner choices = pDiff rf chLeft * reduction rfs corner chLeft + pDiff rf chRight * reduction rfs corner chRight
                                where
                                    splitP  = splitPoint rf corner
                                    (curLower,curUpper) = Map.lookupDefault (Inf,Inf) rf choices
                                    chLeft  = Map.insert rf (curLower, Open splitP) choices
                                    chRight = Map.insert rf (Open splitP, curUpper) choices

                            splitPoint rf remRfsCornerPts = ((fromIntegral nRfs-1)*equalSplit rf + (if rfOnLeft then 1 else -1) * (sumExpr exprY evalVals - sumExpr exprX evalVals))/fromIntegral nRfs
                                where
                                    evalVals = Map.union remRfsCornerPts equalSplits
                                    rfOnLeft = Set.member rf $ AST.exprRandomFunctions exprX
                                    equalSplit rf = Map.lookupDefault (error "IHPMC.splitPoint") rf equalSplits

                                    sumExpr :: AST.Expr AST.RealN -> Map.HashMap RFuncLabel Rational-> Rational
                                    sumExpr (AST.RealConstant c) _ = c
                                    sumExpr (AST.UserRFunc rf') vals
                                        | rf' == rf = 0
                                        | otherwise = fromMaybe (error "IHPMC.sumExpr: Just expected") $ Map.lookup rf' vals
                                    sumExpr (AST.RealSum x y) vals = sumExpr x vals + sumExpr y vals

                            nRfs = length rfs

                            remRfsCorners rfs = Set.foldr
                                (\rf corners -> let (l,u)   = Map.lookupDefault (Inf, Inf) rf prevChoicesReal
                                                    mbX     = Interval.pointRational (Interval.toPoint Lower l)
                                                    mbY     = Interval.pointRational (Interval.toPoint Upper u)
                                                    add mbC = case mbC of
                                                       Nothing -> []
                                                       Just c  -> Map.insert rf c <$> corners
                                                in  add mbX ++ add mbY
                                )
                                [Map.empty]
                                remainingRfs

                            remainingRfs = Set.difference predRfs $ Set.fromList rfs

                    pDiff rf choices = pUntilUpper - pUntilLower where
                        pUntilLower = cdf' cdf True  curLower
                        pUntilUpper = cdf' cdf False curUpper
                        (curLower,curUpper) = Map.lookupDefault (Inf,Inf) rf choices
                        (cdf, icdf) = case Map.lookup rf rfDefs of
                            Just (AST.RealDist cdf icdf:_) -> (cdf, icdf)

heuristicComposed :: HashSet CachedSplitPoints -> CachedSplitPoints
heuristicComposed = Set.foldr
    (\(rfsInPrims,splitPoints) (rfsInPrims', splitPoints') -> (rfsInPrims + rfsInPrims', combineSplitPoints splitPoints splitPoints'))
    (0, Map.empty)
    where
        combineSplitPoints :: HashMap (RFuncLabel, SplitPoint) Double -> HashMap (RFuncLabel, SplitPoint) Double -> HashMap (RFuncLabel, SplitPoint) Double
        combineSplitPoints = Map.unionWith (+)

cdf' _ lower Inf      = if lower then 0.0 else 1.0
cdf' cdf _ (Open x)   = cdf x
cdf' cdf _ (Closed x) = cdf x

getTime = fmap (\x -> fromIntegral (round (x*1000)::Int)) getPOSIXTime