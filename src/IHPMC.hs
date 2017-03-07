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
    , heuristicsCacheComputations
    , HPT.CachedSplitPoints
    ) where
import Formula (Formula)
import qualified Formula
import HPT (HPT)
import qualified HPT
import Data.HashSet (Set)
import qualified Data.HashSet as Set
import Data.HashMap (Map)
import qualified Data.HashMap as Map
import qualified GroundedAST
import Interval (Interval, IntervalLimit(..), LowerUpper(..), (~>), (~<))
import qualified Interval
import Data.Maybe (fromMaybe)
import Control.Monad.State.Strict
import qualified Data.List as List
import Data.Time.Clock.POSIX (getPOSIXTime)
import Exception
import Data.Foldable (foldl')
import Probability
import Data.Text (Text)
import Control.Arrow (second)
import Data.Ratio

type FState = Formula.FState HPT.CachedSplitPoints

ihpmc :: Formula.NodeRef
      -> [Formula.NodeRef]
      -> (Int -> ProbabilityBounds -> Int -> Bool)
      -> (Int -> ProbabilityBounds -> Int -> Int -> Maybe (ExceptionalT IOException IO ()))
      -> Formula HPT.CachedSplitPoints
      -> ExceptionalT IOException IO (Int, Int, Maybe ProbabilityBounds, Formula HPT.CachedSplitPoints)
ihpmc query evidence finishPred reportingIO f = do
    t <- doIO getTime
    ((n, et, mbBounds), f') <- runStateT
        ( do
            evidenceConj <- state $ runState $ do
                evidence' <- forM evidence Formula.augmentWithEntry
                Formula.insert
                    Formula.evidenceComposedLabel
                    True
                    Formula.And
                    evidence'
            initHpt <- state $ runState $ HPT.initialHPT query $ Formula.entryRef evidenceConj
            ihpmc' 1 t t initHpt
        ) f
    return (n, et, mbBounds, f')
    where
    ihpmc' :: Int
           -> Int
           -> Int
           -> HPT
           -> StateT (Formula HPT.CachedSplitPoints) (ExceptionalT IOException IO) (Int, Int, Maybe ProbabilityBounds)
    ihpmc' i startTime lastReportedTime hpt = do
        mbHpt <- state $ runState $ ihpmcIterate hpt
        curTime <- lift $ doIO getTime
        let runningTime = curTime - startTime
        case mbHpt of
            Nothing -> return (i, runningTime, HPT.bounds hpt)
            Just hpt' -> do
                let bounds = HPT.bounds hpt'
                case bounds of
                    Just bs | not $ finishPred i bs runningTime -> case reportingIO i bs runningTime (lastReportedTime - startTime) of
                        Just repIO -> lift repIO >> ihpmc' (succ i) startTime curTime hpt'
                        Nothing    ->               ihpmc' (succ i) startTime lastReportedTime hpt'
                    _ -> return (i, runningTime, bounds)

    ihpmcIterate :: HPT -> FState (Maybe HPT)
    ihpmcIterate hpt = case HPT.nextLeaf hpt of
        Nothing -> return Nothing
        Just (HPT.HPTLeaf fs p cachedProofs, hpt') -> case fs of
            HPT.WithinEv q _ -> do
                qEntry        <- Formula.augmentWithEntry q
                let (mbSpPoint, cProofsL, cProofsR) =  splitPoint qEntry cachedProofs
                case mbSpPoint of
                    Nothing -> return Nothing
                    Just spPoint -> do
                        (ql, _, qr, _, pl) <- splitFormula qEntry Nothing spPoint
                        Formula.dereference q
                        let pr =  1.0 - pl
                        hpt''  <- HPT.addLeafWithinEvidence ql (pl * p) cProofsL hpt'
                        hpt''' <- HPT.addLeafWithinEvidence qr (pr * p) cProofsR hpt''
                        return $ Just hpt'''
            HPT.MaybeWithinEv q e _ -> do
                eEntry      <- Formula.augmentWithEntry e
                let (mbSpPoint, cProofsL, cProofsR) =  splitPoint eEntry cachedProofs
                case mbSpPoint of
                    Nothing -> return Nothing
                    Just spPoint -> do
                        (el, Just ql, er, Just qr, pl) <- splitFormula eEntry (Just q) spPoint
                        Formula.dereference e
                        when (Formula.deterministicNodeRef el /= Just False && Formula.deterministicNodeRef er /= Just False)
                             (Formula.reference query) -- new lazy formula refers to initial query
                        let pr =  1.0 - pl
                        hpt'' <- HPT.addLeaf ql el (pl * p) cProofsL hpt'
                        Just <$> HPT.addLeaf qr er (pr * p) cProofsR hpt''

data ProofCounters = ProofCounters (Map Int Int) Int deriving Eq-- last arg: max length of proof

instance Ord ProofCounters where
    compare (ProofCounters countsX maxLengthX) (ProofCounters countsY maxLengthY) = compare' 1
        where
        compare' i
            | i > maxLengthX || i > maxLengthY = compare maxLengthX maxLengthY
            | otherwise = case compare (Map.findWithDefault 0 i countsX) (Map.findWithDefault 0 i countsY) of
                EQ  -> compare' $ succ i
                res -> res

splitPoint :: Formula.RefWithNode HPT.CachedSplitPoints -> Set HPT.Proof -> (Maybe HPT.SplitPoint, Set HPT.Proof, Set HPT.Proof)
splitPoint f cachedProofs
    | null candidateSplitPoints = (Nothing, Set.empty, Set.empty)
    | Set.null cachedProofs = let newProofs = Set.union proofsT proofsF
                              in if Set.null newProofs
                                 then ( Just $ fst $ List.maximumBy (\(_,x) (_,y) -> compare x y) candidateSplitPoints
                                      , Set.empty
                                      , Set.empty
                                      )
                                 else splitWithProofs newProofs
    | otherwise             = splitWithProofs cachedProofs
    where
    HPT.CachedSplitPoints proofsT proofsF spType = Formula.entryCachedInfo f
    candidateSplitPoints = case spType of
        HPT.Composed pts  -> Map.toList pts
        HPT.Primitive pts -> (, 0) <$> Set.toList pts

    splitWithProofs :: Set HPT.Proof -> (Maybe HPT.SplitPoint, Set HPT.Proof, Set HPT.Proof)
    splitWithProofs proofs = (Just splitPt, condCachedProofs splitPt HPT.Left proofs, condCachedProofs splitPt HPT.Right proofs)
        where
        splitPt = fst $ List.maximumBy (\(_,x) (_,y) -> compare x y) (attachScores <$> candidateSplitPoints)

        attachScores :: (HPT.SplitPoint, Int)
                     -> (HPT.SplitPoint, (ProofCounters, Int))
        attachScores (pt, score) =
            ( pt
            , ( Map.findWithDefault (ProofCounters Map.empty 0) pt proofCounters
              , score
              )
            )

        proofCounters :: Map HPT.SplitPoint ProofCounters
        proofCounters = Set.fold
            ( \(HPT.Proof p) counts-> let lengthProof = Map.size p in Map.foldWithKey
                ( \pt _ counts' -> Map.insert
                    pt
                    ( case Map.lookup pt counts' of
                        Nothing -> ProofCounters (Map.singleton lengthProof 1) lengthProof
                        Just (ProofCounters cs maxLenProofs) ->
                            ProofCounters (Map.alter (Just . maybe 1 succ) lengthProof cs) $ max lengthProof maxLenProofs
                    )
                    counts'
                )
                counts
                p
            )
            Map.empty
            proofs

    condCachedProofs :: HPT.SplitPoint -> HPT.Choice -> Set HPT.Proof -> Set HPT.Proof
    condCachedProofs splitPt choice = Set.filter (\(HPT.Proof p) -> not $ Map.null p) . Set.map
        ( \proof@(HPT.Proof pMap) -> case Map.lookup splitPt pMap of
            Nothing -> proof
            Just choice'
                | choice == choice' -> HPT.Proof $ Map.delete splitPt pMap
                | otherwise         -> HPT.Proof Map.empty
        )

splitFormula :: Formula.RefWithNode HPT.CachedSplitPoints
             -> Maybe HPT.LazyNode
             -> HPT.SplitPoint
             -> FState (Formula.NodeRef, Maybe HPT.LazyNode, Formula.NodeRef, Maybe HPT.LazyNode, Probability)
splitFormula f lf (HPT.BoolSplit splitPF) = splitFormulaCommon f lf pLeft addCond True False
    where
    GroundedAST.Flip pLeft = GroundedAST.probabilisticFuncDef splitPF
    pfLabel = GroundedAST.probabilisticFuncLabel splitPF
    addCond val conds = conds{Formula.boolConds = Map.insert pfLabel val $ Formula.boolConds conds}
splitFormula f lf (HPT.StringSplit splitPF splitSet) = splitFormulaCommon f lf pLeft addCond splitSet splitSetCompl
    where
    splitSetCompl                   = Set.difference curSet splitSet
    curSet                          = Map.findWithDefault
                                          (Set.fromList $ snd <$> elements)
                                          (GroundedAST.probabilisticFuncLabel splitPF)
                                          sConds
    Formula.Conditions _ sConds _ _ = Formula.entryChoices f
    GroundedAST.StrDist elements    = GroundedAST.probabilisticFuncDef splitPF
    pLeft                           = List.sum [p | (p, val) <- curElements, Set.member val splitSet] / z
    z                               = List.sum $ fst <$> curElements
    curElements                     = List.filter ((`Set.member` curSet) . snd) elements
    pfLabel                         = GroundedAST.probabilisticFuncLabel splitPF
    addCond val conds               = conds{Formula.stringConds = Map.insert pfLabel val $ Formula.stringConds conds}
-- we assume here that the splitObj is within the set given by the current conditions,
-- otherwise the formula would have already been simplified
--splitFormula f lf (ObjectIntervSplit splitPf splitObj) = undefined
splitFormula f lf (HPT.ObjectIntervSplit splitPf splitObj) = case GroundedAST.probabilisticFuncDef splitPf of
    GroundedAST.UniformObjDist _ -> splitFormulaCommon f lf pLeft (addCondObj splitPf) leftCond rightCond -- TODO: can probabilties become 1.0/0.0?
    GroundedAST.UniformOtherObjDist _ -> error "not implemented"
    where
    pLeft = case possibleValues of
        Formula.Object _                           -> error "object PF restricted to single object should never be selected to split on"
        Formula.AnyExcept excl                     -> p 0 upto' (nrObjects - 1) excl
        Formula.InInterval from upto               -> p from upto' upto Set.empty
        Formula.AnyExceptInInterval excl from upto -> p from upto' upto excl
        where
        upto' = splitObj
        p :: Integer -> Integer -> Integer -> Set Integer -> Probability
        p from uptoSplit  upto excl = ratToProb $
            (uptoSplit - from + 1 - fromIntegral (Set.size $ filterExcl from uptoSplit excl)) %
            (upto      - from + 1 - fromIntegral (Set.size excl))

    -- TODO: corner cases: interval collapses to single point
    leftCond  = case possibleValues of
        Formula.Object _                        -> error "object PF restricted to single object should never be selected to split on"
        Formula.AnyExcept excl                  -> anyExceptInInterval 0    upto' excl
        Formula.InInterval from _               -> inInterval          from upto'
        Formula.AnyExceptInInterval excl from _ -> anyExceptInInterval from upto' excl
        where
        upto' = splitObj
    rightCond = case possibleValues of
        Formula.Object _                        -> error "object PF restricted to single object should never be selected to split on"
        Formula.AnyExcept excl                  -> anyExceptInInterval from' (nrObjects - 1) excl
        Formula.InInterval _ upto               -> inInterval          from' upto
        Formula.AnyExceptInInterval excl _ upto -> anyExceptInInterval from' upto excl
        where
        from' = splitObj + 1

    possibleValues = Map.findWithDefault
        (Formula.InInterval 0 $ nrObjects - 1)
        (GroundedAST.probabilisticFuncLabel splitPf)
        oConds

    nrObjects = GroundedAST.objectPfNrObjects splitPf
    anyExceptInInterval from upto excl | from == upto = if Set.member from excl then error "TODO: deal with inconsistency"
                                                                                else Formula.Object from
                                       | otherwise = Formula.AnyExceptInInterval (filterExcl from upto excl) from upto

    inInterval from upto | from == upto = Formula.Object from
                         | otherwise    = Formula.InInterval from upto
    filterExcl from upto = Set.filter (\e -> e >= from && e <= upto)
    Formula.Conditions _ _ _ oConds = Formula.entryChoices f
splitFormula f lf (HPT.ObjectSplit splitPf splitObj) = case GroundedAST.probabilisticFuncDef splitPf of
    GroundedAST.UniformObjDist _ -> splitObjFormula $ 1 / nPossibilities
    GroundedAST.UniformOtherObjDist otherPf -> case possibleValues otherPf oConds of
        Formula.Object otherObj
            | otherObj == splitObj -> splitObjFormula 0.0
            | otherwise -> splitObjFormula $
                1 / if inCurPossibleValues otherObj then nPossibilities - 1
                                                    else nPossibilities
        _ | splitPfInPossibleValuesOf otherPf ->
            -- we cannot split current PF, split parent PF
            splitFormula f lf $ HPT.ObjectSplit otherPf splitObj
        _ -> splitObjFormula $ 1 / (nPossibilities - 1)
    where
    splitObjFormula :: Probability -> FState (Formula.NodeRef, Maybe HPT.LazyNode, Formula.NodeRef, Maybe HPT.LazyNode, Probability)
    splitObjFormula pLeft
        | pLeft == 1.0 = do -- right branch has probability 0
            left  <- Formula.condition f $ addCondObj splitPf leftCond Formula.noConditions
            return ( Formula.entryRef left
                   , second (addCondObj splitPf leftCond) <$> lf
                   , Formula.refDeterministic False
                   , const (Formula.refDeterministic False, Formula.noConditions) <$> lf
                   , 1.0
                   )
        | pLeft == 0.0 = do
            right <- Formula.condition f $ addCondObj splitPf rightCond Formula.noConditions
            return ( Formula.refDeterministic False
                   , const (Formula.refDeterministic False, Formula.noConditions) <$> lf
                   , Formula.entryRef right
                   , second (addCondObj splitPf rightCond) <$> lf
                   , 0.0
                   )
        | otherwise = splitFormulaCommon f lf pLeft (addCondObj splitPf) leftCond rightCond

    nPossibilities :: Probability
    nPossibilities = case possibleValues splitPf oConds of
        Formula.Object _                           -> error "object PF restricted to single object should never be selected to split on"
        Formula.AnyExcept excl                     -> intToProb $ nr splitPf - fromIntegral (Set.size excl)
        Formula.InInterval from upto               -> intToProb $ upto - from + 1
        Formula.AnyExceptInInterval excl from upto -> intToProb $ upto - from + 1 - fromIntegral (Set.size excl)

    nr :: GroundedAST.PFunc GroundedAST.Object -> Integer
    nr pf = case GroundedAST.probabilisticFuncDef pf of
        GroundedAST.UniformObjDist nr'          -> nr'
        GroundedAST.UniformOtherObjDist otherPf -> nr otherPf

    Formula.Conditions _ _ _ oConds = Formula.entryChoices f

    possibleValues :: GroundedAST.PFunc GroundedAST.Object
                   -> Map GroundedAST.PFuncLabel Formula.ObjCondition
                   -> Formula.ObjCondition
    possibleValues pf = Map.findWithDefault
        (Formula.AnyExcept Set.empty)
        (GroundedAST.probabilisticFuncLabel pf)

    inCurPossibleValues :: Integer -> Bool
    inCurPossibleValues obj = case possibleValues splitPf oConds of
        Formula.Object _                           -> error "object PF restricted to single object should never be selected to split on"
        Formula.AnyExcept excl                     -> not $ Set.member obj excl
        Formula.InInterval from upto               -> from <= obj && obj <= upto
        Formula.AnyExceptInInterval excl from upto -> from <= obj && obj <= upto && not (Set.member obj excl)

    splitPfInPossibleValuesOf :: GroundedAST.PFunc GroundedAST.Object -> Bool
    splitPfInPossibleValuesOf pf = case possibleValues pf oConds of
        Formula.Object _                           -> undefined
        Formula.AnyExcept excl                     -> not $ Set.member splitObj excl
        Formula.InInterval from upto               -> from <= splitObj && splitObj <= upto
        Formula.AnyExceptInInterval excl from upto -> from <= splitObj && splitObj <= upto && not (Set.member splitObj excl)

    leftCond  = Formula.Object splitObj
    rightCond = case possibleValues splitPf oConds of
        Formula.Object _                           -> error "object PF restricted to single object should never be selected to split on"
        Formula.AnyExcept excl                     -> Formula.AnyExcept $ Set.insert splitObj excl
        Formula.InInterval from upto               -> Formula.AnyExceptInInterval (Set.singleton splitObj) from upto
        Formula.AnyExceptInInterval excl from upto -> Formula.AnyExceptInInterval (Set.insert splitObj excl) from upto

splitFormula f lf (HPT.ContinuousSplit splitPF spPoint) = splitFormulaCommon f lf pLeft addCond leftCond rightCond
    where
    leftCond  = Interval.Interval curLower (Open spPoint)
    rightCond = Interval.Interval (Open spPoint) curUpper
    pLeft = (pUntilSplit - pUntilLower) / (pUntilUpper - pUntilLower)
    pUntilLower = cdf' cdf True curLower
    pUntilUpper = cdf' cdf False curUpper
    pUntilSplit = cdf spPoint
    Interval.Interval curLower curUpper = Map.findWithDefault
                                              (Interval.Interval Inf Inf)
                                              (GroundedAST.probabilisticFuncLabel splitPF)
                                              rConds
    rConds = Formula.realConds $ Formula.entryChoices f
    GroundedAST.RealDist cdf _ = GroundedAST.probabilisticFuncDef splitPF
    pfLabel           = GroundedAST.probabilisticFuncLabel splitPF
    addCond val conds = conds{Formula.realConds = Map.insert pfLabel val $ Formula.realConds conds}

splitFormulaCommon :: Formula.RefWithNode HPT.CachedSplitPoints
                   -> Maybe HPT.LazyNode
                   -> Probability
                   -> (cond -> Formula.Conditions -> Formula.Conditions)
                   -> cond
                   -> cond
                   -> FState (Formula.NodeRef, Maybe HPT.LazyNode, Formula.NodeRef, Maybe HPT.LazyNode, Probability)
splitFormulaCommon f lf pLeft addCond leftCond rightCond = do
    left  <- Formula.condition f $ addCond leftCond  Formula.noConditions
    right <- Formula.condition f $ addCond rightCond Formula.noConditions
    return ( Formula.entryRef left
           , second (addCond leftCond)  <$> lf
           , Formula.entryRef right
           , second (addCond rightCond) <$> lf
           , pLeft
           )

addCondObj :: GroundedAST.PFunc a -> Formula.ObjCondition -> Formula.Conditions -> Formula.Conditions
addCondObj pf val conds = conds{Formula.objConds = Map.insert pfLabel val $ Formula.objConds conds}
    where
    pfLabel = GroundedAST.probabilisticFuncLabel pf

heuristicsCacheComputations :: Formula.CacheComputations HPT.CachedSplitPoints
heuristicsCacheComputations = Formula.CacheComputations
    { Formula.cachedInfoComposed          = heuristicComposed
    , Formula.cachedInfoBuildInPredBool   = heuristicBuildInPredBool
    , Formula.cachedInfoBuildInPredString = heuristicBuildInPredString
    , Formula.cachedInfoBuildInPredReal   = heuristicBuildInPredReal
    , Formula.cachedInfoBuildInPredObject = heuristicBuildInPredObject
    , Formula.cachedInfoDeterministic     = heuristicDeterministic
    }

heuristicDeterministic :: Bool -> HPT.CachedSplitPoints
heuristicDeterministic = const $ HPT.CachedSplitPoints Set.empty Set.empty $ HPT.Primitive Set.empty

heuristicBuildInPredBool :: GroundedAST.TypedBuildInPred Bool -> HPT.CachedSplitPoints
heuristicBuildInPredBool prd = HPT.CachedSplitPoints
    proofsT
    proofsF
    (HPT.Primitive $ Set.map HPT.BoolSplit pFuncs)
    where
    (proofsT, proofsF) = case prd of
        GroundedAST.Equality eq (GroundedAST.ConstantExpr (GroundedAST.BoolConstant cnst)) (GroundedAST.PFuncExpr pf) ->
            proofsSinglePf eq cnst pf
        GroundedAST.Equality eq (GroundedAST.PFuncExpr pf) (GroundedAST.ConstantExpr (GroundedAST.BoolConstant cnst)) ->
            proofsSinglePf eq cnst pf
        GroundedAST.Equality eq (GroundedAST.PFuncExpr pfX) (GroundedAST.PFuncExpr pfY) ->
            ( Set.fromList
                [ HPT.Proof $ Map.fromList
                    [ (HPT.BoolSplit pfX, HPT.Left)
                    , (HPT.BoolSplit pfY, if eq then HPT.Left  else HPT.Right)
                    ]
                , HPT.Proof $ Map.fromList
                    [ (HPT.BoolSplit pfX, HPT.Right)
                    , (HPT.BoolSplit pfY, if eq then HPT.Right else HPT.Left)
                    ]
                ]
            , Set.fromList
                [ HPT.Proof $ Map.fromList
                    [ (HPT.BoolSplit pfX, HPT.Left)
                    , (HPT.BoolSplit pfY, if eq then HPT.Right else HPT.Left)
                    ]
                , HPT.Proof $ Map.fromList
                    [ (HPT.BoolSplit pfX, HPT.Right)
                    , (HPT.BoolSplit pfY, if eq then HPT.Left  else HPT.Right)
                    ]
                ]
            )
        _ -> undefined

    proofsSinglePf eq cnst pf =
        ( Set.singleton $ HPT.Proof $ Map.singleton (HPT.BoolSplit pf) $ if eq == cnst then HPT.Left  else HPT.Right
        , Set.singleton $ HPT.Proof $ Map.singleton (HPT.BoolSplit pf) $ if eq == cnst then HPT.Right else HPT.Left
        )

    pFuncs = GroundedAST.predProbabilisticFunctions prd

heuristicBuildInPredString :: Map GroundedAST.PFuncLabel (Set Text)
                           -> GroundedAST.TypedBuildInPred Text
                           -> HPT.CachedSplitPoints
heuristicBuildInPredString _ prd = case prd of
    GroundedAST.Equality eq (GroundedAST.PFuncExpr pf)      (GroundedAST.ConstantExpr cnst) -> splitPointsStringPfConst eq pf cnst
    GroundedAST.Equality eq (GroundedAST.ConstantExpr cnst) (GroundedAST.PFuncExpr pf)      -> splitPointsStringPfConst eq pf cnst
    GroundedAST.Equality _ (GroundedAST.PFuncExpr pfX)     (GroundedAST.PFuncExpr pfY)      -> splitPointsStringPfs pfX pfY
    _                                                                                       -> undefined
    where
    splitPointsStringPfConst :: Bool -> GroundedAST.PFunc Text -> GroundedAST.ConstantExpr Text -> HPT.CachedSplitPoints
    splitPointsStringPfConst eq pf (GroundedAST.StrConstant cnst) = HPT.CachedSplitPoints
        (Set.singleton $ HPT.Proof $ Map.singleton splitPt $ if eq then HPT.Left else HPT.Right)
        (Set.singleton $ HPT.Proof $ Map.singleton splitPt $ if eq then HPT.Right else HPT.Left)
        (HPT.Primitive $ Set.singleton splitPt)
        where
        splitPt = HPT.StringSplit pf $ Set.singleton cnst
    splitPointsStringPfs _ _ = error "equality between two string-valued PFs not implemented"

heuristicBuildInPredReal :: Map GroundedAST.PFuncLabel Interval
                         -> GroundedAST.TypedBuildInPred GroundedAST.RealN
                         -> HPT.CachedSplitPoints
heuristicBuildInPredReal prevChoicesReal prd = case prd of
    GroundedAST.Equality{}          -> error "IHPMC: real equality not implemented"
    GroundedAST.Constant _          -> undefined
    GroundedAST.Ineq op exprX exprY -> HPT.CachedSplitPoints
        proofsT
        proofsF
        ( HPT.Primitive $ Set.unions
            [Set.fromList [sp | (sp, _) <- Map.toList p] | HPT.Proof p <- Set.toList $ Set.union proofsT proofsF]
        )
        where
        proofsT = keepOnlyMinimal proofsT'
        proofsF = keepOnlyMinimal proofsF'

        -- per PF only keep solutions requiring the minimal number of splits
        keepOnlyMinimal :: [([GroundedAST.PFunc GroundedAST.RealN], [HPT.Proof])] -> Set HPT.Proof
        keepOnlyMinimal proofs = snd $ foldl'
            ( \(nSols, proofs') (pfs, proofs'') ->
                  let nPfs' = length pfs
                  in if   null proofs'' || any (\pf -> Map.findWithDefault nPfs pf nSols < nPfs') pfs
                     then (nSols,                                                       proofs')
                     else (foldl' (\nSols' pf -> Map.insert pf nPfs' nSols') nSols pfs, foldl' (flip Set.insert) proofs' proofs'')
            )
            (Map.empty, Set.empty)
            proofs

        (proofsT', proofsF') = foldl'
            (\(resT, resF) (pfSubset, (resT', resF')) -> ((pfSubset, resT') : resT, (pfSubset, resF') : resF))
            ([], [])
            [(pfSubset,) $ findProofs pfSubset | pfSubset <- List.subsequences $ Set.toList predPfs, not $ null pfSubset]

        findProofs :: [GroundedAST.PFunc GroundedAST.RealN] -> ([HPT.Proof], [HPT.Proof])
        findProofs pfs = (proofs True, proofs False)
            where
            -- TODO: does filter 'insideCurrentSpace' prevent wrong proofs here?
            proofs trueProofs =
                [ HPT.Proof $ Map.fromList $ List.filter insideCurrentSpace
                    [ let (sp, pfOnLeft) = spPoint pf corner
                      in  (HPT.ContinuousSplit pf sp, if (pfOnLeft == opIsLt) == trueProofs then HPT.Left else HPT.Right)
                    | pf <- pfs
                    ]
                | corner <- remRfsCorners
                ]

            spPoint :: GroundedAST.PFunc GroundedAST.RealN -> Map (GroundedAST.PFunc GroundedAST.RealN) Rational -> (Rational, Bool)
            spPoint pf remRfsCornerPts = ( ( (fromIntegral nPfs' - 1.0) * equalSplit pf +
                                             (if pfOnLeft then 1.0 else -1.0) * (sumExpr exprY evalVals - sumExpr exprX evalVals)
                                           )
                                           / fromIntegral nPfs'
                                         , pfOnLeft
                                         )
                where
                evalVals = Map.union remRfsCornerPts equalSplits
                pfOnLeft = Set.member pf $ GroundedAST.exprProbabilisticFunctions exprX
                equalSplit pf' = Map.findWithDefault (error "IHPMC.spPoint") pf' equalSplits

                sumExpr :: GroundedAST.Expr GroundedAST.RealN -> Map.Map (GroundedAST.PFunc GroundedAST.RealN) Rational-> Rational
                sumExpr (GroundedAST.ConstantExpr (GroundedAST.RealConstant c)) _ = c
                sumExpr (GroundedAST.PFuncExpr pf') vals
                    | pf' == pf = 0
                    | otherwise = fromMaybe (error "IHPMC.sumExpr: Just expected") $ Map.lookup pf' vals
                sumExpr (GroundedAST.Sum x y) vals = sumExpr x vals + sumExpr y vals

            -- coners of all PFs not in current subset
            remRfsCorners :: [Map (GroundedAST.PFunc GroundedAST.RealN) Rational]
            remRfsCorners = Set.fold
                (\pf corners -> let Interval.Interval l u = Map.findWithDefault (Interval.Interval Inf Inf) (GroundedAST.probabilisticFuncLabel pf) prevChoicesReal
                                    mbX                   = Interval.pointRational (Interval.toPoint Lower l)
                                    mbY                   = Interval.pointRational (Interval.toPoint Upper u)
                                    add mbC               = case mbC of Nothing -> []
                                                                        Just c  -> Map.insert pf c <$> corners
                                in  add mbX ++ add mbY
                )
                [Map.empty]
                remainingRfs

            remainingRfs = Set.difference predPfs $ Set.fromList pfs

            -- point is inside and not on the boundary of the current space, so it is a valid split point
            insideCurrentSpace :: (HPT.SplitPoint, a) -> Bool
            insideCurrentSpace (HPT.ContinuousSplit pf p, _) = (lp ~> Interval.toPoint Lower lower) == Just True &&
                                                           (lp ~< Interval.toPoint Upper upper) == Just True
                where
                lp = Interval.rat2IntervLimPoint p
                Interval.Interval lower upper = Map.findWithDefault (Interval.Interval Inf Inf) (GroundedAST.probabilisticFuncLabel pf) prevChoicesReal
            insideCurrentSpace _ = error "IHPMC.heuristicBuildInPred.insideCurrentSpace"

            nPfs' = length pfs

        predPfs = GroundedAST.predProbabilisticFunctions prd
        nPfs = Set.size predPfs
        opIsLt = case op of
            GroundedAST.Lt   -> True
            GroundedAST.LtEq -> True
            GroundedAST.Gt   -> False
            GroundedAST.GtEq -> False

        equalSplits :: Map (GroundedAST.PFunc GroundedAST.RealN) Rational
        equalSplits = Map.fromList [(pf,equalSplit pf) | pf <- Set.toList predPfs]
            where
            equalSplit pf = icdf ((pUntilLower + pUntilUpper) / 2.0)
                where
                pUntilLower   = cdf' cdf True  curLower
                pUntilUpper   = cdf' cdf False curUpper
                Interval.Interval curLower curUpper = Map.findWithDefault (Interval.Interval Inf Inf) (GroundedAST.probabilisticFuncLabel pf) prevChoicesReal
                GroundedAST.RealDist cdf icdf = GroundedAST.probabilisticFuncDef pf

            -- how much thoes this split reduce the error bound
--            reduction :: [GroundedAST.PFunc GroundedAST.RealN]
--                      -> Map (GroundedAST.PFunc GroundedAST.RealN) Rational
--                      -> Map GroundedAST.PFuncLabel Interval
--                      -> Probability
--            reduction [] _ choices
--                | all ((==) $ Just True) checkedCorners || all ((==) $ Just False) checkedCorners = product [pDiff pf choices | pf <- Set.toList remainingRfs]
--                | otherwise                                                                       = 0.0
--                    where
--                    extremePoints  = Set.map
--                        ( \pf' -> let pfLabel = GroundedAST.probabilisticFuncLabel pf'
--                                  in (pfLabel, Map.findWithDefault (Interval.Interval Inf Inf) pfLabel choices)
--                        )
--                        predRfs
--                    corners        = Interval.corners $ Set.toList extremePoints
--                    checkedCorners = GroundedAST.checkRealIneqPred op exprX exprY <$> corners
--            reduction (pf:pfs') corner choices = pDiff pf chLeft * reduction pfs' corner chLeft + pDiff pf chRight * reduction pfs' corner chRight
--                where
--                splitP  = spPoint pf corner
--                Interval.Interval curLower curUpper = Map.findWithDefault (Interval.Interval Inf Inf) pfLabel choices
--                chLeft  = Map.insert pfLabel (Interval.Interval curLower (Open splitP)) choices
--                chRight = Map.insert pfLabel (Interval.Interval (Open splitP) curUpper) choices
--                pfLabel = GroundedAST.probabilisticFuncLabel pf

--        pDiff :: GroundedAST.PFunc GroundedAST.RealN -> Map GroundedAST.PFuncLabel Interval -> Probability
--        pDiff pf choices = pUntilUpper - pUntilLower
--            where
--            pUntilLower = cdf' cdf True  curLower
--            pUntilUpper = cdf' cdf False curUpper
--            Interval.Interval curLower curUpper = Map.findWithDefault (Interval.Interval Inf Inf) (GroundedAST.probabilisticFuncLabel pf) choices
--            GroundedAST.RealDist cdf _  = GroundedAST.probabilisticFuncDef pf

heuristicBuildInPredObject :: Map GroundedAST.PFuncLabel Formula.ObjCondition
                           -> GroundedAST.TypedBuildInPred GroundedAST.Object
                           -> HPT.CachedSplitPoints
heuristicBuildInPredObject prevChoicesObjects prd = case prd of
    GroundedAST.Equality eq (GroundedAST.PFuncExpr pf)      (GroundedAST.ConstantExpr cnst) -> splitPointsObjPfConst eq pf cnst
    GroundedAST.Equality eq (GroundedAST.ConstantExpr cnst) (GroundedAST.PFuncExpr pf)      -> splitPointsObjPfConst eq pf cnst
    GroundedAST.Equality eq (GroundedAST.PFuncExpr pfX)     (GroundedAST.PFuncExpr pfY)     -> splitPointsObjPfs eq pfX pfY
    _                                                                                       -> undefined
    where
    splitPointsObjPfConst :: Bool
                          -> GroundedAST.PFunc GroundedAST.Object
                          -> GroundedAST.ConstantExpr GroundedAST.Object
                          -> HPT.CachedSplitPoints
    splitPointsObjPfConst eq pf (GroundedAST.ObjConstant cnst) = HPT.CachedSplitPoints
        (Set.singleton $ HPT.Proof $ Map.singleton splitPt $ if eq then HPT.Left else HPT.Right)
        (Set.singleton $ HPT.Proof $ Map.singleton splitPt $ if eq then HPT.Right else HPT.Left)
        (HPT.Primitive $ Set.singleton splitPt)
        where
        splitPt = HPT.ObjectSplit pf cnst

    splitPointsObjPfs :: Bool
                      -> GroundedAST.PFunc GroundedAST.Object
                      -> GroundedAST.PFunc GroundedAST.Object
                      -> HPT.CachedSplitPoints
    splitPointsObjPfs eq pfX pfY = HPT.CachedSplitPoints
        proofsT
        proofsF
        (HPT.Primitive $ Set.unions [Set.fromList [sp | (sp, _) <- Map.toList p] | HPT.Proof p <- Set.toList $ Set.union proofsT proofsF])
        where
        proofsT = keepOnlyMinimal (proofsOnlyT pfX pfY) (proofsOnlyT pfY pfX) proofsBothT proofsBothEqualSpT
        proofsF = keepOnlyMinimal (proofsOnlyF pfX pfY) (proofsOnlyF pfY pfX) proofsBothF proofsBothEqualSpF

        -- only keep solutions requiring the minimal number of splits
        keepOnlyMinimal :: [HPT.Proof] -> [HPT.Proof] -> [HPT.Proof] -> [HPT.Proof] -> Set HPT.Proof
        keepOnlyMinimal proofsOnlyX proofsOnlyY ~proofsBoth ~proofsBothEqualSp
            | Set.null proofsOnlyX' = if Set.null proofsOnlyY'
                                      then if Set.null proofsBoth'
                                           then proofsBothEqualSp'
                                           else proofsBoth'
                                      else proofsOnlyY'
            | otherwise             = if Set.null proofsOnlyY'
                                      then proofsOnlyX'
                                      else Set.union proofsOnlyY' proofsOnlyX'
            where
            proofsOnlyX'        = toProofSet proofsOnlyX
            proofsOnlyY'        = toProofSet proofsOnlyY
            ~proofsBoth'        = toProofSet proofsBoth
            ~proofsBothEqualSp' = toProofSet proofsBothEqualSp

            toProofSet = Set.fromList . List.filter validProof

        -- TODO: there are not only disproofs...
        proofsOnlyT pf otherPf | eq        = []
                               | otherwise = disproofsSingle pf otherPf
        proofsOnlyF pf otherPf | eq        = disproofsSingle pf otherPf
                               | otherwise = []

        disproofsSingle pf otherPf = [ HPT.Proof $ Map.singleton (HPT.ObjectIntervSplit pf $ lCornerOther - 1) HPT.Left
                                     , HPT.Proof $ Map.singleton (HPT.ObjectIntervSplit pf   uCornerOther)     HPT.Right
                                     ]
            where
            (lCornerOther, uCornerOther, _) = corners otherPf

        ~proofsBothT | eq        = []
                     | otherwise = disproofsBoth
        ~proofsBothF | eq        = disproofsBoth
                     | otherwise = []

        ~disproofsBoth =
            [ HPT.Proof $ Map.fromList [(spX, HPT.Left),  (spY, HPT.Right)]
            , HPT.Proof $ Map.fromList [(spX, HPT.Right), (spY, HPT.Left)]
            ]
            where
            spX = HPT.ObjectIntervSplit pfX splitBoth
            spY = HPT.ObjectIntervSplit pfY splitBoth

        -- last resort: for both propose to split into parts with equal probability
        ~proofsBothEqualSpT | eq        = []
                            | otherwise = disproofsproofsBothEqualSp
        ~proofsBothEqualSpF | eq        = disproofsproofsBothEqualSp
                            | otherwise = []

        ~disproofsproofsBothEqualSp =
            [ HPT.Proof $ Map.fromList [(spX, HPT.Left),  (spY, HPT.Right)]
            , HPT.Proof $ Map.fromList [(spX, HPT.Right), (spY, HPT.Left)]
            ]
            where
            spX = HPT.ObjectIntervSplit pfX $ equalSplit pfX
            spY = HPT.ObjectIntervSplit pfY $ equalSplit pfY

        ~splitBoth = (equalSplit pfX + equalSplit pfY) `div` 2

        -- all split points in proof are valid
        validProof :: HPT.Proof -> Bool
        validProof (HPT.Proof p) = all validSplitPoint $ Map.toList p

        -- split points is inside current space and does actually split into two non-empty parts
        validSplitPoint :: (HPT.SplitPoint, a) -> Bool
        validSplitPoint (HPT.ObjectIntervSplit pf splitPt, _) = splitPt >= from && splitPt < upto
            where
            (from, upto, _) = corners pf
        validSplitPoint _ = undefined

        corners :: GroundedAST.PFunc GroundedAST.Object -> (Integer, Integer, Set Integer)
        corners pf = case Map.lookup (GroundedAST.probabilisticFuncLabel pf) prevChoicesObjects of
            Nothing                             -> (0, lastObj, Set.empty)
            Just (Formula.Object obj)           -> (obj, obj, Set.empty)
            Just (Formula.AnyExcept excl)       -> ( head $ List.filter (\i -> not $ Set.member i excl) [0..lastObj]
                                                   , head $ List.filter (\i -> not $ Set.member i excl) $ reverse [0..lastObj]
                                                   , excl
                                                   )
            Just (Formula.InInterval from upto) -> (from, upto, Set.empty)
            Just (Formula.AnyExceptInInterval excl from upto) ->
                ( head $ List.filter (\i -> not $ Set.member i excl) [from..upto]
                , head $ List.filter (\i -> not $ Set.member i excl) $ reverse [from..upto]
                , excl
                )
            where
            lastObj = GroundedAST.objectPfNrObjects pf - 1

        equalSplit :: GroundedAST.PFunc GroundedAST.Object -> Integer
        equalSplit pf = appNTimes (nObjects `div` 2 - 1) increment lCorner
            where
            (lCorner, uCorner, excl) = corners pf
            nObjects = uCorner - lCorner + 1 - fromIntegral (Set.size excl)

            increment x
                | Set.member x excl = increment x'
                | otherwise         = x'
                where
                x' = succ x

            -- precondition: first paremeter should be >= 0
            appNTimes :: Integer -> (a -> a) -> a -> a
            appNTimes 0 _ x = x
            appNTimes n _ _ | n < 0 = error "precondition"
            appNTimes n f x = appNTimes (n - 1) f $ f x

heuristicComposed :: Formula.NodeType -> Int -> [HPT.CachedSplitPoints] -> HPT.CachedSplitPoints
heuristicComposed op nPfs points = HPT.CachedSplitPoints
    proofsT
    proofsF
    (HPT.Composed $ composition points)
    where
    proofsT
        | op == Formula.And = proofProduct allProofsT
        | otherwise         = proofSum     allProofsT
    proofsF
        | op == Formula.Or  = proofProduct allProofsF
        | otherwise         = proofSum     allProofsF
    allProofsT = (\(HPT.CachedSplitPoints psT _ _) -> psT) <$> points
    allProofsF = (\(HPT.CachedSplitPoints _ psF _) -> psF) <$> points

    onlyMinLengthProofs proofs | Set.null proofs = proofs
                               | otherwise = Set.filter (\(HPT.Proof p) -> Map.size p <= minLength) proofs
        where
        ~minLength = minimum [Map.size p | HPT.Proof p <- Set.toList proofs]

    proofSum :: [Set HPT.Proof] -> Set HPT.Proof
    proofSum = Set.unions

    proofProduct :: [Set HPT.Proof] -> Set HPT.Proof
    proofProduct [] = undefined
    proofProduct (fstP:restPs) = foldl' (\ps ps' ->
            onlyMinLengthProofs $ Set.unions [combineProofWithSet p ps | p <- Set.toList ps']
        ) fstP restPs
        where
        combineProofWithSet :: HPT.Proof -> Set HPT.Proof -> Set HPT.Proof
        combineProofWithSet p = Set.fold
            ( \p' ps' -> case combineProofs p p' of
                  Just p'' | Map.size p'' <= 7 -> Set.insert (HPT.Proof p'') ps'
                  _                            -> ps'
            )
            Set.empty

        combineProofs :: HPT.Proof -> HPT.Proof -> Maybe (Map HPT.SplitPoint HPT.Choice)
        combineProofs (HPT.Proof x) (HPT.Proof y) = Map.foldWithKey addProofElement (Just x) y

        addProofElement :: HPT.SplitPoint
                        -> HPT.Choice
                        -> Maybe (Map HPT.SplitPoint HPT.Choice)
                        -> Maybe (Map HPT.SplitPoint HPT.Choice)
        addProofElement pt choice mbP = do
            p <- mbP
            -- TODO: this check of proof consistency is only correct for bools
            case Map.lookup pt p of
                Nothing                          -> return $ Map.insert pt choice p
                Just choice' | choice == choice' -> return p
                _                                -> mzero
    composition :: [HPT.CachedSplitPoints] -> Map HPT.SplitPoint Int
    composition pts = foldl'
        (\pts' pt-> Set.fold (`Map.insert` nPfs) pts' $ primPts pt)
        ( foldl'
            (\splitPoints splitPoints' -> Map.unionWith (+) splitPoints $ ptsMap splitPoints')
            Map.empty
            pts
        )
        pts

    primPts :: HPT.CachedSplitPoints -> Set HPT.SplitPoint
    primPts (HPT.CachedSplitPoints _ _ (HPT.Primitive p)) = p
    primPts (HPT.CachedSplitPoints _ _( HPT.Composed _))  = Set.empty

    ptsMap :: HPT.CachedSplitPoints -> Map HPT.SplitPoint Int
    ptsMap (HPT.CachedSplitPoints _ _ (HPT.Primitive _)) = Map.empty
    ptsMap (HPT.CachedSplitPoints _ _( HPT.Composed m))  = m

cdf' :: (Rational -> Probability) -> Bool -> IntervalLimit -> Probability
cdf' _ lower Inf      = if lower then 0.0 else 1.0
cdf' cdf _ (Open x)   = cdf x
cdf' cdf _ (Closed x) = cdf x

getTime :: IO Int
getTime = (\x -> fromIntegral (round (x*1000)::Int)) <$> getPOSIXTime
