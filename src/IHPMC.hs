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

{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE Strict #-}
#endif

module IHPMC
    ( ihpmc
    , heuristicsCacheComputations
    , CachedSplitPoints
    ) where
import Formula (Formula)
import qualified Formula
import HPT (HPT, SplitPoint(..), CachedSplitPoints(..))
import qualified HPT
import Data.HashSet (Set)
import qualified Data.HashSet as Set
import Data.HashMap (Map)
import qualified Data.HashMap as Map
import qualified GroundedAST
import Interval (Interval, IntervalLimit(..), LowerUpper(..), (~>), (~<))
import qualified Interval
import Data.Maybe (fromMaybe, catMaybes)
import Control.Monad.State.Strict
import qualified Data.List as List
import Data.Time.Clock.POSIX (getPOSIXTime)
import Exception
import Data.Foldable (foldl')
import Probability
import Data.Text (Text)
import Control.Arrow (second)
import Data.List (partition)
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
        Just (HPT.HPTLeaf fs p, hpt') -> case fs of
            HPT.WithinEv q _ -> do
                qEntry        <- Formula.augmentWithEntry q
                let mbSpPoint =  splitPoint qEntry
                case mbSpPoint of
                    Nothing -> return Nothing
                    Just spPoint -> do
                        (ql, _, qr, _, pl) <- splitFormula qEntry Nothing spPoint
                        Formula.dereference q
                        let pr =  1.0 - pl
                        hpt''  <- HPT.addLeafWithinEvidence ql (pl * p) hpt'
                        hpt''' <- HPT.addLeafWithinEvidence qr (pr * p) hpt''
                        return $ Just hpt'''
            HPT.MaybeWithinEv q e _ -> do
                eEntry      <- Formula.augmentWithEntry e
                let mbSpPoint =  splitPoint eEntry
                case mbSpPoint of
                    Nothing -> return Nothing
                    Just spPoint -> do
                        (el, Just ql, er, Just qr, pl) <- splitFormula eEntry (Just q) spPoint
                        Formula.dereference e
                        when (Formula.deterministicNodeRef el /= Just False && Formula.deterministicNodeRef er /= Just False)
                             (Formula.reference query) -- new lazy formula refers to initial query
                        let pr =  1.0 - pl
                        hpt'' <- HPT.addLeaf ql el (pl * p) hpt'
                        Just <$> HPT.addLeaf qr er (pr * p) hpt''

splitPoint :: Formula.RefWithNode HPT.CachedSplitPoints -> Maybe SplitPoint
splitPoint f | null candidateSplitPoints = Nothing
             | otherwise = let (spPoint, _) = List.maximumBy (\(_,x) (_,y) -> compare x y) candidateSplitPoints
                           in  Just spPoint
    where
    candidateSplitPoints = Map.toList pts
    HPT.CachedSplitPoints _ pts _ = Formula.entryCachedInfo f

splitFormula :: Formula.RefWithNode HPT.CachedSplitPoints
             -> Maybe HPT.LazyNode
             -> SplitPoint
             -> FState (Formula.NodeRef, Maybe HPT.LazyNode, Formula.NodeRef, Maybe HPT.LazyNode, Probability)
splitFormula f lf (BoolSplit splitPF) = splitFormulaCommon f lf pLeft addCond True False
    where
    GroundedAST.Flip pLeft = GroundedAST.probabilisticFuncDef splitPF
    pfLabel = GroundedAST.probabilisticFuncLabel splitPF
    addCond val conds = conds{Formula.boolConds = Map.insert pfLabel val $ Formula.boolConds conds}
splitFormula f lf (StringSplit splitPF splitSet) = splitFormulaCommon f lf pLeft addCond splitSet splitSetCompl
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
splitFormula f lf (ObjectIntervSplit splitPf splitObj) = case GroundedAST.probabilisticFuncDef splitPf of
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
splitFormula f lf (ObjectSplit splitPf splitObj) = case GroundedAST.probabilisticFuncDef splitPf of
    GroundedAST.UniformObjDist _ -> splitObjFormula $ 1 / nPossibilities
    GroundedAST.UniformOtherObjDist otherPf -> case possibleValues otherPf oConds of
        Formula.Object otherObj
            | otherObj == splitObj -> splitObjFormula 0.0
            | otherwise -> splitObjFormula $
                1 / if inCurPossibleValues otherObj then nPossibilities - 1
                                                    else nPossibilities
        _ | splitPfInPossibleValuesOf otherPf ->
            -- we cannot split current PF, split parent PF
            splitFormula f lf $ ObjectSplit otherPf splitObj
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

splitFormula f lf (ContinuousSplit splitPF spPoint) = splitFormulaCommon f lf pLeft addCond leftCond rightCond
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
heuristicDeterministic = const $ CachedSplitPoints HPT.Primitive Map.empty 1

heuristicBuildInPredBool :: GroundedAST.TypedBuildInPred Bool -> HPT.CachedSplitPoints
heuristicBuildInPredBool prd = CachedSplitPoints HPT.Primitive
    (Set.fold (\pf pts -> Map.insert (BoolSplit pf) 1.0 pts) Map.empty $ GroundedAST.predProbabilisticFunctions prd)
    1

heuristicBuildInPredString :: Map GroundedAST.PFuncLabel (Set Text)
                           -> GroundedAST.TypedBuildInPred Text
                           -> HPT.CachedSplitPoints
heuristicBuildInPredString _ prd = case prd of
    GroundedAST.Equality _ (GroundedAST.PFuncExpr pf)      (GroundedAST.ConstantExpr cnst) -> splitPointsStringPfConst pf cnst
    GroundedAST.Equality _ (GroundedAST.ConstantExpr cnst) (GroundedAST.PFuncExpr pf)      -> splitPointsStringPfConst pf cnst
    GroundedAST.Equality _ (GroundedAST.PFuncExpr pfX)     (GroundedAST.PFuncExpr pfY)     -> splitPointsStringPfs pfX pfY
    _                                                                                      -> undefined
    where
    splitPointsStringPfConst :: GroundedAST.PFunc Text -> GroundedAST.ConstantExpr Text -> HPT.CachedSplitPoints
    splitPointsStringPfConst pf (GroundedAST.StrConstant cnst) =
        CachedSplitPoints HPT.Primitive (Map.singleton (StringSplit pf $ Set.singleton cnst) 1.0) 1
    splitPointsStringPfs _ _ = error "equality between two string-valued PFs not implemented"

heuristicBuildInPredReal :: Map GroundedAST.PFuncLabel Interval
                         -> GroundedAST.TypedBuildInPred GroundedAST.RealN
                         -> HPT.CachedSplitPoints
heuristicBuildInPredReal prevChoicesReal prd = case prd of
    GroundedAST.Equality{}          -> error "IHPMC: real equality not implemented"
    GroundedAST.Constant _          -> CachedSplitPoints HPT.Primitive Map.empty 1
    GroundedAST.Ineq op exprX exprY -> CachedSplitPoints HPT.Primitive scores nPfs
        where
        predRfs = GroundedAST.predProbabilisticFunctions prd
        nPfs = Set.size predRfs

        -- only keep solutions requiring the minimal number of splits
        scores :: Map SplitPoint Double
        scores = snd $ foldl'
                (\(nSols, splitPs) (pfs, splitPs') ->
                    let nPfs' = length pfs
                    in if   any (\pf -> Map.findWithDefault nPfs pf nSols < nPfs') pfs
                       then (nSols,                                                       splitPs)
                       else (foldl' (\nSols' pf -> Map.insert pf nPfs' nSols') nSols pfs, Map.unionWith (+) splitPs splitPs')
                )
                (Map.empty, Map.empty)
                (catMaybes [(pfSubset,) <$> splitPoints pfSubset | pfSubset <- List.subsequences (Set.toList predRfs), not $ null pfSubset])

        -- try to find splitpoints solving predicate by splitting on the subset of PFs given
        splitPoints :: [GroundedAST.PFunc GroundedAST.RealN]
                    -> Maybe (Map SplitPoint Double)
        splitPoints pfs
            | null result = Nothing
            | otherwise   = Just result
            where
            result :: Map SplitPoint Double
            result = foldl'
                (Map.unionWith (+))
                Map.empty
                [ Map.fromList $ List.filter insideCurrentSpace
                    [ (ContinuousSplit pf $ spPoint pf corner, probToDouble $ reduction pfs corner prevChoicesReal)
                    | pf <- pfs
                    ]
                | corner <- remRfsCorners
                ]

            spPoint :: GroundedAST.PFunc GroundedAST.RealN -> Map (GroundedAST.PFunc GroundedAST.RealN) Rational -> Rational
            spPoint pf remRfsCornerPts = (   (fromIntegral nPfs' - 1.0) * equalSplit pf
                                             + (if pfOnLeft then 1.0 else -1.0) * (sumExpr exprY evalVals - sumExpr exprX evalVals)
                                         )
                                         / fromIntegral nPfs'
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

            remainingRfs = Set.difference predRfs $ Set.fromList pfs

            -- how much thoes this split reduce the error bound
            reduction :: [GroundedAST.PFunc GroundedAST.RealN]
                      -> Map (GroundedAST.PFunc GroundedAST.RealN) Rational
                      -> Map GroundedAST.PFuncLabel Interval
                      -> Probability
            reduction [] _ choices
                | all ((==) $ Just True) checkedCorners || all ((==) $ Just False) checkedCorners = product [pDiff pf choices | pf <- Set.toList remainingRfs]
                | otherwise                                                                       = 0.0
                    where
                    extremePoints  = Set.map
                        ( \pf' -> let pfLabel = GroundedAST.probabilisticFuncLabel pf'
                                  in (pfLabel, Map.findWithDefault (Interval.Interval Inf Inf) pfLabel choices)
                        )
                        predRfs
                    corners        = Interval.corners $ Set.toList extremePoints
                    checkedCorners = GroundedAST.checkRealIneqPred op exprX exprY <$> corners
            reduction (pf:pfs') corner choices = pDiff pf chLeft * reduction pfs' corner chLeft + pDiff pf chRight * reduction pfs' corner chRight
                where
                splitP  = spPoint pf corner
                Interval.Interval curLower curUpper = Map.findWithDefault (Interval.Interval Inf Inf) pfLabel choices
                chLeft  = Map.insert pfLabel (Interval.Interval curLower (Open splitP)) choices
                chRight = Map.insert pfLabel (Interval.Interval (Open splitP) curUpper) choices
                pfLabel = GroundedAST.probabilisticFuncLabel pf

            -- point is inside and not on the boundary of the current space, so it is a valid split point
            insideCurrentSpace :: (SplitPoint, Double) -> Bool
            insideCurrentSpace (ContinuousSplit pf p, _) = (lp ~> Interval.toPoint Lower lower) == Just True &&
                                                           (lp ~< Interval.toPoint Upper upper) == Just True
                where
                lp = Interval.rat2IntervLimPoint p
                Interval.Interval lower upper = Map.findWithDefault (Interval.Interval Inf Inf) (GroundedAST.probabilisticFuncLabel pf) prevChoicesReal
            insideCurrentSpace _ = error "IHPMC.heuristicBuildInPred.insideCurrentSpace"

            nPfs' = length pfs

        equalSplits :: Map (GroundedAST.PFunc GroundedAST.RealN) Rational
        equalSplits = Map.fromList [(pf,equalSplit pf) | pf <- Set.toList predRfs]
            where
                equalSplit pf = icdf ((pUntilLower + pUntilUpper) / 2.0)
                    where
                    pUntilLower   = cdf' cdf True  curLower
                    pUntilUpper   = cdf' cdf False curUpper
                    Interval.Interval curLower curUpper = Map.findWithDefault (Interval.Interval Inf Inf) (GroundedAST.probabilisticFuncLabel pf) prevChoicesReal
                    GroundedAST.RealDist cdf icdf = GroundedAST.probabilisticFuncDef pf

        pDiff :: GroundedAST.PFunc GroundedAST.RealN -> Map GroundedAST.PFuncLabel Interval -> Probability
        pDiff pf choices = pUntilUpper - pUntilLower
            where
            pUntilLower = cdf' cdf True  curLower
            pUntilUpper = cdf' cdf False curUpper
            Interval.Interval curLower curUpper = Map.findWithDefault (Interval.Interval Inf Inf) (GroundedAST.probabilisticFuncLabel pf) choices
            GroundedAST.RealDist cdf _  = GroundedAST.probabilisticFuncDef pf

heuristicBuildInPredObject :: Map GroundedAST.PFuncLabel Formula.ObjCondition
                           -> GroundedAST.TypedBuildInPred GroundedAST.Object
                           -> HPT.CachedSplitPoints
heuristicBuildInPredObject prevChoicesObjects prd = case prd of
    GroundedAST.Equality _ (GroundedAST.PFuncExpr pf)      (GroundedAST.ConstantExpr cnst) -> splitPointsObjPfConst pf cnst
    GroundedAST.Equality _ (GroundedAST.ConstantExpr cnst) (GroundedAST.PFuncExpr pf)      -> splitPointsObjPfConst pf cnst
    GroundedAST.Equality _ (GroundedAST.PFuncExpr pfX)     (GroundedAST.PFuncExpr pfY)     -> splitPointsObjPfs pfX pfY
    _                                                                                      -> undefined
    where
    splitPointsObjPfConst :: GroundedAST.PFunc GroundedAST.Object -> GroundedAST.ConstantExpr GroundedAST.Object -> HPT.CachedSplitPoints
    splitPointsObjPfConst pf (GroundedAST.ObjConstant cnst) = CachedSplitPoints HPT.Primitive (Map.singleton (ObjectSplit pf cnst) 1.0) 1

    splitPointsObjPfs :: GroundedAST.PFunc GroundedAST.Object
                      -> GroundedAST.PFunc GroundedAST.Object
                      -> CachedSplitPoints
    splitPointsObjPfs pfX pfY = CachedSplitPoints HPT.Primitive scores 2
        where
        -- only keep solutions requiring the minimal number of splits
        scores :: Map SplitPoint Double
        scores
            | null splitPointsOnlyX = if null splitPointsOnlyY
                                      then if null splitPointsBoth
                                           then splitPointsBothEqual
                                           else splitPointsBoth
                                      else splitPointsOnlyY
            | otherwise             = if null splitPointsOnlyY
                                      then splitPointsOnlyX
                                      else Map.union splitPointsOnlyY splitPointsOnlyX

        splitPointsOnlyX = Map.fromList $ List.filter validSplitPoint
            [(ObjectIntervSplit pfX $ lCornerY - 1, reduction),  (ObjectIntervSplit pfX uCornerY, reduction)]
        splitPointsOnlyY = Map.fromList $ List.filter validSplitPoint
            [(ObjectIntervSplit pfY $ lCornerX - 1, reduction),  (ObjectIntervSplit pfY uCornerX, reduction)]
        ~splitPointsBoth = Map.fromList $ List.filter validSplitPoint
            [(ObjectIntervSplit pfX splitBoth, reduction), (ObjectIntervSplit pfY splitBoth, reduction)]
        -- last resort: for both propose to split into parts with equal probability
        ~splitPointsBothEqual = Map.fromList
            [(ObjectIntervSplit pfX $ equalSplit pfX, reduction), (ObjectIntervSplit pfY $ equalSplit pfY, reduction)]

        (lCornerX, uCornerX, _) = corners pfX
        (lCornerY, uCornerY, _) = corners pfY
        ~splitBoth = (equalSplit pfX + equalSplit pfY) `div` 2

        reduction = 1.0

        -- split points is inside current space and does actually split into two non-empty parts
        validSplitPoint :: (SplitPoint, Double) -> Bool
        validSplitPoint (ObjectIntervSplit pf splitPt, _) = splitPt >= from && splitPt < upto
            where
            (from, upto, _) = corners pf
        validSplitPoint _ = error "should this happen?"

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

heuristicComposed :: Int -> [HPT.CachedSplitPoints] -> HPT.CachedSplitPoints
heuristicComposed nPFuncs points
    | null primPts = HPT.CachedSplitPoints HPT.Composed                            (composition compPts) nPFuncs
    | otherwise    = HPT.CachedSplitPoints HPT.Composed ((/ fromIntegral score) <$> composition primPts) nPFuncs
    where
    (primPts, compPts) = partition isPrimitive points
    score = product $ (\(HPT.CachedSplitPoints _ _ s) -> s) <$> points

    composition :: [HPT.CachedSplitPoints] -> Map SplitPoint Double
    composition = foldl'
        (\splitPoints splitPoints' -> Map.unionWith (+) splitPoints $ ptsMap splitPoints')
        Map.empty

    isPrimitive :: HPT.CachedSplitPoints -> Bool
    isPrimitive (HPT.CachedSplitPoints HPT.Primitive _ _) = True
    isPrimitive (HPT.CachedSplitPoints HPT.Composed _ _)  = False

    ptsMap :: HPT.CachedSplitPoints -> Map SplitPoint Double
    ptsMap (HPT.CachedSplitPoints HPT.Primitive m _) = m
    ptsMap (HPT.CachedSplitPoints HPT.Composed m _)  = m

cdf' :: (Rational -> Probability) -> Bool -> IntervalLimit -> Probability
cdf' _ lower Inf      = if lower then 0.0 else 1.0
cdf' cdf _ (Open x)   = cdf x
cdf' cdf _ (Closed x) = cdf x

getTime :: IO Int
getTime = (\x -> fromIntegral (round (x*1000)::Int)) <$> getPOSIXTime
