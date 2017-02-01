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
import Data.Maybe (fromMaybe)
import Control.Monad.State.Strict
import qualified Data.List as List
import Data.Time.Clock.POSIX (getPOSIXTime)
import Exception
import Data.Foldable (foldl')
import Probability
import Data.Text (Text)
import Control.Arrow (second)
import Data.List (partition)

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
                    (Formula.uncondComposedLabel $ GroundedAST.PredicateLabel (-1)) -- '-1 is unused predicate label, reserved for evidence
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
            HPT.WithinEv q -> do
                qEntry        <- Formula.augmentWithEntry q
                let mbSpPoint =  splitPoint qEntry
                case mbSpPoint of
                    Nothing -> return Nothing
                    Just spPoint -> do
                        (ql, _, qr, _, pl) <- splitFormula qEntry Nothing spPoint
                        Formula.dereference q
                        let pr             =  1.0 - pl
                        return $ Just
                               $ HPT.addLeafWithinEvidence ql (pl * p)
                               $ HPT.addLeafWithinEvidence qr (pr * p) hpt'
            HPT.MaybeWithinEv q e -> do
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
                        hpt''  <- HPT.addLeaf ql el (pl * p) hpt'
                        Just <$> HPT.addLeaf qr er (pr * p) hpt''

splitPoint :: Formula.RefWithNode HPT.CachedSplitPoints -> Maybe SplitPoint
splitPoint f | null candidateSplitPoints = Nothing
             | otherwise = let (spPoint, _) = List.maximumBy (\(_,x) (_,y) -> compare x y) candidateSplitPoints
                           in  Just spPoint
    where
    candidateSplitPoints = Map.toList pts
    pts = case Formula.entryCachedInfo f of
        HPT.CachedSplitPointsPrimitive pts' -> pts'
        HPT.CachedSplitPointsComposed  pts' -> pts'

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
splitFormula f lf (ObjectSplit splitPf splitObj) = case GroundedAST.probabilisticFuncDef splitPf of
    GroundedAST.UniformObjDist _
        | nPossibilities == 1 -> do -- right branch has probability 0
            left  <- Formula.condition f $ addCond leftCond  Formula.noConditions
            return ( Formula.entryRef left
                   , second (addCond leftCond)  <$> lf
                   , Formula.refDeterministic False
                   , const (Formula.refDeterministic False, Formula.noConditions) <$> lf
                   , 1.0
                   )
        | otherwise           -> splitObjFormula $ 1 / nPossibilities
    GroundedAST.UniformOtherObjDist otherPf -> case possibleValues otherPf oConds of
        Formula.Object otherObj
            | otherObj == splitObj -> do -- left branch is excluded
                right <- Formula.condition f $ addCond rightCond Formula.noConditions
                return ( Formula.refDeterministic False
                       , const (Formula.refDeterministic False, Formula.noConditions) <$> lf
                       , Formula.entryRef right
                       , second (addCond rightCond) <$> lf
                       , 0.0
                       )
            | otherwise -> splitObjFormula $
                1 / if Set.member otherObj curExclSet then nPossibilities
                                                      else nPossibilities - 1
        Formula.AnyExcept otherExcl
            | Set.member splitObj otherExcl -> splitObjFormula $ 1 / (nPossibilities - 1)
            | otherwise -> splitFormula f lf $ ObjectSplit otherPf splitObj
        where
        possibleValues :: GroundedAST.PFunc GroundedAST.Object
                       -> Map GroundedAST.PFuncLabel Formula.ObjCondition
                       -> Formula.ObjCondition
        possibleValues pf = Map.findWithDefault
            (Formula.AnyExcept Set.empty)
            (GroundedAST.probabilisticFuncLabel pf)
    where
    nr :: GroundedAST.PFunc GroundedAST.Object -> Integer
    nr pf = case GroundedAST.probabilisticFuncDef pf of
        GroundedAST.UniformObjDist nr'          -> nr'
        GroundedAST.UniformOtherObjDist otherPf -> nr otherPf
    nPossibilities = intToProb (nr splitPf - fromIntegral (Set.size curExclSet))
    Formula.Conditions _ _ _ oConds = Formula.entryChoices f
    curExclSet = case Map.lookup (GroundedAST.probabilisticFuncLabel splitPf) oConds of
            Just (Formula.AnyExcept s) -> s
            Just (Formula.Object _)    -> error "object PF restricted to single object should never be selected to split on"
            Nothing                    -> Set.empty
    leftCond  = Formula.Object splitObj
    rightCond = Formula.AnyExcept $ Set.insert splitObj curExclSet
    addCond val conds = conds{Formula.objConds = Map.insert pfLabel val $ Formula.objConds conds}
    pfLabel           = GroundedAST.probabilisticFuncLabel splitPf

    splitObjFormula pLeft = splitFormulaCommon f lf pLeft addCond leftCond rightCond
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
heuristicDeterministic = const $ CachedSplitPointsPrimitive Map.empty

heuristicBuildInPredBool :: GroundedAST.TypedBuildInPred Bool -> HPT.CachedSplitPoints
heuristicBuildInPredBool prd = CachedSplitPointsPrimitive $
    Set.fold (\pf pts -> Map.insert (BoolSplit pf) 1.0 pts) Map.empty $ GroundedAST.predProbabilisticFunctions prd

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
    splitPointsStringPfConst pf (GroundedAST.StrConstant cnst) = CachedSplitPointsPrimitive $ Map.singleton (StringSplit pf $ Set.singleton cnst) 1.0
    splitPointsStringPfs _ _ = error "equality between two string-valued PFs not implemented"

heuristicBuildInPredReal :: Map GroundedAST.PFuncLabel Interval
                         -> GroundedAST.TypedBuildInPred GroundedAST.RealN
                         -> HPT.CachedSplitPoints
heuristicBuildInPredReal prevChoicesReal prd = case prd of
    GroundedAST.Equality{}          -> error "IHPMC: real equality not implemented"
    GroundedAST.Constant _          -> CachedSplitPointsPrimitive Map.empty
    GroundedAST.Ineq op exprX exprY -> CachedSplitPointsPrimitive scores
        where
        predRfs = GroundedAST.predProbabilisticFunctions prd
        nPfs = Set.size predRfs

        scores :: Map SplitPoint Double
        scores = snd $ foldl'
                (\(nSols, splitPs) (pfs, nSols', splitPs') -> if   any (\pf -> Map.findWithDefault nPfs pf nSols < length pfs) pfs
                                                              then (nSols, splitPs)
                                                              else (Map.union nSols nSols', Map.unionWith (+) splitPs splitPs')
                )
                (Map.empty, Map.empty)
                (splitPoints <$> List.subsequences (Set.toList predRfs))

        splitPoints :: [GroundedAST.PFunc GroundedAST.RealN]
                    -> ([GroundedAST.PFunc GroundedAST.RealN], Map (GroundedAST.PFunc GroundedAST.RealN) Int, Map SplitPoint Double)
        splitPoints pfs
            | null pfs || null result = (pfs, Map.empty,                              result)
            | otherwise               = (pfs, Map.fromList [(pf, nPfs') | pf <- pfs], result)
            where
            result :: Map SplitPoint Double
            result = Map.filterWithKey notOnBoundary $ foldl'
                (Map.unionWith (+))
                Map.empty
                [ Map.fromList [ (ContinuousSplit pf $ spPoint pf corner, probToDouble $ reduction pfs corner prevChoicesReal)
                               | pf <- pfs
                               ]
                | corner <- remRfsCorners
                ]

            notOnBoundary :: SplitPoint -> Double -> Bool
            notOnBoundary (ContinuousSplit pf p) _ = (lp ~> Interval.toPoint Lower lower) == Just True &&
                                                     (lp ~< Interval.toPoint Upper upper) == Just True
                where
                lp = Interval.rat2IntervLimPoint p
                Interval.Interval lower upper = Map.findWithDefault (Interval.Interval Inf Inf) (GroundedAST.probabilisticFuncLabel pf) prevChoicesReal
            notOnBoundary _ _ = error "IHPMC.heuristicBuildInPred.notOnBoundary"

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

            spPoint pf remRfsCornerPts = (   (fromIntegral nPfs' - 1.0)*equalSplit pf
                                              + (if pfOnLeft then 1.0 else -1.0) * (sumExpr exprY evalVals - sumExpr exprX evalVals)
                                            ) / fromIntegral nPfs'
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

            nPfs' = length pfs

            remRfsCorners = Set.fold
                (\pf corners -> let Interval.Interval l u = Map.findWithDefault (Interval.Interval Inf Inf) (GroundedAST.probabilisticFuncLabel pf) prevChoicesReal
                                    mbX                   = Interval.pointRational (Interval.toPoint Lower l)
                                    mbY                   = Interval.pointRational (Interval.toPoint Upper u)
                                    add mbC               = case mbC of
                                                               Nothing -> []
                                                               Just c  -> Map.insert pf c <$> corners
                                in  add mbX ++ add mbY
                )
                [Map.empty]
                remainingRfs

            remainingRfs = Set.difference predRfs $ Set.fromList pfs

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
heuristicBuildInPredObject _ prd = case prd of
    GroundedAST.Equality _ (GroundedAST.PFuncExpr pf)      (GroundedAST.ConstantExpr cnst) -> splitPointsObjPfConst pf cnst
    GroundedAST.Equality _ (GroundedAST.ConstantExpr cnst) (GroundedAST.PFuncExpr pf)      -> splitPointsObjPfConst pf cnst
    GroundedAST.Equality _ (GroundedAST.PFuncExpr pfX)     (GroundedAST.PFuncExpr pfY)     -> splitPointsObjPfs pfX pfY
    _                                                                                      -> undefined
    where
    splitPointsObjPfConst :: GroundedAST.PFunc GroundedAST.Object -> GroundedAST.ConstantExpr GroundedAST.Object -> HPT.CachedSplitPoints
    splitPointsObjPfConst pf (GroundedAST.ObjConstant cnst) = CachedSplitPointsPrimitive $ Map.singleton (ObjectSplit pf cnst) 1.0
    splitPointsObjPfs _ _ = error "equality between two object-valued PFs not implemented"

heuristicComposed :: [HPT.CachedSplitPoints] -> HPT.CachedSplitPoints
heuristicComposed points
    | null primPts = HPT.CachedSplitPointsComposed ((/ pi) <$> composition compPts)
    | otherwise    = HPT.CachedSplitPointsComposed ((/ (fromIntegral $ Map.size $ composition compPts)) <$> composition primPts)
    where
    (primPts, compPts) = partition isPrimitive points

    composition :: [HPT.CachedSplitPoints] -> Map SplitPoint Double
    composition = foldl'
                        ( \splitPoints splitPoints' ->
                          combineSplitPoints splitPoints $ ptsMap splitPoints'
                        )
                        Map.empty

    combineSplitPoints :: Map SplitPoint Double
                       -> Map SplitPoint Double
                       -> Map SplitPoint Double
    combineSplitPoints = Map.unionWith (+)

    isPrimitive (HPT.CachedSplitPointsPrimitive _) = True
    isPrimitive (HPT.CachedSplitPointsComposed _)  = False

    ptsMap (HPT.CachedSplitPointsPrimitive m) = m
    ptsMap (HPT.CachedSplitPointsComposed m)  = m

cdf' :: (Rational -> Probability) -> Bool -> IntervalLimit -> Probability
cdf' _ lower Inf      = if lower then 0.0 else 1.0
cdf' cdf _ (Open x)   = cdf x
cdf' cdf _ (Closed x) = cdf x

getTime :: IO Int
getTime = (\x -> fromIntegral (round (x*1000)::Int)) <$> getPOSIXTime
