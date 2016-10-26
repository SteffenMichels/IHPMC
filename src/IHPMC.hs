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
    ) where
import Formula (Formula)
import qualified Formula
import HPT (HPT)
import qualified HPT
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
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

-- total score, split points + scores
data CachedSplitPoints = CachedSplitPoints Double (HashMap SplitPoint Double)
type FState = Formula.FState CachedSplitPoints
data SplitPoint = BoolSplit       (GroundedAST.PFunc Bool)
                | StringSplit     (GroundedAST.PFunc String)            (HashSet String) -- left branch: all string in this set, right branch: all remaining strings
                | ContinuousSplit (GroundedAST.PFunc GroundedAST.RealN) Rational
                deriving (Eq, Generic)
instance Hashable SplitPoint

ihpmc :: Formula.NodeRef
      -> [Formula.NodeRef]
      -> (Int -> ProbabilityBounds -> Int -> Bool)
      -> (Int -> ProbabilityBounds -> Int -> Int -> Maybe (ExceptionalT IOException IO ()))
      -> Formula CachedSplitPoints
      -> ExceptionalT IOException IO (Int, Int, Maybe ProbabilityBounds, Formula CachedSplitPoints)
ihpmc query evidence finishPred reportingIO f = do
    t <- doIO getTime
    ((n, et, mbBounds), f'') <- runStateT (ihpmc' 1 t t $ HPT.initialHPT query $ Formula.entryRef evidenceConj) f'
    return (n, et, mbBounds, f'')
    where
    (evidenceConj, f') = runState (Formula.insert
            (Formula.uncondComposedLabel $ GroundedAST.PredicateLabel (-1)) -- '-1 is unused predicate label, reserved for evidence
            True
            Formula.And
            evidence
        ) f
    ihpmc' :: Int
           -> Int
           -> Int
           -> HPT
           -> StateT (Formula CachedSplitPoints) (ExceptionalT IOException IO) (Int, Int, Maybe ProbabilityBounds)
    ihpmc' i startTime lastReportedTime hpt = do
        mbHpt <- state $ runState $ ihpmcIterate hpt
        curTime <- lift $ doIO getTime
        let runningTime = curTime - startTime
        case mbHpt of
            Nothing -> return (i, runningTime, HPT.bounds hpt)
            Just hpt' -> do
                let bounds = HPT.bounds hpt
                case bounds of
                    Just bs | not $ finishPred i bs runningTime -> case reportingIO i bs runningTime (lastReportedTime - startTime) of
                        Just repIO -> lift repIO >> ihpmc' (succ i) startTime curTime hpt'
                        Nothing    ->               ihpmc' (succ i) startTime lastReportedTime hpt'
                    _ -> return (i, runningTime, bounds)

ihpmcIterate :: HPT -> FState (Maybe HPT)
ihpmcIterate hpt = case HPT.nextLeaf hpt of
    Nothing -> return Nothing
    Just (HPT.HPTLeaf q mbE p, hpt') -> Just <$> case mbE of
        Nothing -> do
            qEntry       <- Formula.augmentWithEntry q
            let spPoint  =  splitPoint qEntry
            (ql, qr, pl) <- splitFormula qEntry spPoint
            let pr       =  1.0 - pl
            return $ HPT.addLeafWithinEvidence ql (pl * p)
                   $ HPT.addLeafWithinEvidence qr (pr * p) hpt'
        Just e -> do
            qEntry       <- Formula.augmentWithEntry q
            eEntry       <- Formula.augmentWithEntry e
            let spPoint  =  splitPoint eEntry
            (ql, qr, _)  <- splitFormula qEntry spPoint
            (el, er, pl) <- splitFormula eEntry spPoint
            let pr       =  1.0 - pl
            return $ HPT.addLeaf ql el (pl * p) $ HPT.addLeaf qr er (pr * p) hpt'

splitPoint :: Formula.RefWithNode CachedSplitPoints -> SplitPoint
splitPoint f = spPoint
    where
    (spPoint, _)         = List.maximumBy (\(_,x) (_,y) -> compare x y) candidateSplitPoints
    candidateSplitPoints = Map.toList pts where CachedSplitPoints _ pts = Formula.entryCachedInfo f

splitFormula :: Formula.RefWithNode CachedSplitPoints -> SplitPoint -> FState (Formula.NodeRef, Formula.NodeRef, Probability)
splitFormula f (BoolSplit splitPF) = do
    left  <- Formula.conditionBool f splitPF True
    right <- Formula.conditionBool f splitPF False
    let GroundedAST.Flip pLeft = GroundedAST.probabilisticFuncDef splitPF
    return (Formula.entryRef left, Formula.entryRef right, pLeft)
splitFormula f (StringSplit splitPF splitSet) = do
    left  <- Formula.conditionString f splitPF splitSet
    right <- Formula.conditionString f splitPF $ Set.difference curSet splitSet
    return (Formula.entryRef left, Formula.entryRef right, pLeft)
    where
    curSet                        = Map.lookupDefault (Set.fromList $ snd <$> elements) splitPF sConds
    Formula.Conditions _ sConds _ = Formula.entryChoices f
    GroundedAST.StrDist elements  = GroundedAST.probabilisticFuncDef splitPF
    pLeft                         = List.sum [p | (p, val) <- curElements, Set.member val splitSet] / z
    z                             = List.sum $ fst <$> curElements
    curElements                   = List.filter ((`Set.member` curSet) . snd) elements
splitFormula f (ContinuousSplit splitPF spPoint) = do
    left  <- Formula.conditionReal f splitPF $ Interval.Interval curLower (Open spPoint)
    right <- Formula.conditionReal f splitPF $ Interval.Interval (Open spPoint) curUpper
    return (Formula.entryRef left, Formula.entryRef right, pLeft)
    where
    pLeft = (pUntilSplit - pUntilLower) / (pUntilUpper - pUntilLower)
    pUntilLower = cdf' cdf True curLower
    pUntilUpper = cdf' cdf False curUpper
    pUntilSplit = cdf spPoint
    Interval.Interval curLower curUpper = Map.lookupDefault (Interval.Interval Inf Inf) splitPF rConds
    rConds = Formula.realConds $ Formula.entryChoices f
    GroundedAST.RealDist cdf _ = GroundedAST.probabilisticFuncDef splitPF

heuristicsCacheComputations :: Formula.CacheComputations CachedSplitPoints
heuristicsCacheComputations = Formula.CacheComputations
    { Formula.cachedInfoComposed          = heuristicComposed
    , Formula.cachedInfoBuildInPredBool   = heuristicBuildInPredBool
    , Formula.cachedInfoBuildInPredString = heuristicBuildInPredString
    , Formula.cachedInfoBuildInPredReal   = heuristicBuildInPredReal
    , Formula.cachedInfoDeterministic     = heuristicDeterministic
    }

heuristicDeterministic :: Bool -> CachedSplitPoints
heuristicDeterministic = const $ CachedSplitPoints 0 Map.empty

heuristicBuildInPredBool :: GroundedAST.TypedBuildInPred Bool -> CachedSplitPoints
heuristicBuildInPredBool prd = CachedSplitPoints (fromIntegral $ Set.size $ GroundedAST.predProbabilisticFunctions prd) $
    foldl' (\pts pf -> Map.insert (BoolSplit pf) 1.0 pts) Map.empty $ GroundedAST.predProbabilisticFunctions prd

heuristicBuildInPredString :: HashMap (GroundedAST.PFunc String) (HashSet String)
                           -> GroundedAST.TypedBuildInPred String
                           -> CachedSplitPoints
heuristicBuildInPredString _ prd = case prd of
    GroundedAST.Constant _ -> CachedSplitPoints 0.0 Map.empty
    GroundedAST.Equality _ (GroundedAST.PFuncExpr pf)      (GroundedAST.ConstantExpr cnst) -> splitPointsStringPfConst pf cnst
    GroundedAST.Equality _ (GroundedAST.ConstantExpr cnst) (GroundedAST.PFuncExpr pf)      -> splitPointsStringPfConst pf cnst
    GroundedAST.Equality _ (GroundedAST.PFuncExpr pfX)     (GroundedAST.PFuncExpr pfY)     -> splitPointsStringPfs pfX pfY
    _                                                                                      -> undefined
    where
    splitPointsStringPfConst :: GroundedAST.PFunc String -> GroundedAST.ConstantExpr String -> CachedSplitPoints
    splitPointsStringPfConst pf (GroundedAST.StrConstant cnst) = CachedSplitPoints 1 $ Map.singleton (StringSplit pf $ Set.singleton cnst) 1.0
    splitPointsStringPfs _ _ = error "equality between two string-value PFs not implemented"

heuristicBuildInPredReal :: HashMap (GroundedAST.PFunc GroundedAST.RealN) Interval
                         -> GroundedAST.TypedBuildInPred GroundedAST.RealN
                         -> CachedSplitPoints
heuristicBuildInPredReal prevChoicesReal prd = case prd of
    GroundedAST.Equality{} -> error "IHPMC: real equality not implemented"
    GroundedAST.Constant _ -> CachedSplitPoints 0.0 Map.empty
    GroundedAST.Ineq op exprX exprY -> CachedSplitPoints (foldl' (\tot s -> tot + (2 - s)) 0.0 scores) scores
        where
        predRfs = GroundedAST.predProbabilisticFunctions prd
        nPfs = Set.size predRfs
        scores = snd $ foldl'
                (\(nSols, splitPs) (pfs, nSols', splitPs') -> if   any (\pf -> Map.lookupDefault nPfs pf nSols < length pfs) pfs
                                                              then (nSols, splitPs)
                                                              else (Map.union nSols nSols', Map.unionWith (+) splitPs splitPs')
                )
                (Map.empty, Map.empty)
                (splitPoints <$> List.subsequences (Set.toList predRfs))
        equalSplits = Map.fromList [(pf,equalSplit pf) | pf <- Set.toList predRfs]
            where
                equalSplit pf = icdf ((pUntilLower + pUntilUpper) / 2.0)
                    where
                    pUntilLower   = cdf' cdf True  curLower
                    pUntilUpper   = cdf' cdf False curUpper
                    Interval.Interval curLower curUpper = Map.lookupDefault (Interval.Interval Inf Inf) pf prevChoicesReal
                    GroundedAST.RealDist cdf icdf = GroundedAST.probabilisticFuncDef pf
        splitPoints pfs
            | null pfs || null result = (pfs, Map.empty,                              result)
            | otherwise               = (pfs, Map.fromList [(pf, nPfs') | pf <- pfs], result)
            where
            result = Map.filterWithKey notOnBoundary $ foldl'
                (Map.unionWith (+))
                Map.empty
                [ Map.fromList [ (ContinuousSplit pf $ spPoint pf corner, probToDouble $ reduction pfs corner prevChoicesReal)
                               | pf <- pfs
                               ]
                | corner <- remRfsCorners
                ]

            notOnBoundary (ContinuousSplit pf p) _ = (lp ~> Interval.toPoint Lower lower) == Just True &&
                                                     (lp ~< Interval.toPoint Upper upper) == Just True
                where
                lp = Interval.rat2IntervLimPoint p
                Interval.Interval lower upper = Map.lookupDefault (Interval.Interval Inf Inf) pf prevChoicesReal
            notOnBoundary _ _ = error "IHPMC.heuristicBuildInPred.notOnBoundary"

            reduction [] _ choices
                | all ((==) $ Just True) checkedCorners || all ((==) $ Just False) checkedCorners = product [pDiff pf choices | pf <- Set.toList remainingRfs]
                | otherwise                                                                       = 0.0
                    where
                    extremePoints  = Set.map (\pf' -> (pf', Map.lookupDefault (Interval.Interval Inf Inf) pf' choices)) predRfs
                    corners        = Interval.corners $ Set.toList extremePoints
                    checkedCorners = map (GroundedAST.checkRealIneqPred op exprX exprY) corners
            reduction (pf:pfs') corner choices = pDiff pf chLeft * reduction pfs' corner chLeft + pDiff pf chRight * reduction pfs' corner chRight
                where
                splitP  = spPoint pf corner
                Interval.Interval curLower curUpper = Map.lookupDefault (Interval.Interval Inf Inf) pf choices
                chLeft  = Map.insert pf (Interval.Interval curLower (Open splitP)) choices
                chRight = Map.insert pf (Interval.Interval (Open splitP) curUpper) choices

            spPoint pf remRfsCornerPts = (   (fromIntegral nPfs' - 1.0)*equalSplit pf
                                              + (if pfOnLeft then 1.0 else -1.0) * (sumExpr exprY evalVals - sumExpr exprX evalVals)
                                            ) / fromIntegral nPfs'
                where
                evalVals = Map.union remRfsCornerPts equalSplits
                pfOnLeft = Set.member pf $ GroundedAST.exprProbabilisticFunctions exprX
                equalSplit pf' = Map.lookupDefault (error "IHPMC.spPoint") pf' equalSplits

                sumExpr :: GroundedAST.Expr GroundedAST.RealN -> Map.HashMap (GroundedAST.PFunc GroundedAST.RealN) Rational-> Rational
                sumExpr (GroundedAST.ConstantExpr (GroundedAST.RealConstant c)) _ = c
                sumExpr (GroundedAST.PFuncExpr pf') vals
                    | pf' == pf = 0
                    | otherwise = fromMaybe (error "IHPMC.sumExpr: Just expected") $ Map.lookup pf' vals
                sumExpr (GroundedAST.Sum x y) vals = sumExpr x vals + sumExpr y vals

            nPfs' = length pfs

            remRfsCorners = foldl'
                (\corners pf -> let Interval.Interval l u = Map.lookupDefault (Interval.Interval Inf Inf) pf prevChoicesReal
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

        pDiff pf choices = pUntilUpper - pUntilLower
            where
            pUntilLower = cdf' cdf True  curLower
            pUntilUpper = cdf' cdf False curUpper
            Interval.Interval curLower curUpper = Map.lookupDefault (Interval.Interval Inf Inf) pf choices
            cdf = case GroundedAST.probabilisticFuncDef pf of
                GroundedAST.RealDist cdf'' _ -> cdf''
                _ -> error "IHPMC.heuristicBuildInPred.cdf"

heuristicComposed :: [CachedSplitPoints] -> CachedSplitPoints
heuristicComposed points = CachedSplitPoints total ((/ total) <$> splitPts)
    where
    CachedSplitPoints total splitPts = foldl'
                        ( \(CachedSplitPoints total' splitPoints) (CachedSplitPoints total'' splitPoints') ->
                          CachedSplitPoints (total' + total'') $ combineSplitPoints splitPoints splitPoints'
                        )
                        (CachedSplitPoints 0.0 Map.empty)
                        points

    combineSplitPoints :: HashMap SplitPoint Double
                       -> HashMap SplitPoint Double
                       -> HashMap SplitPoint Double
    combineSplitPoints = Map.unionWith (+)

cdf' :: (Rational -> Probability) -> Bool -> IntervalLimit -> Probability
cdf' _ lower Inf      = if lower then 0.0 else 1.0
cdf' cdf _ (Open x)   = cdf x
cdf' cdf _ (Closed x) = cdf x

getTime :: IO Int
getTime = (\x -> fromIntegral (round (x*1000)::Int)) <$> getPOSIXTime
