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
    , untilFinished
    , heuristicsCacheComputations
    ) where
import Formula (Formula)
import qualified Formula
import HPT (HPT, HPTNode)
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

untilFinished :: Int -> ProbabilityBounds -> Int -> Bool
untilFinished _ _ _ = False

ihpmc :: Formula.NodeRef
      -> [Formula.NodeRef]
      -> (Int -> ProbabilityBounds -> Int -> Bool)
      -> (Int -> ProbabilityBounds -> Int -> Int -> Maybe (ExceptionalT IOException IO ()))
      -> Formula CachedSplitPoints
      -> ExceptionalT IOException IO (Int, Int, Maybe ProbabilityBounds, HPT)
ihpmc query evidence finishPred reportingIO f = do
    t <- doIO getTime
    evalStateT (ihpmc' 1 t t $ HPT.initialNode query $ Formula.entryRef evidenceConj) f'
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
           -> HPTNode
           -> StateT (Formula CachedSplitPoints) (ExceptionalT IOException IO) (Int, Int, Maybe ProbabilityBounds, HPT)
    ihpmc' i startTime lastReportedTime hptNode = do
        hpt <- state $ runState $ ihpmcIterate hptNode 1.0
        curTime <- lift $ doIO getTime
        let runningTime = curTime - startTime
        case hpt of
            (HPT.Finished _ _)            -> return (i, runningTime, HPT.bounds hpt, hpt)
            (HPT.Unfinished hptNode' _ _) -> do
                let bounds = HPT.bounds hpt
                case bounds of
                    Just bs | not $ finishPred i bs runningTime -> case reportingIO i bs runningTime (lastReportedTime - startTime) of
                        Just repIO -> lift repIO >> ihpmc' (succ i) startTime curTime hptNode'
                        Nothing    -> ihpmc' (succ i) startTime lastReportedTime hptNode'
                    _ -> return (i, runningTime, bounds, hpt)

ihpmcIterate :: HPTNode -> Double -> FState HPT
ihpmcIterate hptNode partChoiceProb = do
    (hptNode', triple@(HPT.ProbabilityQuadruple t f e u), score) <- iterateNode hptNode partChoiceProb
    return $ if u == 0.0 && e == 0.0 then HPT.Finished t f
                                     else HPT.Unfinished hptNode' triple score
    where
    iterateNode :: HPTNode -> Double -> FState (HPTNode, HPT.ProbabilityQuadruple, Double)
    iterateNode (HPT.Choice choice pFunc p left right) partChoiceProb' = do
        (left', right') <- case (left, right) of
            (HPT.Unfinished hptNode' _ _, _) | HPT.score left > HPT.score right ->
                (,right) <$> ihpmcIterate hptNode' (probToDouble p * partChoiceProb')
            (_, HPT.Unfinished hptNode' _ _) ->
                (left,)  <$> ihpmcIterate hptNode' (probToDouble (1.0 - p) * partChoiceProb')
            _ -> error "finished node should not be selected for iteration"
        return (HPT.Choice choice pFunc p left' right', combineProbsChoice p left' right', combineScoresChoice left' right')
    iterateNode (HPT.Leaf qRef eRef) _ = case Formula.deterministicNodeRef eRef of
        Just True  -> iterateNode (HPT.WithinEvidence qRef) partChoiceProb
        Just False -> return (undefined, HPT.outsideEvidenceQuadruple, 0.0)
        Nothing -> do
            qEntry <- Formula.augmentWithEntry qRef
            eEntry <- Formula.augmentWithEntry eRef
            iterationLeaf
                eEntry
                (\p condOp -> do
                    qEntry' <- condOp qEntry
                    eEntry' <- condOp eEntry
                    return $ case Formula.entryNode eEntry' of
                        Formula.Deterministic val ->
                            if val
                            then HPT.Unfinished (HPT.WithinEvidence $ Formula.entryRef qEntry') HPT.withinEvidenceQuadruple (probToDouble p * partChoiceProb)
                            else HPT.outsideEvidence
                        _ -> HPT.Unfinished
                            (HPT.Leaf (Formula.entryRef qEntry') $ Formula.entryRef eEntry')
                            HPT.unknownQuadruple
                            (probToDouble p * partChoiceProb)
                )

    iterateNode (HPT.WithinEvidence qRef) _ = case Formula.deterministicNodeRef qRef of
        Just val -> return (undefined, if val then HPT.trueQuadruple else HPT.falseQuadruple, 0.0)
        Nothing -> do
            qEntry <- Formula.augmentWithEntry qRef
            iterationLeaf
                qEntry
                (\p condOp -> do
                    qEntry' <- condOp qEntry
                    return $ case Formula.entryNode qEntry' of
                        Formula.Deterministic val ->
                            if val
                            then HPT.Finished 1.0 0.0
                            else HPT.Finished 0.0 1.0
                        _ -> HPT.Unfinished
                            (HPT.WithinEvidence $ Formula.entryRef qEntry')
                            HPT.withinEvidenceQuadruple
                            (probToDouble p * partChoiceProb)
                )

iterationLeaf :: Formula.RefWithNode CachedSplitPoints
              -> (    Probability
                   -> (Formula.RefWithNode CachedSplitPoints -> Formula.FState CachedSplitPoints (Formula.RefWithNode CachedSplitPoints))
                   -> FState HPT
                 )
              -> FState (HPTNode, HPT.ProbabilityQuadruple, Double)
iterationLeaf splitRfEntry makeHPT = do
    let (splitPoint, _) = List.maximumBy (\(_,x) (_,y) -> compare x y) candidateSplitPoints--(trace (show candidateSplitPoints) candidateSplitPoints)
    case splitPoint of
        BoolSplit splitPF -> do
            left  <- makeHPT p       (\fEntry -> Formula.conditionBool fEntry splitPF True)
            right <- makeHPT (1 - p) (\fEntry -> Formula.conditionBool fEntry splitPF False)
            return (HPT.Choice HPT.ChoiceBool (GroundedAST.probabilisticFuncLabel splitPF) p left right, combineProbsChoice p left right, combineScoresChoice left right)
            where
            GroundedAST.Flip p = GroundedAST.probabilisticFuncDef splitPF
        StringSplit splitPF splitSet -> do
            left  <- makeHPT pRight       (\fEntry -> Formula.conditionString fEntry splitPF splitSet)
            right <- makeHPT (1 - pRight) (\fEntry -> Formula.conditionString fEntry splitPF $ Set.difference curSet splitSet)
            return (HPT.Choice (HPT.ChoiceString splitSet) (GroundedAST.probabilisticFuncLabel splitPF) pRight left right, combineProbsChoice pRight left right, combineScoresChoice left right)
            where
            pRight                        = List.sum [p | (p, val) <- curElements, Set.member val splitSet] / z
            z                             = List.sum $ fst <$> curElements
            curElements                   = List.filter ((`Set.member` curSet) . snd) elements
            curSet                        = Map.lookupDefault (Set.fromList $ snd <$> elements) splitPF sConds
            Formula.Conditions _ sConds _ = Formula.entryChoices splitRfEntry
            GroundedAST.StrDist elements = GroundedAST.probabilisticFuncDef splitPF
        ContinuousSplit splitPF splitPoint' -> do
            left  <- makeHPT p         (\fEntry -> Formula.conditionReal fEntry splitPF $ Interval.Interval curLower (Open splitPoint'))
            right <- makeHPT (1.0 - p) (\fEntry -> Formula.conditionReal fEntry splitPF $ Interval.Interval (Open splitPoint') curUpper)
            return (HPT.Choice (HPT.ChoiceReal splitPoint') (GroundedAST.probabilisticFuncLabel splitPF) p left right, combineProbsChoice p left right, combineScoresChoice left right)
            where
            p = (pUntilSplit - pUntilLower) / (pUntilUpper - pUntilLower)
            pUntilLower = cdf' cdf True curLower
            pUntilUpper = cdf' cdf False curUpper
            pUntilSplit = cdf splitPoint'
            Interval.Interval curLower curUpper = Map.lookupDefault (Interval.Interval Inf Inf) splitPF rConds
            rConds = Formula.realConds $ Formula.entryChoices splitRfEntry
            GroundedAST.RealDist cdf _ = GroundedAST.probabilisticFuncDef splitPF
    where
    candidateSplitPoints = Map.toList pts where CachedSplitPoints _ pts = Formula.entryCachedInfo splitRfEntry

combineProbsChoice :: Probability -> HPT -> HPT -> HPT.ProbabilityQuadruple
combineProbsChoice p left right = HPT.ProbabilityQuadruple
    ((leftTrue    - rightTrue)    * p + rightTrue)
    ((leftFalse   - rightFalse)   * p + rightFalse)
    ((leftWithinE - rightWithinE) * p + rightWithinE)
    ((leftUnknown - rightUnknown) * p + rightUnknown)
    where
    HPT.ProbabilityQuadruple leftTrue  leftFalse  leftWithinE  leftUnknown  = HPT.quadruple left
    HPT.ProbabilityQuadruple rightTrue rightFalse rightWithinE rightUnknown = HPT.quadruple right

combineScoresChoice :: HPT -> HPT -> Double
combineScoresChoice left right = max (HPT.score left) (HPT.score right)

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
                (\(nSols, splitPs) (pfs, nSols', splitPs') -> if any (\pf -> Map.lookupDefault nPfs pf nSols < length pfs) pfs
                                                              then (nSols, splitPs)
                                                              else (Map.union nSols nSols', Map.unionWith (+) splitPs splitPs')
                )
                (Map.empty, Map.empty)
                (splitPoints <$> List.subsequences (Set.toList predRfs))
        equalSplits = Map.fromList [(pf,equalSplit pf) | pf <- Set.toList predRfs]
            where
                equalSplit pf = icdf ((pUntilLower + pUntilUpper) / 2.0)
                    where
                    pUntilLower = cdf' cdf True  curLower
                    pUntilUpper = cdf' cdf False curUpper
                    Interval.Interval curLower curUpper = Map.lookupDefault (Interval.Interval Inf Inf) pf prevChoicesReal
                    GroundedAST.RealDist cdf icdf = GroundedAST.probabilisticFuncDef pf
        splitPoints pfs
            | null pfs || null result = (pfs, Map.empty,                             result)
            | otherwise               = (pfs, Map.fromList [(pf, nPfs') | pf <- pfs], result)
            where
            result = Map.filterWithKey notOnBoundary $ foldl'
                (Map.unionWith (+))
                Map.empty
                [ Map.fromList [ (ContinuousSplit pf $ splitPoint pf corner, probToDouble $ reduction pfs corner prevChoicesReal)
                               | pf <- pfs
                               ]
                | corner <- remRfsCorners
                ]

            notOnBoundary (ContinuousSplit pf p) _ =    (Interval.rat2IntervLimPoint p ~> Interval.toPoint Lower lower) == Just True
                                                     && (Interval.rat2IntervLimPoint p ~< Interval.toPoint Upper upper) == Just True
                where
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
                splitP  = splitPoint pf corner
                Interval.Interval curLower curUpper = Map.lookupDefault (Interval.Interval Inf Inf) pf choices
                chLeft  = Map.insert pf (Interval.Interval curLower (Open splitP)) choices
                chRight = Map.insert pf (Interval.Interval (Open splitP) curUpper) choices

            splitPoint pf remRfsCornerPts = (   (fromIntegral nPfs' - 1.0)*equalSplit pf
                                              + (if pfOnLeft then 1.0 else -1.0) * (sumExpr exprY evalVals - sumExpr exprX evalVals)
                                            ) / fromIntegral nPfs'
                where
                evalVals = Map.union remRfsCornerPts equalSplits
                pfOnLeft = Set.member pf $ GroundedAST.exprProbabilisticFunctions exprX
                equalSplit pf' = Map.lookupDefault (error "IHPMC.splitPoint") pf' equalSplits

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
