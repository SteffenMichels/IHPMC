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
    , untilFinished
    , heuristicsCacheComputations
    ) where
import Formula (Formula)
import qualified Formula
import HPT (HPT, HPTNode)
import qualified HPT
import BasicTypes
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import qualified Data.HashSet as Set
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import qualified GroundedAST
import Interval (Interval, IntervalLimit(..), LowerUpper(..), (~>), (~<))
import qualified Interval
import Data.Maybe (fromMaybe)
import Control.Monad.State.Strict
import Data.List (maximumBy, subsequences)
import Data.Time.Clock.POSIX (getPOSIXTime)
import Exception
import Data.Foldable (foldl')
--import System.IO.Unsafe (unsafePerformIO)
--import Debug.Trace (trace)

-- number of rfs in primitives, split points + scores
data CachedSplitPoints = CachedSplitPoints Int (HashMap (GroundedAST.RFunc, SplitPoint) Double)
type FState = Formula.FState CachedSplitPoints
data SplitPoint = DiscreteSplit | ContinuousSplit Rational deriving (Eq, Generic)
instance Hashable SplitPoint

untilFinished :: Int -> ProbabilityBounds -> Int -> Bool
untilFinished _ _ _ = False

ihpmc :: Formula.NodeRef
      -> [Formula.NodeRef]
      -> (Int -> ProbabilityBounds -> Int -> Bool)
      -> Maybe Int
      -> Formula CachedSplitPoints
      -> ExceptionalT IOException IO [(Int, Int, ProbabilityBounds)]
ihpmc query evidence finishPred mbRepInterval f = do
    t <- doIO getTime
    evalStateT (ihpmc' 1 t t $ HPT.initialNode query $ Formula.entryRef evidenceConj) f'
    where
    (evidenceConj, f') = runState (Formula.insert (Right (Formula.Conditions Map.empty Map.empty)) True Formula.And evidence) f
    ihpmc' :: Int -> Int -> Int -> HPTNode -> StateT (Formula CachedSplitPoints) (ExceptionalT IOException IO) [(Int, Int, ProbabilityBounds)]
    ihpmc' i startTime lastReportedTime hptNode = do
        hpt <- state $ runState $ ihpmcIterate hptNode 1.0
        curTime <- lift $ doIO getTime
        let runningTime = curTime - startTime
        case hpt of
            (HPT.Finished _ _)            -> return [(i, runningTime, HPT.bounds hpt)]
            (HPT.Unfinished hptNode' _ _) -> do
                let bounds = HPT.bounds hpt
                if finishPred i bounds runningTime
                    then return [(i, runningTime, bounds)]--return $ unsafePerformIO (runExceptionalT (HPT.exportAsDot "/tmp/hpt.dot" hpt >> Formula.exportAsDot "/tmp/f.dot" f) >> return [(i, runningTime, bounds)])
                    else if case mbRepInterval of Just repInterv -> curTime - lastReportedTime >= repInterv; _ -> False
                        then ihpmc' (succ i) startTime curTime hptNode' >>= \bs -> return ((i, runningTime, bounds) : bs)
                        else ihpmc' (succ i) startTime lastReportedTime hptNode'

ihpmcIterate :: HPTNode -> Double -> FState HPT
ihpmcIterate hptNode partChoiceProb = do
    (hptNode', triple@(HPT.ProbabilityTriple t f u), score) <- iterateNode hptNode partChoiceProb
    return $ if u == 0.0 then HPT.Finished t f
                         else HPT.Unfinished hptNode' triple score
    where
    iterateNode :: HPTNode -> Double -> FState (HPTNode, HPT.ProbabilityTriple, Double)
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
    iterateNode (HPT.Leaf qRef eRef) _ = case Formula.deterministicNodeRef eRef of
        Just True  -> iterateNode (HPT.WithinEvidence qRef) partChoiceProb
        Just False -> return (undefined, HPT.outsideEvidenceTriple, 0.0)
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
                            then HPT.Unfinished (HPT.WithinEvidence $ Formula.entryRef qEntry') HPT.unknownTriple (probToDouble p * partChoiceProb)
                            else HPT.outsideEvidence
                        _ -> HPT.Unfinished
                            (HPT.Leaf (Formula.entryRef qEntry') $ Formula.entryRef eEntry')
                            HPT.unknownTriple
                            (probToDouble p * partChoiceProb)
                )

    iterateNode (HPT.WithinEvidence qRef) _ = case Formula.deterministicNodeRef qRef of
        Just val -> return (undefined, if val then HPT.trueTriple else HPT.falseTriple, 0.0)
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
                            HPT.unknownTriple
                            (probToDouble p * partChoiceProb)
                )

iterationLeaf :: Formula.RefWithNode CachedSplitPoints
              -> (    Probability
                   -> (Formula.RefWithNode CachedSplitPoints -> Formula.FState CachedSplitPoints (Formula.RefWithNode CachedSplitPoints))
                   -> FState HPT
                 )
              -> FState (HPTNode, HPT.ProbabilityTriple, Double)
iterationLeaf splitRfEntry makeHPT = do
    let ((splitRF, splitPoint), _) = maximumBy (\(_,x) (_,y) -> compare x y) candidateSplitPoints--(trace (show candidateSplitPoints) candidateSplitPoints)
    let rfDef = GroundedAST.randomFuncDef splitRF
    case splitPoint of
        DiscreteSplit -> case rfDef of
            GroundedAST.Flip p -> do
                left  <- makeHPT p       (\fEntry -> Formula.conditionBool fEntry splitRF True)
                right <- makeHPT (1 - p) (\fEntry -> Formula.conditionBool fEntry splitRF False)
                return (HPT.ChoiceBool splitRF p left right, combineProbsChoice p left right, combineScoresChoice left right)
            _ -> error "IHPMC: wrong RF def"
        ContinuousSplit splitPoint' -> case rfDef of
            GroundedAST.RealDist cdf _ -> do
                left  <- makeHPT p         (\fEntry -> Formula.conditionReal fEntry splitRF $ Interval.Interval curLower (Open splitPoint'))
                right <- makeHPT (1.0 - p) (\fEntry -> Formula.conditionReal fEntry splitRF $ Interval.Interval (Open splitPoint') curUpper)
                return (HPT.ChoiceReal splitRF p splitPoint' left right, combineProbsChoice p left right, combineScoresChoice left right)
                    where
                    p = (pUntilSplit - pUntilLower) / (pUntilUpper - pUntilLower)
                    pUntilLower = cdf' cdf True curLower
                    pUntilUpper = cdf' cdf False curUpper
                    pUntilSplit = cdf splitPoint'
                    Interval.Interval curLower curUpper = Map.lookupDefault (Interval.Interval Inf Inf) splitRF rConds
                        where
                        Formula.Conditions _ rConds = Formula.entryChoices splitRfEntry
            _  -> error "IHPMC: wrong RF def"
    where
    candidateSplitPoints = Map.toList pts where CachedSplitPoints _ pts = Formula.entryCachedInfo splitRfEntry

combineProbsChoice :: Probability -> HPT -> HPT -> HPT.ProbabilityTriple
combineProbsChoice p left right = HPT.ProbabilityTriple
    ((leftTrue    - rightTrue)    * p + rightTrue)
    ((leftFalse   - rightFalse)   * p + rightFalse)
    ((leftUnknown - rightUnknown) * p + rightUnknown)
    where
    HPT.ProbabilityTriple leftTrue  leftFalse  leftUnknown  = HPT.triple left
    HPT.ProbabilityTriple rightTrue rightFalse rightUnknown = HPT.triple right

combineScoresChoice :: HPT -> HPT -> Double
combineScoresChoice left right = max (HPT.score left) (HPT.score right)

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
                            equalSplit rf = case  GroundedAST.randomFuncDef rf of
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

                    pDiff rf choices = pUntilUpper - pUntilLower
                        where
                        pUntilLower = cdf' cdf True  curLower
                        pUntilUpper = cdf' cdf False curUpper
                        Interval.Interval curLower curUpper = Map.lookupDefault (Interval.Interval Inf Inf) rf choices
                        cdf = case GroundedAST.randomFuncDef rf of
                            GroundedAST.RealDist cdf'' _ -> cdf''
                            _ -> error "IHPMC.heuristicBuildInPred.cdf"

heuristicComposed :: [CachedSplitPoints] -> CachedSplitPoints
heuristicComposed = foldl'
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
