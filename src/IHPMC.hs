--The MIT License (MIT)
--
--Copyright (c) 2016-2017 Steffen Michels (mail@steffen-michels.de)
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
    , HPT.CachedSplitPoints
    ) where
import qualified KnowledgeBase as KB
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
import Data.List (foldl1')

type KBState = KB.KBState HPT.CachedSplitPoints

-- | The actual IHPMC inference algorithm.
-- Computes bounds on the probability of a query given evidence.
-- A predicate determines when this anytime algorithm is stopped.
-- Also intermediate results can be reported.
ihpmc :: KB.NodeRef HPT.CachedSplitPoints            -- ^ The query KB node.
      -> [KB.NodeRef HPT.CachedSplitPoints]          -- ^ The evidence KB nodes.
      -> (Int -> ProbabilityBounds -> Int -> Bool)   -- ^ A predicate determining when to stop the algorithm.
                                                     -- The arguments are:
                                                     --
                                                     -- (1) the number of iterations.
                                                     -- (2) the current probability bounds.
                                                     -- (3) the total runtime.
      -> ( Int -> ProbabilityBounds -> Int -> Int
           -> Maybe (ExceptionalT IOException IO ())
         )                                           -- ^ A reporting function that optionally
                                                     -- gives an arbitrary IO action. The arguments are:
                                                     --
                                                     -- (1) the number of iterations.
                                                     -- (2) the current probability bounds.
                                                     -- (3) the total runtime.
                                                     -- (4) the runtime at which a report was generated last time.
      -> KBState (Int, Int, Maybe ProbabilityBounds) -- ^ Performs IO for measuring runtime and reporting. Return values:
                                                     --
                                                     -- (1) The number of iterations.
                                                     -- (2) The total runtime.
                                                     -- (3) The actual probability bound result
                                                     --     ('Nothing' if evidence is found to be inconsistent.)
ihpmc query evidence finishPred reportingIO = do
    t <- KB.kbStateDoIO getTime
    evidence' <- forM evidence KB.augmentWithEntry
    -- put together all evidence elements in single conjunction
    evidenceConj <- KB.insert
            KB.evidenceComposedLabel
            True
            KB.And
            evidence'
    -- initialise HPT
    initHpt <- HPT.initialHPT query $ KB.entryRef evidenceConj
    -- run inference
    ihpmc' 1 t t initHpt
    where
    ihpmc' :: Int -- iteration number
           -> Int
           -> Int
           -> HPT
           -> KBState (Int, Int, Maybe ProbabilityBounds)
    ihpmc' i startTime lastReportedTime hpt = do
        mbHpt   <- ihpmcIterate hpt
        curTime <- KB.kbStateDoIO getTime
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

    ihpmcIterate :: HPT -> KBState (Maybe HPT)
    ihpmcIterate hpt = case HPT.nextLeaf hpt of
        Nothing -> return Nothing
        Just (HPT.HPTLeaf fs p, hpt') -> case fs of
            HPT.WithinEv q _ -> do
                qEntry <- KB.augmentWithEntry q
                case splitPoint qEntry of
                    Nothing -> return Nothing
                    Just spPoint -> do
                        (ql, _, qr, _, pl) <- splitNode qEntry Nothing spPoint
                        KB.dereference q
                        let pr =  1.0 - pl
                        hpt''  <- HPT.addLeafWithinEvidence ql (pl * p) hpt'
                        hpt''' <- HPT.addLeafWithinEvidence qr (pr * p) hpt''
                        return $ Just hpt'''
            HPT.MaybeWithinEv q e _ -> do
                eEntry <- KB.augmentWithEntry e
                case splitPoint eEntry of
                    Nothing -> return Nothing
                    Just spPoint -> do
                        (el, Just ql, er, Just qr, pl) <- splitNode eEntry (Just q) spPoint
                        KB.dereference e
                        when (KB.deterministicNodeRef el /= Just False && KB.deterministicNodeRef er /= Just False)
                             (KB.reference query) -- new lazy KB node refers to initial query
                        let pr =  1.0 - pl
                        hpt'' <- HPT.addLeaf ql el (pl * p) hpt'
                        Just <$> HPT.addLeaf qr er (pr * p) hpt''

data ProofCounters = ProofCounters
                         (Map Int Int) -- length of proof -> nr of proofs with that length
                         Int           -- max length of proof
                         deriving (Eq, Show)

instance Ord ProofCounters where
    compare (ProofCounters countsX maxLengthX) (ProofCounters countsY maxLengthY) = compare' 1
        where
        compare' i
            | i > maxLengthX || i > maxLengthY = compare maxLengthX maxLengthY
            | otherwise = case compare (Map.findWithDefault 0 i countsX) (Map.findWithDefault 0 i countsY) of
                EQ  -> compare' $ succ i
                res -> res

type RefWithNode = KB.RefWithNode HPT.CachedSplitPoints

-- | Find the next point to split the KB node on.
splitPoint :: RefWithNode          -- ^ The KB node to split on.
           -> Maybe HPT.SplitPoint -- ^ Nothing if the node is true/false (cannot be split further).
                                   --   Otherwise, the best split point found.
splitPoint f
    | null candidateSplitPoints = Nothing
    -- no "short" proofs are found, so we have to resort to use split point of evidence with highest score
    | Set.null proofs           = Just $ fst $ List.maximumBy (\(_,x) (_,y) -> compare x y) candidateSplitPoints
    | otherwise                 = Just $ splitWithProofs proofs
    where
    proofs = Set.union proofsT proofsF
    HPT.CachedSplitPoints proofsT proofsF spType = KB.entryCachedInfo f
    candidateSplitPoints = case spType of
        HPT.Composed pts  -> Map.toList pts
        HPT.Primitive pts -> (, 0) <$> Set.toList pts

    splitWithProofs :: Set HPT.Proof -> HPT.SplitPoint
    splitWithProofs proofs' = fst $ List.maximumBy (\(_,x) (_,y) -> compare x y) (attachScores <$> candidateSplitPoints)
        where
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
            ( \(HPT.Proof p) counts-> let lengthProof = Map.size p in foldl'
                ( \counts' pt -> Map.insert
                    pt
                    ( case Map.lookup pt counts' of
                        Nothing -> ProofCounters (Map.singleton lengthProof 1) lengthProof
                        Just (ProofCounters cs maxLenProofs) ->
                            ProofCounters (Map.alter (Just . maybe 1 succ) lengthProof cs) $ max lengthProof maxLenProofs
                    )
                    counts'
                )
                counts
                (Map.keys p)
            )
            Map.empty
            proofs'

-- | Splits the KB node according to splitpoint given.
-- This results in 2 (or 4 if evidence is included) new KB nodes.
splitNode :: RefWithNode
          -> Maybe HPT.LazyNode
          -> HPT.SplitPoint
          -> KBState (KB.NodeRef HPT.CachedSplitPoints, Maybe HPT.LazyNode, KB.NodeRef HPT.CachedSplitPoints, Maybe HPT.LazyNode, Probability)
splitNode f lf (HPT.BoolSplit splitPF) = splitNodeCommon f lf pLeft addCond True False
    where
    GroundedAST.Flip pLeft = GroundedAST.probabilisticFuncDef splitPF
    pfLabel = GroundedAST.probabilisticFuncLabel splitPF
    addCond val conds = conds{KB.boolConds = Map.insert pfLabel val $ KB.boolConds conds}
splitNode f lf (HPT.StringSplit splitPF splitSet) = splitNodeCommon f lf pLeft addCond splitSet splitSetCompl
    where
    splitSetCompl                   = Set.difference curSet splitSet
    curSet                          = Map.findWithDefault
                                          (Set.fromList $ snd <$> elements)
                                          (GroundedAST.probabilisticFuncLabel splitPF)
                                          sConds
    KB.Conditions _ sConds _ _ = KB.entryChoices f
    GroundedAST.StrDist elements    = GroundedAST.probabilisticFuncDef splitPF
    pLeft                           = List.sum [p | (p, val) <- curElements, Set.member val splitSet] / z
    z                               = List.sum $ fst <$> curElements
    curElements                     = List.filter ((`Set.member` curSet) . snd) elements
    pfLabel                         = GroundedAST.probabilisticFuncLabel splitPF
    addCond val conds               = conds{KB.stringConds = Map.insert pfLabel val $ KB.stringConds conds}
-- we assume here that the splitObj is within the set given by the current conditions,
-- otherwise the KB node would have already been simplified
splitNode f lf (HPT.ObjectIntervSplit splitPf splitObj) = case GroundedAST.probabilisticFuncDef splitPf of
    GroundedAST.UniformObjDist _ -> splitNodeCommon f lf pLeft (addCondObj splitPf) leftCond rightCond -- TODO: can probabilties become 1.0/0.0?
    GroundedAST.UniformOtherObjDist _ -> error "not implemented"
    where
    pLeft = case possibleValues of
        KB.Object _                           -> error "object PF restricted to single object should never be selected to split on"
        KB.AnyExcept excl                     -> p 0 upto' (nrObjects - 1) excl
        KB.InInterval from upto               -> p from upto' upto Set.empty
        KB.AnyExceptInInterval excl from upto -> p from upto' upto excl
        where
        upto' = splitObj
        p :: Integer -> Integer -> Integer -> Set Integer -> Probability
        p from uptoSplit  upto excl = ratToProb $
            (uptoSplit - from + 1 - fromIntegral (Set.size $ filterExcl from uptoSplit excl)) %
            (upto      - from + 1 - fromIntegral (Set.size excl))

    -- TODO: corner cases: interval collapses to single point
    leftCond  = case possibleValues of
        KB.Object _                        -> error "object PF restricted to single object should never be selected to split on"
        KB.AnyExcept excl                  -> anyExceptInInterval 0    upto' excl
        KB.InInterval from _               -> inInterval          from upto'
        KB.AnyExceptInInterval excl from _ -> anyExceptInInterval from upto' excl
        where
        upto' = splitObj
    rightCond = case possibleValues of
        KB.Object _                        -> error "object PF restricted to single object should never be selected to split on"
        KB.AnyExcept excl                  -> anyExceptInInterval from' (nrObjects - 1) excl
        KB.InInterval _ upto               -> inInterval          from' upto
        KB.AnyExceptInInterval excl _ upto -> anyExceptInInterval from' upto excl
        where
        from' = splitObj + 1

    possibleValues = Map.findWithDefault
        (KB.InInterval 0 $ nrObjects - 1)
        (GroundedAST.probabilisticFuncLabel splitPf)
        oConds

    nrObjects = GroundedAST.objectPfNrObjects splitPf
    anyExceptInInterval from upto excl | from == upto = if Set.member from excl then error "TODO: deal with inconsistency"
                                                                                else KB.Object from
                                       | otherwise = KB.AnyExceptInInterval (filterExcl from upto excl) from upto

    inInterval from upto | from == upto = KB.Object from
                         | otherwise    = KB.InInterval from upto
    filterExcl from upto = Set.filter (\e -> e >= from && e <= upto)
    KB.Conditions _ _ _ oConds = KB.entryChoices f
splitNode f lf (HPT.ObjectSplit splitPf splitObj) = case GroundedAST.probabilisticFuncDef splitPf of
    GroundedAST.UniformObjDist _ -> splitObjNode $ 1 / nPossibilities
    GroundedAST.UniformOtherObjDist otherPf -> case possibleValues otherPf oConds of
        KB.Object otherObj
            | otherObj == splitObj -> splitObjNode 0.0
            | otherwise -> splitObjNode $
                1 / if inCurPossibleValues otherObj then nPossibilities - 1
                                                    else nPossibilities
        _ | splitPfInPossibleValuesOf otherPf ->
            -- we cannot split current PF, split parent PF
            splitNode f lf $ HPT.ObjectSplit otherPf splitObj
        _ -> splitObjNode $ 1 / (nPossibilities - 1)
    where
    splitObjNode :: Probability -> KBState (KB.NodeRef HPT.CachedSplitPoints, Maybe HPT.LazyNode, KB.NodeRef HPT.CachedSplitPoints, Maybe HPT.LazyNode, Probability)
    splitObjNode pLeft
        | pLeft == 1.0 = do -- right branch has probability 0
            left  <- KB.condition f $ addCondObj splitPf leftCond KB.noConditions
            return ( KB.entryRef left
                   , second (addCondObj splitPf leftCond) <$> lf
                   , KB.refDeterministic False
                   , const (KB.refDeterministic False, KB.noConditions) <$> lf
                   , 1.0
                   )
        | pLeft == 0.0 = do
            right <- KB.condition f $ addCondObj splitPf rightCond KB.noConditions
            return ( KB.refDeterministic False
                   , const (KB.refDeterministic False, KB.noConditions) <$> lf
                   , KB.entryRef right
                   , second (addCondObj splitPf rightCond) <$> lf
                   , 0.0
                   )
        | otherwise = splitNodeCommon f lf pLeft (addCondObj splitPf) leftCond rightCond

    nPossibilities :: Probability
    nPossibilities = case possibleValues splitPf oConds of
        KB.Object _                           -> error "object PF restricted to single object should never be selected to split on"
        KB.AnyExcept excl                     -> intToProb $ nr splitPf - fromIntegral (Set.size excl)
        KB.InInterval from upto               -> intToProb $ upto - from + 1
        KB.AnyExceptInInterval excl from upto -> intToProb $ upto - from + 1 - fromIntegral (Set.size excl)

    nr :: GroundedAST.PFunc GroundedAST.Object -> Integer
    nr pf = case GroundedAST.probabilisticFuncDef pf of
        GroundedAST.UniformObjDist nr'          -> nr'
        GroundedAST.UniformOtherObjDist otherPf -> nr otherPf

    KB.Conditions _ _ _ oConds = KB.entryChoices f

    possibleValues :: GroundedAST.PFunc GroundedAST.Object
                   -> Map GroundedAST.PFuncLabel KB.ObjCondition
                   -> KB.ObjCondition
    possibleValues pf = Map.findWithDefault
        (KB.AnyExcept Set.empty)
        (GroundedAST.probabilisticFuncLabel pf)

    inCurPossibleValues :: Integer -> Bool
    inCurPossibleValues obj = case possibleValues splitPf oConds of
        KB.Object _                           -> error "object PF restricted to single object should never be selected to split on"
        KB.AnyExcept excl                     -> not $ Set.member obj excl
        KB.InInterval from upto               -> from <= obj && obj <= upto
        KB.AnyExceptInInterval excl from upto -> from <= obj && obj <= upto && not (Set.member obj excl)

    splitPfInPossibleValuesOf :: GroundedAST.PFunc GroundedAST.Object -> Bool
    splitPfInPossibleValuesOf pf = case possibleValues pf oConds of
        KB.Object _                           -> undefined
        KB.AnyExcept excl                     -> not $ Set.member splitObj excl
        KB.InInterval from upto               -> from <= splitObj && splitObj <= upto
        KB.AnyExceptInInterval excl from upto -> from <= splitObj && splitObj <= upto && not (Set.member splitObj excl)

    leftCond  = KB.Object splitObj
    rightCond = case possibleValues splitPf oConds of
        KB.Object _                           -> error "object PF restricted to single object should never be selected to split on"
        KB.AnyExcept excl                     -> KB.AnyExcept $ Set.insert splitObj excl
        KB.InInterval from upto               -> KB.AnyExceptInInterval (Set.singleton splitObj) from upto
        KB.AnyExceptInInterval excl from upto -> KB.AnyExceptInInterval (Set.insert splitObj excl) from upto

splitNode f lf (HPT.ContinuousSplit splitPF spPoint) = splitNodeCommon f lf pLeft addCond leftCond rightCond
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
    rConds = KB.realConds $ KB.entryChoices f
    GroundedAST.RealDist cdf _ = GroundedAST.probabilisticFuncDef splitPF
    pfLabel           = GroundedAST.probabilisticFuncLabel splitPF
    addCond val conds = conds{KB.realConds = Map.insert pfLabel val $ KB.realConds conds}

splitNodeCommon :: RefWithNode
                -> Maybe HPT.LazyNode
                -> Probability
                -> (cond -> KB.Conditions -> KB.Conditions)
                -> cond
                -> cond
                -> KBState (KB.NodeRef HPT.CachedSplitPoints, Maybe HPT.LazyNode, KB.NodeRef HPT.CachedSplitPoints, Maybe HPT.LazyNode, Probability)
splitNodeCommon f lf pLeft addCond leftCond rightCond = do
    left  <- KB.condition f $ addCond leftCond  KB.noConditions
    right <- KB.condition f $ addCond rightCond KB.noConditions
    return ( KB.entryRef left
           , second (addCond leftCond)  <$> lf
           , KB.entryRef right
           , second (addCond rightCond) <$> lf
           , pLeft
           )

addCondObj :: GroundedAST.PFunc a -> KB.ObjCondition -> KB.Conditions -> KB.Conditions
addCondObj pf val conds = conds{KB.objConds = Map.insert pfLabel val $ KB.objConds conds}
    where
    pfLabel = GroundedAST.probabilisticFuncLabel pf

heuristicsCacheComputations :: KB.CacheComputations HPT.CachedSplitPoints
heuristicsCacheComputations = KB.CacheComputations
    { KB.cachedInfoComposed          = heuristicComposed
    , KB.cachedInfoBuildInPredBool   = heuristicBuildInPredBool
    , KB.cachedInfoBuildInPredString = heuristicBuildInPredString
    , KB.cachedInfoBuildInPredReal   = heuristicBuildInPredReal
    , KB.cachedInfoBuildInPredObject = heuristicBuildInPredObject
    , KB.cachedInfoDeterministic     = heuristicDeterministic
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

heuristicBuildInPredObject :: Map GroundedAST.PFuncLabel KB.ObjCondition
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
            Just (KB.Object obj)           -> (obj, obj, Set.empty)
            Just (KB.AnyExcept excl)       -> ( head $ List.filter (\i -> not $ Set.member i excl) [0..lastObj]
                                                   , head $ List.filter (\i -> not $ Set.member i excl) $ reverse [0..lastObj]
                                                   , excl
                                                   )
            Just (KB.InInterval from upto) -> (from, upto, Set.empty)
            Just (KB.AnyExceptInInterval excl from upto) ->
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

            -- precondition: first parameter should be >= 0
            appNTimes :: Integer -> (a -> a) -> a -> a
            appNTimes 0 _ x = x
            appNTimes n _ _ | n < 0 = error "precondition"
            appNTimes n f x = appNTimes (n - 1) f $ f x

heuristicComposed :: KB.NodeType -> Int -> [HPT.CachedSplitPoints] -> HPT.CachedSplitPoints
heuristicComposed op nPfs points = HPT.CachedSplitPoints
    proofsT
    proofsF
    (HPT.Composed $ composition points)
    where
    proofsT
        | op == KB.And = proofProduct allProofsT
        | otherwise         = proofSum     allProofsT
    proofsF
        | op == KB.Or  = proofProduct allProofsF
        | otherwise         = proofSum     allProofsF
    allProofsT = (\(HPT.CachedSplitPoints psT _ _) -> psT) <$> points
    allProofsF = (\(HPT.CachedSplitPoints _ psF _) -> psF) <$> points

    proofSum :: [Set HPT.Proof] -> Set HPT.Proof
    proofSum = restrictToN . Set.unions

    proofProduct :: [Set HPT.Proof] -> Set HPT.Proof
    proofProduct = foldl1' (\ps ps' ->
            restrictToN $ Set.unions [combineProofWithSet p ps | p <- Set.toList ps']
        )
        where
        combineProofWithSet :: HPT.Proof -> Set HPT.Proof -> Set HPT.Proof
        combineProofWithSet p = Set.fold
            ( \p' ps' -> case combineProofs p p' of
                  Just p'' -> Set.insert (HPT.Proof p'') ps'
                  _        -> ps'
            )
            Set.empty

        combineProofs :: HPT.Proof -> HPT.Proof -> Maybe (Map HPT.SplitPoint HPT.Choice)
        combineProofs (HPT.Proof x) (HPT.Proof y) = foldl' addProofElement (Just x) $ Map.toList y

        addProofElement :: Maybe (Map HPT.SplitPoint HPT.Choice)
                        -> (HPT.SplitPoint, HPT.Choice)
                        -> Maybe (Map HPT.SplitPoint HPT.Choice)
        addProofElement mbP (pt, choice) = do
            p <- mbP
            -- TODO: this check of proof consistency is only correct for bools
            case Map.lookup pt p of
                Nothing                          -> return $ Map.insert pt choice p
                Just choice' | choice == choice' -> return p
                _                                -> mzero

    restrictToN proofs = Set.fromList $
                         take 1 $
                         List.sortBy (\(HPT.Proof x) (HPT.Proof y) -> compare (Map.size x) (Map.size y)) $
                         Set.toList proofs

    composition :: [HPT.CachedSplitPoints] -> Map HPT.SplitPoint Int
    composition pts = foldl'
        (\pts' pt-> Set.fold (`Map.insert` nPfs) pts' $ primPts pt) -- set score for all split points from primitives to nr of PFs
        compositionComposed
        pts
        where
        compositionComposed :: Map HPT.SplitPoint Int
        compositionComposed = foldl'
                  (\splitPoints splitPoints' -> Map.unionWith (+) splitPoints $ ptsMap splitPoints')
                  Map.empty
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

