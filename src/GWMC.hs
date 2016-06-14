-----------------------------------------------------------------------------
--
-- Module      :  GWMC
-- Copyright   :
-- License     :  AllRightsReserved
--
-- Maintainer  :
-- Stability   :
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

module GWMC
    ( gwmc
    , gwmcEvidence
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
import Interval (Interval, IntervalLimit(..), IntervalLimitPoint(..), LowerUpper(..), (~<), (~>))
import qualified Interval
import Data.Maybe (mapMaybe, fromJust)
import Control.Arrow (first)
import Control.Monad.State.Strict
import Data.Foldable (foldlM)
import System.IO.Unsafe (unsafePerformIO)
import Exception
import Data.List (maximumBy)

type CachedSplitPoints = (Int, HashMap (RFuncLabel, SplitPoint) Double) -- number of rfs in primitives, split points + scores
type FState = State (Formula CachedSplitPoints)

data SplitPoint = DiscreteSplit | ContinuousSplit Rational deriving (Eq, Show, Generic)
instance Hashable SplitPoint

untilFinished :: Int -> ProbabilityBounds -> Bool
untilFinished _ _ = False

gwmc :: Formula.NodeRef -> (Int -> ProbabilityBounds -> Bool) -> HashMap RFuncLabel [AST.RFuncDef] -> Formula CachedSplitPoints -> ProbabilityBounds
gwmc query finishPred rfuncDefs f =  evalState (gwmc' 1 $ HPT.initialNode query) $ unsafePerformIO (runExceptionalT (Formula.exportAsDot "/tmp/o.dot" f) >> return f) where
    gwmc' :: Int -> HPTNode -> FState ProbabilityBounds
    gwmc' i pstNode = do
        pst <- GWMC.iterate pstNode 1.0 rfuncDefs
        case pst of
            pst@(HPT.Finished _)              -> return $ HPT.bounds pst
            pst@(HPT.Unfinished pstNode' _ _) -> let bounds = HPT.bounds pst
                                                 in if finishPred i $ HPT.bounds pst
                                                    then get >>= \f -> return $ unsafePerformIO (runExceptionalT (HPT.exportAsDot "/tmp/hpt.dot" pst >> Formula.exportAsDot "/tmp/f.dot" f) >> return bounds)
                                                    else gwmc' (i+1) pstNode'

gwmcEvidence :: Formula.NodeRef -> Formula.NodeRef -> (Int -> ProbabilityBounds -> Bool) -> HashMap RFuncLabel [AST.RFuncDef] -> Formula CachedSplitPoints -> ProbabilityBounds
gwmcEvidence query evidence finishPred rfuncDefs =  evalState (do
        queryAndEvidence    <- state $ Formula.insert Nothing True Formula.And (Set.fromList [queryRef True,  evidence])
        negQueryAndEvidence <- state $ Formula.insert Nothing True Formula.And (Set.fromList [queryRef False, evidence])
        gwmc' 1 (initHPT queryAndEvidence) (initHPT negQueryAndEvidence)
    ) where
    queryRef sign = case query of
        Formula.RefComposed qSign label                  -> Formula.RefComposed (sign == qSign) label
        Formula.RefBuildInPredicate pred prevChoicesReal -> Formula.RefBuildInPredicate (if sign then pred else AST.negatePred pred) prevChoicesReal
    initHPT nwr = HPT.Unfinished (HPT.initialNode $ Formula.entryRef nwr) (0.0,1.0) undefined

    gwmc' :: Int -> HPT -> HPT -> FState ProbabilityBounds
    gwmc' i qe nqe = case (qe, nqe) of
        _ | finishPred i bounds          -> return bounds
        (HPT.Finished _, HPT.Finished _) -> return bounds
        _ | HPT.maxError qe > HPT.maxError nqe -> do
            let (HPT.Unfinished pstNode _ _) = qe
            qe'  <- GWMC.iterate pstNode 1.0 rfuncDefs
            gwmc' (i+1) qe' nqe
        _ -> do
            let (HPT.Unfinished pstNode _ _) = nqe
            nqe' <- GWMC.iterate pstNode 1.0 rfuncDefs
            gwmc' (i+1) qe nqe'
        where
            bounds = probBounds qe nqe

    probBounds qe nqe = (lqe/(lqe+unqe), uqe/(uqe+lnqe)) where
        (lqe,  uqe)  = HPT.bounds qe
        (lnqe, unqe) = HPT.bounds nqe

iterate :: HPTNode -> Double -> HashMap RFuncLabel [AST.RFuncDef] -> FState HPT
iterate pstNode partChoiceProb rfuncDefs = do
    (pstNode', bounds@(l,u), score) <- iterateNode pstNode partChoiceProb
    return $ if l == u then HPT.Finished l
                       else HPT.Unfinished pstNode' bounds score
    where
        iterateNode :: HPTNode -> Double -> FState (HPTNode, ProbabilityBounds, Double)
        iterateNode (HPT.ChoiceBool rFuncLabel p left right) partChoiceProb = do
            (left, right) <- case (left, right) of
                (HPT.Unfinished pstNode _ _, _) | HPT.score left > HPT.score right ->
                    (,right) <$> GWMC.iterate pstNode (probToDouble p * partChoiceProb) rfuncDefs
                (_, HPT.Unfinished pstNode _ _) ->
                    (left,)  <$> GWMC.iterate pstNode (probToDouble (1-p) * partChoiceProb) rfuncDefs
                _ -> error "finished node should not be selected for iteration"
            return (HPT.ChoiceBool rFuncLabel p left right, combineProbsChoice p left right, combineScoresChoice left right)
        iterateNode (HPT.ChoiceReal rf p splitPoint left right) partChoiceProb = do
            (left, right) <- case (left, right) of
                (HPT.Unfinished pstNode _ _, _) | HPT.score left > HPT.score right ->
                    (,right) <$> GWMC.iterate pstNode (probToDouble p * partChoiceProb) rfuncDefs
                (_, HPT.Unfinished pstNode _ _) ->
                    (left,)  <$> GWMC.iterate pstNode (probToDouble (1-p) * partChoiceProb) rfuncDefs
                _ -> error "finished node should not be selected for iteration"
            return (HPT.ChoiceReal rf p splitPoint left right, combineProbsChoice p left right, combineScoresChoice left right)
        iterateNode (HPT.Decomposition op dec) partChoiceProb = do
            selectedChild <- GWMC.iterate selectedChildNode partChoiceProb rfuncDefs
            let dec' = selectedChild:tail sortedChildren
            return (HPT.Decomposition op dec', combineProbsDecomp op dec', combineScoresDecomp dec')
            where
                sortedChildren = sortWith (\c -> -HPT.score  c) dec
                selectedChildNode = case head sortedChildren of
                    HPT.Unfinished pstNode _ _ -> pstNode
                    _                          -> error "finished node should not be selected for iteration"
        iterateNode (HPT.Leaf ref) partChoiceProb = do
            f <- get
            case decompose ref f of
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
                                (curLower, curUpper) = Map.lookupDefault (Inf, Inf) splitRF $ Formula.entryPrevChoicesReal fEntry
                        _  -> error ("undefined rfunc " ++ splitRF)
                    where
                        ((splitRF, splitPoint), _) = head sortedCandidateSplitPoints--trace (show sortedCandidateSplitPoints) $
                        sortedCandidateSplitPoints = sortWith (negate . snd) $ Map.toList $ snd $ Formula.entryCachedInfo $ Formula.augmentWithEntry ref f

                        fEntry = Formula.augmentWithEntry ref f
                        toHPTNode p entry = case Formula.entryNode entry of
                            Formula.Deterministic val -> HPT.Finished $ if val then 1.0 else 0.0
                            _                         -> HPT.Unfinished (HPT.Leaf $ Formula.entryRef entry) (0.0,1.0) (probToDouble p * partChoiceProb)
                Just (origOp, decOp, sign, decomposition) -> do
                    psts <- foldlM (\psts dec -> do
                            fresh <- if Set.size dec > 1 then
                                    state $ \f -> first Formula.entryRef $ Formula.insert Nothing sign origOp dec f
                                else
                                    let single = getFirst dec in
                                    return $ if sign then single else Formula.negate single
                            return (HPT.Unfinished (HPT.Leaf fresh) (0.0,1.0) partChoiceProb:psts)
                        ) [] decomposition
                    return (HPT.Decomposition decOp psts, (0.0,1.0), combineScoresDecomp psts)

combineProbsChoice p left right = (p*leftLower+(1-p)*rightLower, p*leftUpper+(1-p)*rightUpper) where
    (leftLower,  leftUpper)  = HPT.bounds left
    (rightLower, rightUpper) = HPT.bounds right
combineProbsDecomp Formula.And dec = foldr (\pst (l,u) -> let (l',u') = HPT.bounds pst in (l'*l,u'*u)) (1.0, 1.0) dec
combineProbsDecomp Formula.Or dec  = (1-nl, 1-nu) where
    (nl, nu) = foldr (\pst (l,u) -> let (l',u') = HPT.bounds pst in (l*(1.0-l'), u*(1.0-u'))) (1.0, 1.0) dec

combineScoresChoice left right = max (HPT.score left) (HPT.score right)
combineScoresDecomp            = foldr (\pst score -> max score $ HPT.score pst) 0.0

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

determineSplitPoint :: RFuncLabel -> Interval -> HashMap RFuncLabel [AST.RFuncDef] -> HashMap RFuncLabel (Interval, Int) -> Formula.RefWithNode CachedSplitPoints -> Formula CachedSplitPoints -> Rational
determineSplitPoint rf (lower,upper) rfuncDefs prevChoicesReal fEntry f = fst $ head list
    where
        list = sortWith (\(point,score) -> -score) (Map.toList $ pointsWithScore fEntry)
        pointsWithScore entry
            | Set.member rf $ Formula.entryRFuncs entry = case Formula.entryNode entry of
                Formula.Composed op children  -> foldr combine Map.empty [pointsWithScore $ Formula.augmentWithEntry c f | c <- Set.toList children]
                Formula.BuildInPredicate pred _ -> Map.fromList $ points pred
                _                         -> Map.empty
            | otherwise = Map.empty

        points pred@(AST.RealIneq _ exprX exprY) = points''
            where
                rfOnLeft = Set.member rf $ AST.exprRandomFunctions exprX
                mbOtherIntervs = mapM (\rf -> ((rf,) . fst) <$> Map.lookup rf prevChoicesReal) (filter (rf /=) $ Set.toList $ AST.predRandomFunctions pred)
                points' = case mbOtherIntervs of
                    Nothing -> []
                    Just otherIntervs -> filter (\p -> (Interval.Point p Interval.InftePlus~> Interval.toPoint Lower lower) == Just True && (Interval.Point p Interval.InfteMinus ~< Interval.toPoint Upper upper) == Just True) possibleSolutions
                        where
                            possibleSolutions = [(if rfOnLeft then -1 else 1) * (sumExpr exprX c - sumExpr exprY c) | c <- partCorners]
                            -- partial corners of all other RFs occurring in pred (can only split on finite points)
                            partCorners
                                | null otherIntervs = [undefined] -- only single empty (not evaluated) corner needed in case of no other rf
                                | otherwise         = mapMaybe (mapM Interval.pointRational) $ Interval.corners otherIntervs

                -- split probability mass in some smart way if no other split is possible
                points''
                    | null points' = [(((fromIntegral nRfs-1)*equalSplit rf + (if rfOnLeft then 1 else -1) * (sumExpr exprY prefSplitPs - sumExpr exprX prefSplitPs))/fromIntegral nRfs, 1.0/fromIntegral nRfs)] -- penalty for higher-dimensional constraints
                    | otherwise    = [(p,1.0) | p <- points']

                prefSplitPs = Set.foldr (\rf ps -> Map.insert rf (equalSplit rf) ps) Map.empty rfs
                rfs = AST.predRandomFunctions pred
                nRfs = Set.size rfs

                equalSplit rf = case Map.lookup rf rfuncDefs of
                    Just (AST.RealDist cdf icdf:_) -> icdf ((pUntilLower + pUntilUpper)/2)
                        where
                            pUntilLower = cdf' cdf True  curLower
                            pUntilUpper = cdf' cdf False curUpper
                            (curLower, curUpper) = fst $ Map.lookupDefault ((Inf, Inf), undefined) rf prevChoicesReal
                    _ -> error "GWMC.equalSplit failed"

                sumExpr :: AST.Expr AST.RealN -> Map.HashMap RFuncLabel Rational-> Rational
                sumExpr (AST.RealConstant c) _ = c
                sumExpr (AST.UserRFunc rf') vals
                    | rf' == rf = 0
                    | otherwise = fromJust $ Map.lookup rf' vals
                sumExpr (AST.RealSum x y) vals = sumExpr x vals + sumExpr y vals

        combine :: HashMap Rational Double -> HashMap Rational Double -> HashMap Rational Double
        combine x y = foldr (\(p,score) map -> Map.insert p (score + Map.lookupDefault 0.0 p map) map) y $ Map.toList x

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
        (AST.RealIneq op exprX exprY) -> (nRfs, Map.fromList [((rf, splitPoint rf), probToDouble $ errorReduction rf (Set.filter (/= rf) predRfs) prevChoicesReal) | rf <- Set.toList predRfs])
            where
                errorReduction2 rf remRfs choices = pDiff where
                    (curLower',curUpper') = Map.lookupDefault (Inf,Inf) rf choices
                    pUntilLower = cdf' cdf True  curLower'
                    pUntilUpper = cdf' cdf False curUpper'
                    pDiff       = pUntilUpper - pUntilLower
                    (cdf, icdf) = case Map.lookup rf rfDefs of
                            Just (AST.RealDist cdf icdf:_) -> (cdf, icdf)
                bestReduction rfs choices = maximumBy (\(_,r) (_,s) -> compare r s) [(rf, errorReduction rf (Set.filter (/= rf) rfs) choices) | rf <- Set.toList rfs]
                errorReduction rf remRfs choices = leftRed + rightRed
                    where
                        leftRed  = errorRed' (Map.insert rf (curLower, Open splitP) choices)
                        rightRed = errorRed' (Map.insert rf (Open splitP, curUpper) choices)
                        (curLower,curUpper) = Map.lookupDefault (Inf,Inf) rf choices
                        errorRed' choices
                            | all ((==) $ Just True) checkedCorners || all ((==) $ Just False) checkedCorners = pDiff
                            | Set.null remRfs = 0
                            | otherwise = let (_,pDiff') = bestReduction remRfs choices
                                          in  pDiff*pDiff'/2
                            where
                                extremePoints  = Set.map (\rf' -> (rf', Map.lookupDefault (Inf,Inf) rf' choices)) predRfs
                                corners        = Interval.corners $ Set.toList extremePoints
                                checkedCorners = map (AST.checkRealIneqPred op exprX exprY) corners

                                (curLower',curUpper') = Map.lookupDefault (Inf,Inf) rf choices
                                pUntilLower = cdf' cdf True  curLower'
                                pUntilUpper = cdf' cdf False curUpper'
                                pDiff       = pUntilUpper - pUntilLower
                        (cdf, icdf) = case Map.lookup rf rfDefs of
                            Just (AST.RealDist cdf icdf:_) -> (cdf, icdf)

                        ContinuousSplit splitP = realSplitPoint rf cdf icdf

                splitPoint rf = case Map.lookup rf rfDefs of
                    Just (AST.RealDist cdf icdf:_) -> realSplitPoint rf cdf icdf
                    _  -> error ("undefined rfunc " ++ rf)

                realSplitPoint rf cdf icdf = let sppoint = splitPoint
                                             in ContinuousSplit sppoint
                        where
                            splitPoint
                                | null points' = equalSplit
                                | otherwise    = head points'
                                where
                                    equalSplit = icdf ((pUntilLower + pUntilUpper)/2) where
                                        pUntilLower = cdf' cdf True  curLower
                                        pUntilUpper = cdf' cdf False curUpper
                                        (curLower, curUpper) = Map.lookupDefault (Inf, Inf) rf prevChoicesReal

                                    {-sumExpr :: AST.Expr AST.RealN -> Map.HashMap RFuncLabel Rational-> Rational
                                    sumExpr (AST.RealConstant c) _ = c
                                    sumExpr (AST.UserRFunc rf') vals
                                        | rf' == rf = 0
                                        | otherwise = fromJust $ Map.lookup rf' vals
                                    sumExpr (AST.RealSum x y) vals = sumExpr x vals + sumExpr y vals-}

                                    (lower, upper) = Map.lookupDefault (Inf,Inf) rf prevChoicesReal
                                    rfOnLeft = Set.member rf $ AST.exprRandomFunctions exprX
                                    mbOtherIntervs = mapM (\rf -> (rf,) <$> Map.lookup rf prevChoicesReal) (filter (rf /=) $ Set.toList $ AST.predRandomFunctions pred)
                                    points' = case mbOtherIntervs of
                                        Nothing -> []
                                        Just otherIntervs -> mapMaybe Interval.pointRational possibleSolutions -- only points with rational component (non-infinite) are valid split points
                                            where
                                                -- only min and max which are in current interval are valid solutions
                                                possibleSolutions = filter
                                                                        (\p -> (p ~> Interval.toPoint Lower lower) == Just True && (p ~< Interval.toPoint Upper upper) == Just True)
                                                                        [minimum boundaryPoints, maximum boundaryPoints]
                                                -- boundary points (with Indet filtered out)
                                                boundaryPoints = filter (/= Indet) [let x = sumExpr exprX c - sumExpr exprY c in if rfOnLeft then -x else x | c <- partCorners]
                                                -- partial corners of all other RFs occurring in pred
                                                partCorners
                                                    | null otherIntervs = [undefined] -- only single empty (not evaluated) corner needed in case of no other rf
                                                    | otherwise         = Interval.corners otherIntervs
                                    sumExpr :: AST.Expr AST.RealN -> Map.HashMap RFuncLabel IntervalLimitPoint-> IntervalLimitPoint
                                    sumExpr (AST.RealConstant c) _ = Point c Interval.InfteNull
                                    sumExpr (AST.UserRFunc rf') vals
                                        | rf' == rf = Point 0 Interval.InfteNull
                                        | otherwise = fromJust $ Map.lookup rf' vals
                                    sumExpr (AST.RealSum x y) vals = sumExpr x vals + sumExpr y vals

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
