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
    ) where
import Formula (Formula)
import qualified Formula
import PST (PST, PSTNode)
import qualified PST
import BasicTypes
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as Map
import qualified AST
import Text.Printf (printf)
import GHC.Exts (sortWith)
import Debug.Trace (trace)
import qualified Data.List as List
import Interval (Interval, IntervalLimit(..), LowerUpper(..))
import qualified Interval
import Numeric (fromRat)
import Data.Maybe (mapMaybe, fromJust)
import Control.Arrow (first)
import Control.Applicative ((<$>))
import Control.Monad.State.Strict
import Data.Foldable (foldlM)

import System.IO.Unsafe (unsafePerformIO)
import Exception

type FState = State Formula

untilFinished :: Int -> ProbabilityBounds -> Bool
untilFinished _ _ = False

gwmc :: Formula.NodeRef -> (Int -> ProbabilityBounds -> Bool) -> HashMap RFuncLabel [AST.RFuncDef] -> Formula -> ProbabilityBounds
gwmc query finishPred rfuncDefs =  evalState (gwmc' 1 $ PST.initialNode query) where
    gwmc' :: Int -> PSTNode -> FState ProbabilityBounds
    gwmc' i pstNode = do
        pst <- GWMC.iterate pstNode Map.empty 1.0 rfuncDefs
        case pst of
            pst@(PST.Finished _)              -> return $ PST.bounds pst
            pst@(PST.Unfinished pstNode' _ _) -> let bounds = PST.bounds pst
                                                 in if finishPred i $ PST.bounds pst
                                                    then return $ unsafePerformIO (runExceptionalT (PST.exportAsDot "/tmp/pst.dot" pst) >> return bounds)
                                                    else gwmc' (i+1) pstNode'

gwmcEvidence :: Formula.NodeRef -> Formula.NodeRef -> HashMap RFuncLabel [AST.RFuncDef] -> Formula -> [ProbabilityBounds]
gwmcEvidence query evidence rfuncDefs f = probBounds <$> evalState (do
        queryAndEvidence    <- state $ Formula.insert Nothing True Formula.And (Set.fromList [queryRef True,  evidence])
        negQueryAndEvidence <- state $ Formula.insert Nothing True Formula.And (Set.fromList [queryRef False, evidence])
        gwmc' (initPST queryAndEvidence) (initPST negQueryAndEvidence)
    ) f
    where
        gwmc' :: PST -> PST -> FState [(PST, PST)]
        gwmc' (PST.Finished _) (PST.Finished _) = return []
        gwmc' qe nqe
            | PST.maxError qe > PST.maxError nqe = do
                let (PST.Unfinished pstNode _ _) = qe
                qe'  <- GWMC.iterate pstNode Map.empty 1.0 rfuncDefs
                rest <- gwmc' qe' nqe
                return $ (qe', nqe) : rest
            | otherwise = do
                let (PST.Unfinished pstNode _ _) = nqe
                nqe' <- GWMC.iterate pstNode Map.empty 1.0 rfuncDefs
                rest <- gwmc' qe nqe'
                return $ (qe, nqe') : rest

        probBounds (qe, nqe) = (lqe/(lqe+unqe), uqe/(uqe+lnqe)) where
            (lqe,  uqe)  = PST.bounds qe
            (lnqe, unqe) = PST.bounds nqe

        initPST nwr = PST.Unfinished (PST.initialNode $ Formula.entryRef nwr) (0.0,1.0) undefined
        queryRef sign = case query of
            Formula.RefComposed qSign label  -> Formula.RefComposed (sign == qSign) label
            Formula.RefBuildInPredicate pred -> Formula.RefBuildInPredicate $ if sign then pred else AST.negatePred pred

iterate :: PSTNode -> HashMap RFuncLabel (Interval, Int) -> Double -> HashMap RFuncLabel [AST.RFuncDef] -> FState PST
iterate pstNode previousChoicesReal partChoiceProb rfuncDefs = do
    (pstNode', bounds@(l,u), score) <- iterateNode pstNode previousChoicesReal partChoiceProb
    return $ if l == u then PST.Finished l
                       else PST.Unfinished pstNode' bounds score
    where
        iterateNode :: PSTNode -> HashMap RFuncLabel (Interval, Int) -> Double -> FState (PSTNode, ProbabilityBounds, Double)
        iterateNode (PST.ChoiceBool rFuncLabel p left right) previousChoicesReal partChoiceProb = do
            (left, right) <- case (left, right) of
                (PST.Unfinished pstNode _ _, _) | PST.score left > PST.score right ->
                    (,right) <$> GWMC.iterate pstNode previousChoicesReal (probToDouble p * partChoiceProb) rfuncDefs
                (_, PST.Unfinished pstNode _ _) ->
                    (left,)  <$> GWMC.iterate pstNode previousChoicesReal (probToDouble (1-p) * partChoiceProb) rfuncDefs
                _ -> error "finished node should not be selected for iteration"
            return (PST.ChoiceBool rFuncLabel p left right, combineProbsChoice p left right, combineScoresChoice left right)
        iterateNode (PST.ChoiceReal rf p splitPoint left right) previousChoicesReal partChoiceProb = do
            (left, right) <- case (left, right) of
                (PST.Unfinished pstNode _ _, _) | PST.score left > PST.score right ->
                    (,right) <$> GWMC.iterate pstNode (Map.insert rf ((curLower, Open splitPoint), curCount+1) previousChoicesReal) (probToDouble p * partChoiceProb) rfuncDefs
                (_, PST.Unfinished pstNode _ _) ->
                    (left,)  <$> GWMC.iterate pstNode (Map.insert rf ((Open splitPoint, curUpper), curCount+1) previousChoicesReal) (probToDouble (1-p) * partChoiceProb) rfuncDefs
                _ -> error "finished node should not be selected for iteration"
            return (PST.ChoiceReal rf p splitPoint left right, combineProbsChoice p left right, combineScoresChoice left right)
            where
                ((curLower, curUpper), curCount) = Map.lookupDefault ((Inf, Inf), 0) rf previousChoicesReal
        iterateNode (PST.Decomposition op dec) previousChoicesReal partChoiceProb = do
            selectedChild <- GWMC.iterate selectedChildNode previousChoicesReal partChoiceProb rfuncDefs
            let dec' = selectedChild:tail sortedChildren
            return (PST.Decomposition op dec', combineProbsDecomp op dec', combineScoresDecomp dec')
            where
                sortedChildren = sortWith (\c -> -PST.score  c) dec
                selectedChildNode = case head sortedChildren of
                    PST.Unfinished pstNode _ _ -> pstNode
                    _                          -> error "finished node should not be selected for iteration"
        iterateNode (PST.Leaf ref) previousChoicesReal partChoiceProb = do
            f <- get
            case decompose ref f of
                Nothing -> case Map.lookup rf rfuncDefs of
                    Just (AST.Flip p:_) -> do
                        leftEntry  <- state $ Formula.conditionBool fEntry rf True
                        rightEntry <- state $ Formula.conditionBool fEntry rf False
                        let left  = toPSTNode p leftEntry
                        let right = toPSTNode (1-p) rightEntry
                        return (PST.ChoiceBool rf p left right, combineProbsChoice p left right, combineScoresChoice left right)
                    Just (AST.RealDist cdf _:_) -> do
                        leftEntry  <- state $ Formula.conditionReal fEntry rf (curLower, Open splitPoint) previousChoicesReal
                        rightEntry <- state $ Formula.conditionReal fEntry rf (Open splitPoint, curUpper) previousChoicesReal
                        let left  = toPSTNode p leftEntry
                        let right = toPSTNode (1-p) rightEntry
                        return (PST.ChoiceReal rf p splitPoint left right, combineProbsChoice p left right, combineScoresChoice left right)
                        where
                            p = (pUntilSplit-pUntilLower)/(pUntilUpper-pUntilLower)
                            pUntilLower = cdf' cdf True curLower
                            pUntilUpper = cdf' cdf False curUpper
                            pUntilSplit = cdf splitPoint
                            splitPoint = determineSplitPoint rf curInterv rfuncDefs previousChoicesReal fEntry f
                            curInterv@(curLower, curUpper) = fst $ Map.lookupDefault ((Inf, Inf), undefined) rf previousChoicesReal
                    _  -> error ("undefined rfunc " ++ rf)
                    where
                        rf = fst $ head xxx
                        xxx = sortWith rfScore $ Map.toList $ snd $ Formula.entryScores $ Formula.augmentWithEntry ref f
                        --xxxy = trace (foldl (\str x@(rf,_) -> str ++ "\n" ++ show (rfScore x) ++ " " ++ rf) ("\n" ++ show ref) xxx) xxx
                        rfScore (rf, s) = case Map.lookup rf previousChoicesReal of
                            Just (_, count) -> (count, -s)
                            _               -> (case Map.lookup rf rfuncDefs of Just (AST.Flip p:_) -> -1; _ -> 0, -s)

                        fEntry = Formula.augmentWithEntry ref f
                        toPSTNode p entry = case Formula.entryNode entry of
                            Formula.Deterministic val -> PST.Finished $ if val then 1.0 else 0.0
                            _                         -> PST.Unfinished (PST.Leaf $ Formula.entryRef entry) (0.0,1.0) (probToDouble p * partChoiceProb)
                Just (origOp, decOp, sign, decomposition) -> do
                    psts <- foldlM (\psts dec -> do
                            fresh <- if Set.size dec > 1 then
                                    state $ \f -> first Formula.entryRef $ Formula.insert Nothing sign origOp dec f
                                else
                                    let single = getFirst dec in
                                    return $ if sign then single else Formula.negate single
                            return (PST.Unfinished (PST.Leaf fresh) (0.0,1.0) partChoiceProb:psts)
                        ) [] decomposition
                    return (PST.Decomposition decOp psts, (0.0,1.0), combineScoresDecomp psts)

combineProbsChoice p left right = (p*leftLower+(1-p)*rightLower, p*leftUpper+(1-p)*rightUpper) where
    (leftLower,  leftUpper)  = PST.bounds left
    (rightLower, rightUpper) = PST.bounds right
combineProbsDecomp Formula.And dec = foldr (\pst (l,u) -> let (l',u') = PST.bounds pst in (l'*l,u'*u)) (1.0, 1.0) dec
combineProbsDecomp Formula.Or dec  = (1-nl, 1-nu) where
    (nl, nu) = foldr (\pst (l,u) -> let (l',u') = PST.bounds pst in (l*(1.0-l'), u*(1.0-u'))) (1.0, 1.0) dec

combineScoresChoice left right = max (PST.score left) (PST.score right)
combineScoresDecomp            = foldr (\pst score -> max score $ PST.score pst) 0.0

decompose :: Formula.NodeRef -> Formula -> Maybe (Formula.NodeType, Formula.NodeType, Bool, HashSet (HashSet Formula.NodeRef))
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

determineSplitPoint :: RFuncLabel -> Interval -> HashMap RFuncLabel [AST.RFuncDef] -> HashMap RFuncLabel (Interval, Int) -> Formula.RefWithNode -> Formula -> Rational
determineSplitPoint rf (lower,upper) rfuncDefs prevChoicesReal fEntry f = fst $ head list
    where
        list = sortWith (\(point,score) -> -score) (Map.toList $ pointsWithScore fEntry)
        pointsWithScore entry
            | Set.member rf $ Formula.entryRFuncs entry = case Formula.entryNode entry of
                Formula.Composed op children  -> foldr combine Map.empty [pointsWithScore $ Formula.augmentWithEntry c f | c <- Set.toList children]
                Formula.BuildInPredicate pred -> Map.fromList $ points pred
                _                         -> Map.empty
            | otherwise = Map.empty

        points (AST.RealIn _ (l,u)) = mapMaybe
                                        (\x -> case x of
                                            Inf      -> Nothing
                                            Open p   -> Just (p, 1.0)
                                            Closed p -> Just (p, 1.0)
                                        ) [l,u]
        points pred@(AST.RealIneq _ exprX exprY) = points''
            where
                rfOnLeft = Set.member rf $ AST.exprRandomFunctions exprX
                mbOtherIntervs = mapM (\rf -> ((rf,) . fst) <$> Map.lookup rf prevChoicesReal) (filter (rf /=) $ Set.toList $ AST.predRandomFunctions pred)
                points' = case mbOtherIntervs of
                    Nothing -> []
                    Just otherIntervs -> filter (\p -> Interval.PointPlus p > Interval.toPoint Lower lower && Interval.PointMinus p < Interval.toPoint Upper upper) possibleSolutions
                        where
                            possibleSolutions = [(if rfOnLeft then -1 else 1) * (sumExpr exprX c - sumExpr exprY c) | c <- partCorners]
                            -- partial corners of all other RFs occurring in pred (can only split on finite points)
                            partCorners = mapMaybe (mapM Interval.pointRational) $ Interval.corners otherIntervs

                -- split probability mass in some smart way if no other split is possible
                points''
                    | null points' = [((2*equalSplit rf + (if rfOnLeft then 1 else -1) * (sumExpr exprY prefSplitPs - sumExpr exprX prefSplitPs))/fromIntegral (Set.size rfs), 1.0/fromIntegral (Set.size rfs))] -- penalty for higher-dimensional constraints
                    | otherwise    = [(p,1.0) | p <- points']

                prefSplitPs = Set.foldr (\rf ps -> Map.insert rf (equalSplit rf) ps) Map.empty rfs
                rfs = AST.predRandomFunctions pred

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
                sumExpr (AST.RealSum x y)  vals = sumExpr x vals + sumExpr y vals

        combine :: HashMap Rational Double -> HashMap Rational Double -> HashMap Rational Double
        combine x y = foldr (\(p,score) map -> Map.insert p (score + Map.lookupDefault 0.0 p map) map) y $ Map.toList x

cdf' _ lower Inf      = if lower then 0.0 else 1.0
cdf' cdf _ (Open x)   = cdf x
cdf' cdf _ (Closed x) = cdf x
