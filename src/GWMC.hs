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
    , gwmcDebug
    ) where
import NNF (NNF)
import qualified NNF
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

gwmc :: PredicateLabel -> HashMap RFuncLabel [AST.RFuncDef] -> NNF -> [ProbabilityBounds]
gwmc query rfuncDefs nnf = fmap (\(pst,_) -> PST.bounds pst) results where
    results = gwmcDebug query rfuncDefs nnf

gwmcDebug :: PredicateLabel -> HashMap RFuncLabel [AST.RFuncDef] -> NNF -> [(PST, NNF)]
gwmcDebug query rfuncDefs nnf = gwmc' nnf $ PST.initialNode $ NNF.RefComposed True $ NNF.uncondNodeLabel query
    where
        gwmc' :: NNF -> PSTNode -> [(PST, NNF)]
        gwmc' nnf pstNode = case GWMC.iterate nnf pstNode Map.empty 1.0 rfuncDefs of
            (nnf', pst@(PST.Finished _))              -> [(pst,nnf')]
            (nnf', pst@(PST.Unfinished pstNode' _ _)) -> let results = gwmc' nnf' pstNode'
                                                         in  (pst,nnf') : results

gwmcEvidence :: PredicateLabel -> PredicateLabel -> HashMap RFuncLabel [AST.RFuncDef] -> NNF -> [ProbabilityBounds]
gwmcEvidence query evidence rfuncDefs nnf = probBounds <$> gwmc' (initPST queryAndEvidence) (initPST negQueryAndEvidence) nnf
    where
        gwmc' :: PST -> PST -> NNF -> [(PST, PST, NNF)]
        gwmc' (PST.Finished _) (PST.Finished _) _ = []
        gwmc' qe nqe nnf
            | PST.maxError qe > PST.maxError nqe = let (PST.Unfinished pstNode _ _) = qe
                                                       (nnf', qe')  = GWMC.iterate nnf pstNode Map.empty 1.0 rfuncDefs
                                                       rest = gwmc' qe' nqe nnf'
                                                   in  (qe', nqe, nnf') : rest
            | otherwise                          = let (PST.Unfinished pstNode _ _) = nqe
                                                       (nnf', nqe') = GWMC.iterate nnf pstNode Map.empty 1.0 rfuncDefs
                                                       rest = gwmc' qe nqe' nnf'
                                                   in  (qe, nqe', nnf') : rest

        probBounds (qe, nqe, _) = (lqe/(lqe+unqe), uqe/(uqe+lnqe)) where
            (lqe,  uqe)  = PST.bounds qe
            (lnqe, unqe) = PST.bounds nqe

        initPST nwr = PST.Unfinished (PST.initialNode $ NNF.entryRef nwr) (0.0,1.0) undefined
        (queryAndEvidence,    nnf')  = NNF.insertFresh True NNF.And (Set.fromList [queryRef True,  evidenceRef]) nnf
        (negQueryAndEvidence, nnf'') = NNF.insertFresh True NNF.And (Set.fromList [queryRef False, evidenceRef]) nnf'
        queryRef sign = NNF.RefComposed sign $ NNF.uncondNodeLabel query
        evidenceRef   = NNF.RefComposed True $ NNF.uncondNodeLabel evidence

iterate :: NNF -> PSTNode -> HashMap RFuncLabel Interval -> Double -> HashMap RFuncLabel [AST.RFuncDef] -> (NNF, PST)
iterate nnf pstNode previousChoicesReal partChoiceProb rfuncDefs
    | l == u    = (nnf', PST.Finished l)
    | otherwise = (nnf', PST.Unfinished pstNode' bounds score)
    where
        (nnf', pstNode', bounds@(l,u), score) = iterateNode nnf pstNode previousChoicesReal partChoiceProb

        iterateNode :: NNF -> PSTNode -> HashMap RFuncLabel Interval -> Double -> (NNF, PSTNode, ProbabilityBounds, Double)
        iterateNode nnf (PST.ChoiceBool rFuncLabel p left right) previousChoicesReal partChoiceProb =
            (nnf', PST.ChoiceBool rFuncLabel p left' right', combineProbsChoice p left' right', combineScoresChoice left' right')
            where
                (nnf', left', right') = case (left,right) of
                        (PST.Unfinished pstNode _ _, _) | PST.score left > PST.score  right ->
                            let (nnf'', left'') = GWMC.iterate nnf pstNode previousChoicesReal ((fromRat p::Double)*partChoiceProb) rfuncDefs
                            in  (nnf'', left'', right)
                        (_, PST.Unfinished pstNode _ _) ->
                            let (nnf'', right'') = GWMC.iterate nnf pstNode previousChoicesReal ((fromRat (1-p)::Double)*partChoiceProb) rfuncDefs
                            in  (nnf'', left, right'')
                        _ -> error "finished node should not be selected for iteration"
        iterateNode nnf (PST.ChoiceReal rf p splitPoint left right) previousChoicesReal partChoiceProb =
            (nnf', PST.ChoiceReal rf p splitPoint left' right', combineProbsChoice p left' right', combineScoresChoice left' right')
            where
                (nnf', left', right') = case (left,right) of
                        (PST.Unfinished pstNode _ _, _) | PST.score  left > PST.score  right ->
                            let (nnf'', left'') = GWMC.iterate nnf pstNode (Map.insert rf (curLower, Open splitPoint) previousChoicesReal) ((fromRat p::Double)*partChoiceProb) rfuncDefs
                            in  (nnf'', left'', right)
                        (_, PST.Unfinished pstNode _ _) ->
                            let (nnf'', right'') = GWMC.iterate nnf pstNode (Map.insert rf (Open splitPoint, curUpper) previousChoicesReal) ((fromRat (1-p)::Double)*partChoiceProb) rfuncDefs
                            in  (nnf'', left, right'')
                        _ -> error "finished node should not be selected for iteration"
                (curLower, curUpper) = Map.lookupDefault (Inf, Inf) rf previousChoicesReal
        iterateNode nnf (PST.Decomposition op dec) previousChoicesReal partChoiceProb =
            (nnf', PST.Decomposition op dec', combineProbsDecomp op dec', combineScoresDecomp dec')
            where
                sortedChildren = sortWith (\c -> -PST.score  c) dec
                selectedChild  = head sortedChildren
                selectedChildNode = case selectedChild of
                    PST.Unfinished pstNode _ _ -> pstNode
                    _                          -> error "finished node should not be selected for iteration"
                (nnf', selectedChild') = GWMC.iterate nnf selectedChildNode previousChoicesReal partChoiceProb rfuncDefs
                dec' = selectedChild':tail sortedChildren
        iterateNode nnf (PST.Leaf ref) previousChoicesReal partChoiceProb = case decompose ref nnf of
            Nothing -> case Map.lookup rf rfuncDefs of
                    Just (AST.Flip p:_) -> (nnf'', PST.ChoiceBool rf p left right, combineProbsChoice p left right, combineScoresChoice left right)
                        where
                            (leftEntry,  nnf')  = NNF.conditionBool nnfEntry rf True nnf
                            (rightEntry, nnf'') = NNF.conditionBool nnfEntry rf False nnf'
                            left  = toPSTNode p leftEntry
                            right = toPSTNode (1-p) rightEntry
                    Just (AST.RealDist cdf icdf:_) -> (nnf'', PST.ChoiceReal rf p splitPoint left right, combineProbsChoice p left right, combineScoresChoice left right)
                        where
                            p = (pUntilSplit-pUntilLower)/(pUntilUpper-pUntilLower)
                            pUntilLower = cdf' cdf True curLower
                            pUntilUpper = cdf' cdf False curUpper
                            pUntilSplit = cdf splitPoint
                            (leftEntry,  nnf')  = NNF.conditionReal nnfEntry rf (curLower, Open splitPoint) previousChoicesReal nnf
                            (rightEntry, nnf'') = NNF.conditionReal nnfEntry rf (Open splitPoint, curUpper) previousChoicesReal nnf'
                            left  = toPSTNode p leftEntry
                            right = toPSTNode (1-p) rightEntry
                            splitPoint = determineSplitPoint rf curInterv pUntilLower pUntilUpper icdf previousChoicesReal nnfEntry nnf
                            curInterv@(curLower, curUpper) = Map.lookupDefault (Inf, Inf) rf previousChoicesReal
                    _  -> error ("undefined rfunc " ++ rf)
                    where
                        rf = fst $ head xxx
                        xxx = sortWith rfScore $ Map.toList $ NNF.entryScores $ NNF.augmentWithEntry ref nnf
                        xxxy = trace (foldl (\str x@(rf,(p,n)) -> str ++ "\n" ++ show (rfScore x) ++ " " ++ rf) ("\n" ++ show ref) xxx) xxx
                        rfScore (rf, (p,n)) = case Map.lookup rf previousChoicesReal of
                            Just (l,u) -> let Just (AST.RealDist cdf _:_) = Map.lookup rf rfuncDefs
                                              currentP = fromRat (cdf' cdf False u - cdf' cdf True l)
                                          in  (-currentP * abs (p-n), -currentP)
                            _          -> (-abs (p-n), -1.0)

                        nnfEntry = NNF.augmentWithEntry ref nnf
                        toPSTNode p entry = case NNF.entryNode entry of
                            NNF.Deterministic val -> PST.Finished $ if val then 1.0 else 0.0
                            _                     -> PST.Unfinished (PST.Leaf $ NNF.entryRef entry) (0.0,1.0) ((fromRat p::Double)*partChoiceProb)
                        cdf' _ lower Inf    = if lower then 0.0 else 1.0
                        cdf' cdf _ (Open x)   = cdf x
                        cdf' cdf _ (Closed x) = cdf x
            Just (origOp, decOp, sign, decomposition) -> (nnf', PST.Decomposition decOp psts, (0.0,1.0), combineScoresDecomp psts)
                where
                    (psts, nnf') = Set.foldr
                        (\dec (psts, nnf) ->
                            let (fresh, nnf') = if Set.size dec > 1 then
                                                    first NNF.entryRef $ NNF.insertFresh sign origOp dec nnf
                                                else
                                                    let single = getFirst dec
                                                    in  (if sign then single else negate single, nnf)
                            in  (PST.Unfinished (PST.Leaf fresh) (0.0,1.0) partChoiceProb:psts, nnf')
                        )
                        ([], nnf)
                        decomposition

                    negate (NNF.RefComposed sign label)   = NNF.RefComposed (not sign) label
                    negate (NNF.RefBuildInPredicate pred) = NNF.RefBuildInPredicate (AST.negatePred pred)
                    negate (NNF.RefDeterministic val)     = NNF.RefDeterministic (not val)

combineProbsChoice p left right = (p*leftLower+(1-p)*rightLower, p*leftUpper+(1-p)*rightUpper) where
    (leftLower,  leftUpper)  = PST.bounds left
    (rightLower, rightUpper) = PST.bounds right
combineProbsDecomp NNF.And dec = foldr (\pst (l,u) -> let (l',u') = PST.bounds pst in (l'*l,u'*u)) (1.0, 1.0) dec
combineProbsDecomp NNF.Or dec  = (1-nl, 1-nu) where
    (nl, nu) = foldr (\pst (l,u) -> let (l',u') = PST.bounds pst in (l*(1.0-l'), u*(1.0-u'))) (1.0, 1.0) dec

combineScoresChoice left right = max (PST.score left) (PST.score right)
combineScoresDecomp            = foldr (\pst score -> max score $ PST.score pst) 0.0

decompose :: NNF.NodeRef -> NNF -> Maybe (NNF.NodeType, NNF.NodeType, Bool, HashSet (HashSet NNF.NodeRef))
decompose ref nnf = case NNF.entryNode $ NNF.augmentWithEntry ref nnf of
    NNF.Composed op children -> let dec = decomposeChildren Set.empty $ Set.map (`NNF.augmentWithEntry` nnf) children
                                in  if Set.size dec == 1 then Nothing else Just (op, decOp op, sign, dec)
    _ -> Nothing
    where
        decomposeChildren :: HashSet (HashSet NNF.RefWithNode) -> HashSet NNF.RefWithNode -> HashSet (HashSet NNF.NodeRef)
        decomposeChildren dec children
            | Set.null children = Set.map (Set.map NNF.entryRef) dec
            | otherwise =
                let first               = getFirst children
                    (new, _, children') = findFixpoint (Set.singleton first) (NNF.entryRFuncs first) (Set.delete first children)
                in  decomposeChildren (Set.insert new dec) children'

        findFixpoint :: HashSet NNF.RefWithNode -> HashSet RFuncLabel -> HashSet NNF.RefWithNode -> (HashSet NNF.RefWithNode, HashSet RFuncLabel, HashSet NNF.RefWithNode)
        findFixpoint cur curRFs children
            | Set.null children || List.null withSharedRFs = (cur, curRFs, children)
            | otherwise                                    = findFixpoint cur' curRFs' children'
            where
                (withSharedRFs, withoutSharedRFs) = List.partition (not . Set.null . Set.intersection curRFs . NNF.entryRFuncs) $ Set.toList children
                cur'      = Set.union cur $ Set.fromList withSharedRFs
                curRFs'   = Set.foldr (\c curRFs -> Set.union curRFs $ NNF.entryRFuncs c) curRFs $ Set.fromList withSharedRFs
                children' = Set.fromList withoutSharedRFs
        decOp op
            | sign = op
            | otherwise = case op of
                NNF.And -> NNF.Or
                NNF.Or  -> NNF.And
        sign = case ref of
            NNF.RefComposed sign _ -> sign
            _                      -> error "nodes other than composed ones have to sign"

determineSplitPoint :: RFuncLabel -> Interval -> Probability -> Probability -> (Probability -> Rational) -> HashMap RFuncLabel Interval -> NNF.RefWithNode -> NNF -> Rational
determineSplitPoint rf (lower,upper) pUntilLower pUntilUpper icdf prevChoicesReal nnfEntry nnf = fst $ head list
    where
        list = sortWith (\(point,score) -> -score) (Map.toList $ pointsWithScore nnfEntry)
        listTrace = trace (show list ++ show rf ++ show (NNF.entryRef nnfEntry)) list
        pointsWithScore entry
            | Set.member rf $ NNF.entryRFuncs entry = case NNF.entryNode entry of
                NNF.Composed op children  -> foldr combine Map.empty [pointsWithScore $ NNF.augmentWithEntry c nnf | c <- Set.toList children]
                NNF.BuildInPredicate pred -> Map.fromList $ points pred
                _                         -> Map.empty
            | otherwise = Map.empty

        points (AST.RealIn _ (l,u)) = mapMaybe
                                        (\x -> case x of
                                            Inf      -> Nothing
                                            Open p   -> Just (p, 1.0)
                                            Closed p -> Just (p, 1.0)
                                        ) [l,u]
        points pred = if Set.size (AST.predRandomFunctions pred) == 2 then points'' else error "determineSplitPoint: not implemented"
            where
                otherRf = let [x,y] = Set.toList $ AST.predRandomFunctions pred in if x == rf then y else x
                mbOtherInterv = Map.lookup otherRf prevChoicesReal
                points' = case mbOtherInterv of
                    Nothing -> []
                    Just (otherLower, otherUpper) ->
                        -- points must be in interval and not at boundary
                        filter (\p -> Interval.PointPlus p > Interval.toPoint Lower lower && Interval.PointMinus p < Interval.toPoint Upper upper) rationalPoints
                        where
                            -- can only split at rational points
                            rationalPoints = mapMaybe Interval.pointRational [Interval.toPoint Lower otherLower, Interval.toPoint Upper otherUpper]

                -- split probability mass in two equal part if no other split is possible
                points''
                    | null points' = [(icdf ((pUntilLower + pUntilUpper)/2), 1.0/fromIntegral (Set.size $ AST.predRandomFunctions pred))]
                    | otherwise    = [(p,1.0) | p <- points']

        combine :: HashMap Rational Double -> HashMap Rational Double -> HashMap Rational Double
        combine x y = foldr (\(p,score) map -> Map.insert p (score + Map.lookupDefault 0.0 p map) map) y $ Map.toList x
