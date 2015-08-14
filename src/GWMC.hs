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
import Interval (Interval, IntervalLimit(..))
import qualified Interval
import Numeric (fromRat)
import Data.Maybe (mapMaybe)

gwmc :: PredicateLabel -> HashMap RFuncLabel [AST.RFuncDef] -> NNF -> [ProbabilityBounds]
gwmc query rfuncDefs nnf = fmap (\(pst,_) -> PST.bounds pst) results where
    results = gwmcDebug query rfuncDefs nnf

gwmcDebug :: PredicateLabel -> HashMap RFuncLabel [AST.RFuncDef] -> NNF -> [(PST, NNF)]
gwmcDebug query rfuncDefs nnf = gwmc' nnf $ PST.initialNode $ NNF.uncondNodeLabel query
    where
        gwmc' :: NNF -> PSTNode -> [(PST, NNF)]
        gwmc' nnf pstNode = case iterate nnf pstNode Map.empty of
            (nnf', pst@(PST.Finished _))              -> [(pst,nnf')]
            (nnf', pst@(PST.Unfinished pstNode' _ _)) -> let results = gwmc' nnf' pstNode'
                                                         in  (pst,nnf') : results

        iterate :: NNF -> PSTNode -> HashMap RFuncLabel Interval -> (NNF, PST)
        iterate nnf pstNode previousChoicesReal
            | l == u    = (nnf', PST.Finished l)
            | otherwise = (nnf', PST.Unfinished pstNode' bounds score)
            where
                (nnf', pstNode', bounds@(l,u), score) = iterateNode nnf pstNode previousChoicesReal

        iterateNode :: NNF -> PSTNode -> HashMap RFuncLabel Interval -> (NNF, PSTNode, ProbabilityBounds, Double)
        iterateNode nnf (PST.ChoiceBool rFuncLabel p left right) previousChoicesReal =
            (nnf', PST.ChoiceBool rFuncLabel p left' right', combineProbsChoice p left' right', combineScoresChoice p left' right')
            where
                (nnf', left', right') = case (left,right) of
                        (PST.Unfinished pstNode _ _, _) | errorScore left > errorScore right ->
                            let (nnf'', left'') = iterate nnf pstNode previousChoicesReal
                            in  (nnf'', left'', right)
                        (_, PST.Unfinished pstNode _ _) ->
                            let (nnf'', right'') = iterate nnf pstNode previousChoicesReal
                            in  (nnf'', left, right'')
                        _ -> error "finished node should not be selected for iteration"
        iterateNode nnf (PST.ChoiceReal rf p splitPoint left right) previousChoicesReal =
            (nnf', PST.ChoiceReal rf p splitPoint left' right', combineProbsChoice p left' right', combineScoresChoice p left' right')
            where
                (nnf', left', right') = case (left,right) of
                        (PST.Unfinished pstNode _ _, _) | errorScore left > errorScore right ->
                            let (nnf'', left'') = iterate nnf pstNode (Map.insert rf (curLower, Open splitPoint) previousChoicesReal)
                            in  (nnf'', left'', right)
                        (_, PST.Unfinished pstNode _ _) ->
                            let (nnf'', right'') = iterate nnf pstNode (Map.insert rf (Open splitPoint, curUpper) previousChoicesReal)
                            in  (nnf'', left, right'')
                        _ -> error "finished node should not be selected for iteration"
                (curLower, curUpper) = Map.lookupDefault (Inf, Inf) rf previousChoicesReal
        iterateNode nnf (PST.Decomposition op dec) previousChoicesReal =
            (nnf', PST.Decomposition op dec', combineProbsDecomp op dec', combineScoresDecomp dec')
            where
                sortedChildren = sortWith (\c -> -errorScore c) dec
                selectedChild  = head sortedChildren
                selectedChildNode = case selectedChild of
                    PST.Unfinished pstNode _ _ -> pstNode
                    _                          -> error "finished node should not be selected for iteration"
                (nnf', selectedChild') = iterate nnf selectedChildNode previousChoicesReal
                dec' = selectedChild':tail sortedChildren
        iterateNode nnf (PST.Leaf nnfLabel) previousChoicesReal = case decompose nnfLabel nnf of
            Nothing -> case Map.lookup rf rfuncDefs of
                    Just (AST.Flip p:_) -> (nnf'', PST.ChoiceBool rf p left right, combineProbsChoice p left right, combineScoresChoice p left right)
                        where
                            (leftEntry,  nnf')  = NNF.conditionBool nnfEntry rf True nnf
                            (rightEntry, nnf'') = NNF.conditionBool nnfEntry rf False nnf'
                            left  = toPSTNode leftEntry
                            right = toPSTNode rightEntry
                    Just (AST.RealDist cdf icdf:_) -> (nnf'', PST.ChoiceReal rf p splitPoint left right, combineProbsChoice p left right, combineScoresChoice p left right)
                        where
                            p = (pUntilSplit-pUntilLower)/(pUntilUpper-pUntilLower)
                            pUntilLower = cdf' cdf True curLower
                            pUntilUpper = cdf' cdf False curUpper
                            pUntilSplit = cdf splitPoint
                            (leftEntry,  nnf')  = NNF.conditionReal nnfEntry rf (curLower, Open splitPoint) previousChoicesReal nnf
                            (rightEntry, nnf'') = NNF.conditionReal nnfEntry rf (Open splitPoint, curUpper) previousChoicesReal nnf'
                            left  = toPSTNode leftEntry
                            right = toPSTNode rightEntry
                            splitPoint = determineSplitPoint rf curInterv pUntilLower pUntilUpper icdf nnfEntry nnf
                            curInterv@(curLower, curUpper) = Map.lookupDefault (Inf, Inf) rf previousChoicesReal
                    _  -> error ("undefined rfunc " ++ rf)
                    where
                        xxx = sortWith (\(rf, (p,n)) ->
                                case Map.lookup rf previousChoicesReal of
                                    Just (l,u) -> let Just (AST.RealDist cdf _:_) = Map.lookup rf rfuncDefs
                                                      currentP = fromRat (cdf' cdf True u - cdf' cdf False l)
                                                  in  (-currentP * abs (p-n), -currentP)
                                    _          -> (-abs (p-n), -1.0)
                              ) $ Map.toList $ NNF.entryScores $ NNF.augmentWithEntry nnfLabel nnf
                        xxxy = trace (foldl (\str (rf,(p,n)) -> str ++ "\n" ++ (show (p+n)) ++ " " ++ rf) ("\n" ++ show nnfLabel) xxx) xxx
                        rf = fst $ head xxx
                        nnfEntry = NNF.augmentWithEntry nnfLabel nnf
                        toPSTNode entry = case NNF.entryNode entry of
                            NNF.Deterministic val -> PST.Finished $ if val then 1.0 else 0.0
                            _                     -> PST.Unfinished (PST.Leaf $ NNF.entryLabel entry) (0.0,1.0) (fromIntegral $ Set.size $ NNF.entryRFuncs entry)
                        cdf' _ lower Inf    = if lower then 0.0 else 1.0
                        cdf' cdf _ (Open x)   = cdf x
                        cdf' cdf _ (Closed x) = cdf x
            Just (op, decomposition) -> (nnf', PST.Decomposition op psts, (0.0,1.0), combineScoresDecomp psts)
                where
                    (psts, nnf') = Set.foldr
                        (\dec (psts, nnf) ->
                            let (fresh, nnf') = if Set.size dec > 1 then
                                                    NNF.insertFresh (NNF.Operator op dec) nnf
                                                else
                                                    (NNF.augmentWithEntry (getFirst dec) nnf, nnf)
                            in  (PST.Unfinished (PST.Leaf $ NNF.entryLabel fresh) (0.0,1.0) (fromIntegral $ Set.size $ NNF.entryRFuncs fresh):psts, nnf')
                        )
                        ([], nnf)
                        decomposition

combineProbsChoice p left right = (p*leftLower+(1-p)*rightLower, p*leftUpper+(1-p)*rightUpper) where
    (leftLower,  leftUpper)  = PST.bounds left
    (rightLower, rightUpper) = PST.bounds right
combineProbsDecomp NNF.And dec = foldr (\pst (l,u) -> let (l',u') = PST.bounds pst in (l'*l,u'*u)) (1.0, 1.0) dec
combineProbsDecomp NNF.Or dec  = (1-nl, 1-nu) where
    (nl, nu) = foldr (\pst (l,u) -> let (l',u') = PST.bounds pst in (l*(1.0-l'), u*(1.0-u'))) (1.0, 1.0) dec

combineScoresChoice p left right = (PST.score left + PST.score right){-/2-}
combineScoresDecomp dec          = foldr (\pst score -> score + PST.score pst) 0.0 dec{-/(fromIntegral $ length dec)::Double-}

errorScore pst
    | maxError == 0.0 = 0.0
    | otherwise       = maxError/PST.score pst
    where
        maxError = fromRat $ PST.maxError pst::Double

decompose :: NNF.NodeLabel -> NNF -> Maybe (NNF.NodeType, (HashSet (HashSet NNF.NodeLabel)))
decompose nnfLabel nnf = case NNF.entryNode $ NNF.augmentWithEntry nnfLabel nnf of
    NNF.Operator op children -> let dec = decomposeChildren Set.empty $ Set.map (\c -> NNF.augmentWithEntry c nnf) children
                                in  if Set.size dec == 1 then Nothing else Just (op, dec)
    _ -> Nothing
    where
        decomposeChildren :: HashSet (HashSet NNF.LabelWithEntry) -> HashSet NNF.LabelWithEntry -> HashSet (HashSet NNF.NodeLabel)
        decomposeChildren dec children
            | Set.null children = Set.map (Set.map NNF.entryLabel) dec
            | otherwise =
                let first               = getFirst children
                    (new, _, children') = findFixpoint (Set.singleton first) (NNF.entryRFuncs first) (Set.delete first children)
                in  decomposeChildren (Set.insert new dec) children'

        findFixpoint :: HashSet NNF.LabelWithEntry -> HashSet RFuncLabel -> HashSet NNF.LabelWithEntry -> (HashSet NNF.LabelWithEntry, HashSet RFuncLabel, HashSet NNF.LabelWithEntry)
        findFixpoint cur curRFs children
            | Set.null children || List.null withSharedRFs = (cur, curRFs, children)
            | otherwise                                    = findFixpoint cur' curRFs' children'
            where
                (withSharedRFs, withoutSharedRFs) = List.partition (\c ->  not $ Set.null $ Set.intersection curRFs $ NNF.entryRFuncs c) $ Set.toList children
                cur'      = Set.union cur $ Set.fromList withSharedRFs
                curRFs'   = Set.foldr (\c curRFs -> Set.union curRFs $ NNF.entryRFuncs c) curRFs $ Set.fromList withSharedRFs
                children' = Set.fromList withoutSharedRFs

determineSplitPoint :: RFuncLabel -> Interval -> Probability -> Probability -> (Probability -> Rational) -> NNF.LabelWithEntry -> NNF -> Rational
determineSplitPoint rf curInterv pUntilLower pUntilUpper icdf nnfEntry nnf = fst $ head list
    where
        list = sortWith (\(point,score) -> -score) (Map.toList $ pointsWithScore nnfEntry)
        listTrace = trace (show list ++ show rf ++ (show $ NNF.entryLabel nnfEntry)) list
        pointsWithScore entry
            | Set.member rf $ NNF.entryRFuncs entry = case NNF.entryNode entry of
                NNF.Operator op children  -> foldr combine Map.empty [pointsWithScore $ NNF.augmentWithEntry c nnf | c <- Set.toList children]
                NNF.BuildInPredicate pred -> Map.fromList $ points pred
                _                         -> Map.empty
            | otherwise = Map.empty

        points (AST.RealIn _ (l,u)) = mapMaybe
                                        (\x -> case x of
                                            Inf      -> Nothing
                                            Open p   -> Just (p, 1.0)
                                            Closed p -> Just (p, 1.0)
                                        ) [l,u]
        points pred = [(icdf ((pUntilLower + pUntilUpper)/2), 1.0/(fromIntegral $ Set.size $ AST.predRandomFunctions pred))]

        combine :: HashMap Rational Double -> HashMap Rational Double -> HashMap Rational Double
        combine x y = foldr (\(p,score) map -> Map.insert p (score + Map.lookupDefault 0.0 p map) map) y $ Map.toList x
