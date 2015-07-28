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
    , gwmcPSTs
    ) where
import NNF (NNF)
import qualified NNF
import PST (PST, PSTNode)
import qualified PST
import BasicTypes
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.HashMap.Lazy as HashMap
import qualified AST
import Data.Maybe (fromJust)
import Text.Printf (printf)
import GHC.Exts (sortWith)
import Debug.Trace (trace)
import qualified Data.List as List
import Interval (IntervalLimit(..))

gwmc :: PredicateLabel -> Map RFuncLabel [AST.RFuncDef] -> NNF -> ([ProbabilityBounds], NNF)
gwmc query rfuncDefs nnf = (fmap PST.bounds psts, nnf') where
    (psts, nnf') = gwmcPSTs query rfuncDefs nnf

gwmcPSTs :: PredicateLabel -> Map RFuncLabel [AST.RFuncDef] -> NNF -> ([PST], NNF)
gwmcPSTs query rfuncDefs nnf = gwmc' nnf $ PST.initialNode $ NNF.uncondNodeLabel query
    where
        gwmc' :: NNF -> PSTNode -> ([PST], NNF)
        gwmc' nnf pstNode = case iterate nnf pstNode of
            (nnf', pst@(PST.Finished _))            -> ([pst], nnf')
            (nnf', pst@(PST.Unfinished pstNode' _)) -> let (psts, nnf'') = gwmc' nnf' pstNode' in (pst : psts, nnf'')

        iterate :: NNF -> PSTNode -> (NNF, PST)
        iterate nnf pstNode
            | l == u    = (nnf', PST.Finished l)
            | otherwise = (nnf', PST.Unfinished pstNode' bounds)
            where
                (nnf', pstNode', bounds@(l,u)) = iterateNode nnf pstNode

        iterateNode :: NNF -> PSTNode -> (NNF, PSTNode, ProbabilityBounds)
        iterateNode nnf (PST.ChoiceBool rFuncLabel p left right) =
            (nnf', PST.ChoiceBool rFuncLabel p left' right', combineProbsChoice p left' right')
            where
                (nnf', left', right') = case (left,right) of
                        (PST.Unfinished pstNode _, _) | PST.maxError left > PST.maxError right ->
                            let (nnf'', left'') = iterate nnf pstNode
                            in  (nnf'', left'', right)
                        (_, PST.Unfinished pstNode _) ->
                            let (nnf'', right'') = iterate nnf pstNode
                            in  (nnf'', left, right'')
                        _ -> error "finished node should not be selected for iteration"
        iterateNode nnf (PST.ChoiceReal rFuncLabel p splitPoint left right) =
            (nnf', PST.ChoiceReal rFuncLabel p splitPoint left' right', combineProbsChoice p left' right')
            where
                (nnf', left', right') = case (left,right) of
                        (PST.Unfinished pstNode _, _) | PST.maxError left > PST.maxError right ->
                            let (nnf'', left'') = iterate nnf pstNode
                            in  (nnf'', left'', right)
                        (_, PST.Unfinished pstNode _) ->
                            let (nnf'', right'') = iterate nnf pstNode
                            in  (nnf'', left, right'')
                        _ -> error "finished node should not be selected for iteration"
        iterateNode nnf (PST.Decomposition op dec) =
            (nnf', PST.Decomposition op dec', combineProbsDecomp op dec')
            where
                selectedChild = head . sortWith (\c -> -PST.maxError c) $ Set.toList dec
                selectedChildNode = case selectedChild of
                    PST.Unfinished pstNode _ -> pstNode
                    _                        -> error "finished node should not be selected for iteration"
                (nnf', selectedChild') = iterate nnf selectedChildNode
                dec' = Set.insert selectedChild' (Set.delete selectedChild dec)
        iterateNode nnf (PST.Leaf nnfLabel) = case decompose nnfLabel nnf of
            Nothing -> case Map.lookup rFuncLabel rfuncDefs of
                    Just (AST.Flip p:_) -> (nnf'', PST.ChoiceBool rFuncLabel p left right, combineProbsChoice p left right)
                        where
                            (leftNNFLabel,  nnf')  = NNF.conditionBool nnfLabel rFuncLabel True nnf
                            (rightNNFLabel, nnf'') = NNF.conditionBool nnfLabel rFuncLabel False nnf'
                            left  = toPSTNode leftNNFLabel nnf''
                            right = toPSTNode rightNNFLabel nnf''
                    Just (AST.RealDist cdf:_) -> let p = cdf splitPoint in (nnf'', PST.ChoiceReal rFuncLabel p splitPoint left right, combineProbsChoice p left right)
                        where
                            (leftNNFLabel,  nnf')  = NNF.conditionReal nnfLabel rFuncLabel (Inf, Open splitPoint) nnf
                            (rightNNFLabel, nnf'') = NNF.conditionReal nnfLabel rFuncLabel (Open splitPoint, Inf) nnf'
                            left  = toPSTNode leftNNFLabel nnf''
                            right = toPSTNode rightNNFLabel nnf''
                            splitPoint = 0.0
                    _  -> error ("undefined rfunc " ++ rFuncLabel)
                    where
                        xxx = sortWith (\(rf, (p,n)) -> -p+n) $ HashMap.toList $ NNF.allScores nnfLabel nnf
                        --xxxy = trace (foldl (\str rf -> str ++ "\n" ++ (let (p,n) = NNF.heuristicScores rf nnfLabel nnf in show (p+n)) ++ " " ++ rf) ("\n" ++ show nnfLabel) xxx) xxx
                        rFuncLabel = fst $ head xxx

                        toPSTNode nnfLabel nnf = case NNF.deterministicValue nnfLabel nnf of
                            Just True  -> PST.Finished 1.0
                            Just False -> PST.Finished 0.0
                            Nothing    -> PST.Unfinished (PST.Leaf nnfLabel) (0.0,1.0)
            Just (op, decomposition) -> (nnf', PST.Decomposition op psts, combineProbsDecomp op psts)
                where
                    (psts, nnf') = Set.foldr
                        (\dec (psts, nnf) ->
                            let (fresh, nnf') = if Set.size dec > 1 then
                                                    NNF.insertFresh (NNF.Operator op dec) nnf
                                                else
                                                    (getFirst dec, nnf)
                            in  (Set.insert (PST.Unfinished (PST.Leaf fresh) (0.0,1.0)) psts, nnf'))
                        (Set.empty, nnf)
                        decomposition

        combineProbsChoice p left right = (p*leftLower+(1-p)*rightLower, p*leftUpper+(1-p)*rightUpper) where
            (leftLower,  leftUpper)  = PST.bounds left
            (rightLower, rightUpper) = PST.bounds right
        combineProbsDecomp NNF.And dec = Set.foldr (\pst (l,u) -> let (l',u') = PST.bounds pst in (l'*l,u'*u)) (1.0, 1.0) dec
        combineProbsDecomp NNF.Or dec  = (1-nl, 1-nu) where
            (nl, nu) = Set.foldr (\pst (l,u) -> let (l',u') = PST.bounds pst in (l*(1.0-l'), u*(1.0-u'))) (1.0, 1.0) dec

        showDec dec nnf = Set.foldr (\d str -> str ++ show d ++ " " ++ (show $ Set.foldr (\x rfs -> Set.union rfs $ NNF.randomFunctions x nnf) Set.empty d) ++ "\n") "\n" dec

        decompose :: NNF.NodeLabel -> NNF -> Maybe (NNF.NodeType, (HashSet (HashSet NNF.NodeLabel)))
        decompose nnfLabel nnf = case fromJust $ NNF.lookUp nnfLabel nnf of
            NNF.Operator op children -> let dec = decomposeChildren Set.empty children
                                        in  if Set.size dec == 1 then Nothing else Just (op, dec)
            _ -> Nothing
            where
                decomposeChildren :: (HashSet (HashSet NNF.NodeLabel)) -> (HashSet NNF.NodeLabel) -> (HashSet (HashSet NNF.NodeLabel))
                decomposeChildren dec children
                    | Set.null children = dec
                    | otherwise =
                        let first               = getFirst children
                            (new, _, children') = findFixpoint (Set.singleton first) (NNF.randomFunctions first nnf) (Set.delete first children)
                        in  decomposeChildren (Set.insert new dec) children'

                findFixpoint :: (HashSet NNF.NodeLabel) -> (HashSet RFuncLabel) -> (HashSet NNF.NodeLabel) -> (HashSet NNF.NodeLabel, HashSet RFuncLabel, HashSet NNF.NodeLabel)
                findFixpoint cur curRFs children
                    | Set.null children || List.null withSharedRFs = (cur, curRFs, children)
                    | otherwise                                   = findFixpoint cur' curRFs' children'
                    where
                        (withSharedRFs, withoutSharedRFs) = List.partition (\c ->  not $ Set.null $ Set.intersection curRFs $ NNF.randomFunctions c nnf) $ Set.toList children
                        cur'      = Set.union cur $ Set.fromList withSharedRFs
                        curRFs'   = Set.foldr (\c curRFs -> Set.union curRFs $ NNF.randomFunctions c nnf) curRFs $ Set.fromList withSharedRFs
                        children' = Set.fromList withoutSharedRFs
