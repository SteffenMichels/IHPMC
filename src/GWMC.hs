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
import PST (PST)
import qualified PST
import BasicTypes
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified AST
import Data.Maybe (fromJust)
import Text.Printf (printf)
import GHC.Exts (sortWith)
import Debug.Trace (trace)

gwmc :: PredicateLabel -> Map RFuncLabel [AST.RFuncDef] -> NNF -> ([ProbabilityBounds], NNF)
gwmc query rfuncDefs nnf = (fmap PST.bounds psts, nnf') where
    (psts, nnf') = gwmcPSTs query rfuncDefs nnf

gwmcPSTs :: PredicateLabel -> Map RFuncLabel [AST.RFuncDef] -> NNF -> ([PST], NNF)
gwmcPSTs query rfuncDefs nnf = gwmc' nnf $ PST.empty $ NNF.uncondNodeLabel query
    where
        gwmc' :: NNF -> PST -> ([PST], NNF)
        gwmc' nnf pst = case iterate nnf pst of
            Nothing           -> ([], nnf)
            Just (nnf', pst') -> let (psts, nnf'') = gwmc' nnf' pst' in (pst' : psts, nnf'')

        iterate :: NNF -> PST -> Maybe (NNF, PST)
        iterate nnf (PST.Choice rFuncLabel p left right) = case iterate nnf first of
            Just (nnf', first') -> Just (nnf', PST.Choice rFuncLabel p first' second)
            Nothing -> case iterate nnf second of
                Just (nnf', second') -> Just (nnf', PST.Choice rFuncLabel p first second')
                Nothing -> Nothing
            where
                (first, second) = if PST.maxError left > PST.maxError right then (left, right) else (right, left)
        iterate nnf (PST.Decomposition op dec) = iterateDecomp (Set.toList dec)
            where
                iterateDecomp :: [PST] -> Maybe (NNF, PST)
                iterateDecomp [] = Nothing
                iterateDecomp (next:rest) = case iterate nnf next of
                    Just (nnf', newPst) -> Just (nnf', PST.Decomposition op $ Set.insert newPst (Set.delete next dec))
                    Nothing             -> iterateDecomp rest
        iterate nnf (PST.Finished _) = Nothing
        iterate nnf (PST.Unfinished nnfLabel) = case decompose nnfLabel nnf of
            Nothing -> Just (nnf'', PST.Choice rFuncLabel falseP left right) where
                xxx = sortWith (\x -> orderHeuristic nnfLabel x + orderHeuristicCounter nnfLabel x) $ Set.toList $ NNF.randomFunctions nnfLabel nnf
                xxxy = trace (foldl (\str rf -> str ++ "\n" ++ (show $ orderHeuristic nnfLabel rf) ++ " " ++ rf) ("\n" ++ show nnfLabel) xxx) xxx
                rFuncLabel = head $ reverse xxx
                (leftNNFLabel,  nnf')  = NNF.condition nnfLabel rFuncLabel True nnf
                (rightNNFLabel, nnf'') = NNF.condition nnfLabel rFuncLabel False nnf'
                left  = toPSTNode leftNNFLabel
                right = toPSTNode rightNNFLabel
                falseP = case Map.lookup rFuncLabel rfuncDefs of
                    Just (AST.Flip p:_) -> 1-p

                toPSTNode nnfLabel = case NNF.deterministicValue nnfLabel nnf'' of
                    Just val -> PST.Finished val
                    Nothing  -> PST.Unfinished nnfLabel

                orderHeuristic :: NNF.NodeLabel -> RFuncLabel -> Double
                orderHeuristic nnfLabel rfLabel = case node of
                    NNF.Operator NNF.Or children ->
                        (Set.fold (\c score -> orderHeuristic c rfLabel + score) 0.0 children)
                    NNF.Operator NNF.And children ->
                        (Set.fold (\c score -> orderHeuristic c rfLabel + score) 0.0 children) / fromIntegral (Set.size rFuncs)
                    _ -> if Set.member rfLabel rFuncs then
                            1
                         else
                            0
                    where
                        node = fromJust $ NNF.lookUp nnfLabel nnf
                        rFuncs = NNF.randomFunctions nnfLabel nnf

                orderHeuristicCounter :: NNF.NodeLabel -> RFuncLabel -> Double
                orderHeuristicCounter nnfLabel rfLabel = case node of
                    NNF.Operator NNF.Or children ->
                        (Set.fold (\c score -> orderHeuristic c rfLabel + score) 0.0 children) / fromIntegral (Set.size rFuncs)
                    NNF.Operator NNF.And children ->
                        (Set.fold (\c score -> orderHeuristic c rfLabel + score) 0.0 children)
                    _ -> if Set.member rfLabel rFuncs then
                            1
                         else
                            0
                    where
                        node = fromJust $ NNF.lookUp nnfLabel nnf
                        rFuncs = NNF.randomFunctions nnfLabel nnf
            Just (op, decomposition) -> Just (nnf', PST.Decomposition op psts)
                where
                    (psts, nnf') = Set.fold
                        (\dec (psts, nnf) ->
                            let (fresh, nnf') = if Set.size dec > 1 then
                                                    NNF.insertFresh (NNF.Operator op dec) nnf
                                                else
                                                    (Set.findMin dec, nnf)
                            in  (Set.insert (PST.Unfinished fresh) psts, nnf'))
                        (Set.empty, nnf)
                        decomposition

        showDec dec nnf = Set.fold (\d str -> str ++ show d ++ " " ++ (show $ Set.fold (\x rfs -> Set.union rfs $ NNF.randomFunctions x nnf) Set.empty d) ++ "\n") "\n" dec

        decompose :: NNF.NodeLabel -> NNF -> Maybe (NNF.NodeType, (Set (Set NNF.NodeLabel)))
        decompose nnfLabel nnf = case fromJust $ NNF.lookUp nnfLabel nnf of
            NNF.Operator op children -> let dec = decomposeChildren Set.empty children
                                        in  if Set.size dec == 1 then Nothing else Just (op, dec)
            _ -> Nothing
            where
                decomposeChildren :: (Set (Set NNF.NodeLabel)) -> (Set NNF.NodeLabel) -> (Set (Set NNF.NodeLabel))
                decomposeChildren dec children
                    | Set.null children = dec
                    | otherwise =
                        let first               = Set.findMin children
                            (new, _, children') = findFixpoint (Set.singleton first) (NNF.randomFunctions first nnf) (Set.delete first children)
                        in  decomposeChildren (Set.insert new dec) children'

                findFixpoint :: (Set NNF.NodeLabel) -> (Set RFuncLabel) -> (Set NNF.NodeLabel) -> (Set NNF.NodeLabel, Set RFuncLabel, Set NNF.NodeLabel)
                findFixpoint cur curRFs children
                    | Set.null children || Set.null withSharedRFs = (cur, curRFs, children)
                    | otherwise                                   = findFixpoint cur' curRFs' children'
                    where
                        (withSharedRFs, withoutSharedRFs) = Set.partition (\c ->  not $ Set.null $ Set.intersection curRFs $ NNF.randomFunctions c nnf) children
                        cur'      = Set.union cur withSharedRFs
                        curRFs'   = Set.fold (\c curRFs -> Set.union curRFs $ NNF.randomFunctions c nnf) curRFs withSharedRFs
                        children' = withoutSharedRFs
