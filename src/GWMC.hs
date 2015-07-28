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
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Data.Map (Map)
import qualified Data.Map as Map
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
gwmcPSTs query rfuncDefs nnf = gwmc' nnf $ PST.empty $ NNF.uncondNodeLabel query
    where
        gwmc' :: NNF -> PST -> ([PST], NNF)
        gwmc' nnf pst = case iterate nnf pst of
            Nothing           -> ([], nnf)
            Just (nnf', pst') -> let (psts, nnf'') = gwmc' nnf' pst' in (pst' : psts, nnf'')

        iterate :: NNF -> PST -> Maybe (NNF, PST)
        iterate nnf (PST.ChoiceBool rFuncLabel p left right, _) = fmap newPST mbRes
            where
                newPST (nnf, first, second)
                    | leftFirst = (nnf, (PST.ChoiceBool rFuncLabel p first second, combineProbsChoice p first second))
                    | otherwise = (nnf, (PST.ChoiceBool rFuncLabel p second first, combineProbsChoice p second first))
                mbRes = case iterate nnf first of
                    Just (nnf', first') -> Just (nnf', first', second)
                    Nothing -> case iterate nnf second of
                        Just (nnf', second') -> Just (nnf', first, second')
                        Nothing -> Nothing
                (first, second) = if leftFirst then (left, right) else (right, left)
                leftFirst = PST.maxError left > PST.maxError right
        iterate nnf (PST.ChoiceReal rFuncLabel p splitPoint left right, _) = fmap newPSTNode mbRes
            where
                newPSTNode (nnf, first, second)
                    | leftFirst = (nnf, (PST.ChoiceReal rFuncLabel p splitPoint first second, combineProbsChoice p first second))
                    | otherwise = (nnf, (PST.ChoiceReal rFuncLabel p splitPoint second first, combineProbsChoice p second first))
                mbRes = case iterate nnf first of
                    Just (nnf', first') -> Just (nnf', first', second)
                    Nothing -> case iterate nnf second of
                        Just (nnf', second') -> Just (nnf', first, second')
                        Nothing -> Nothing
                (first, second) = if leftFirst then (left, right) else (right, left)
                leftFirst = PST.maxError left > PST.maxError right
        iterate nnf (PST.Decomposition op dec, _) = iterateDecomp (Set.toList dec)
            where
                iterateDecomp :: [PST] -> Maybe (NNF, PST)
                iterateDecomp [] = Nothing
                iterateDecomp (next:rest) = case iterate nnf next of
                    Just (nnf', newPst) -> let newChildren = Set.insert newPst (Set.delete next dec) in Just (nnf', (PST.Decomposition op newChildren, combineProbsDecomp op newChildren))
                    Nothing             -> iterateDecomp rest
        iterate nnf (PST.Finished _, _) = Nothing
        iterate nnf (PST.Unfinished nnfLabel, _) = case decompose nnfLabel nnf of
            Nothing -> case Map.lookup rFuncLabel rfuncDefs of
                    Just (AST.Flip p:_) -> Just (nnf'', (PST.ChoiceBool rFuncLabel p left right, combineProbsChoice p left right))
                        where
                            (leftNNFLabel,  nnf')  = NNF.conditionBool nnfLabel rFuncLabel True nnf
                            (rightNNFLabel, nnf'') = NNF.conditionBool nnfLabel rFuncLabel False nnf'
                            left  = toPSTNode leftNNFLabel nnf''
                            right = toPSTNode rightNNFLabel nnf''
                    Just (AST.RealDist cdf:_) -> let p = cdf splitPoint in Just (nnf'', (PST.ChoiceReal rFuncLabel p splitPoint left right, combineProbsChoice p left right))
                        where
                            (leftNNFLabel,  nnf')  = NNF.conditionReal nnfLabel rFuncLabel (Inf, Open splitPoint) nnf
                            (rightNNFLabel, nnf'') = NNF.conditionReal nnfLabel rFuncLabel (Open splitPoint, Inf) nnf'
                            left  = toPSTNode leftNNFLabel nnf''
                            right = toPSTNode rightNNFLabel nnf''
                            splitPoint = 0.0
                    _  -> error ("undefined rfunc " ++ rFuncLabel)

                    where
                        xxx = sortWith (\x -> let (p,n) = NNF.heuristicScores x nnfLabel nnf in p+n) $ Set.toList $ NNF.randomFunctions nnfLabel nnf
                        --xxxy = trace (foldl (\str rf -> str ++ "\n" ++ (show $ orderHeuristic nnfLabel rf) ++ " " ++ rf) ("\n" ++ show nnfLabel) xxx) xxx
                        rFuncLabel = head $ reverse xxx

                        toPSTNode nnfLabel nnf = case NNF.deterministicValue nnfLabel nnf of
                            Just True  -> (PST.Finished True,       (1.0,1.0))
                            Just False -> (PST.Finished False,      (0.0,0.0))
                            Nothing    -> (PST.Unfinished nnfLabel, (0.0,1.0))
            Just (op, decomposition) -> Just (nnf', (PST.Decomposition op psts, combineProbsDecomp op psts))
                where
                    (psts, nnf') = Set.foldr
                        (\dec (psts, nnf) ->
                            let (fresh, nnf') = if Set.size dec > 1 then
                                                    NNF.insertFresh (NNF.Operator op dec) nnf
                                                else
                                                    (getFirst dec, nnf)
                            in  (Set.insert (PST.Unfinished fresh, (0.0,1.0)) psts, nnf'))
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
