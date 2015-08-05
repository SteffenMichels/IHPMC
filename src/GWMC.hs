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
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as Map
import qualified Data.HashMap.Lazy as HashMap
import qualified AST
import Text.Printf (printf)
import GHC.Exts (sortWith)
import Debug.Trace (trace)
import qualified Data.List as List
import Interval (Interval, IntervalLimit(..))
import Numeric (fromRat)

gwmc :: PredicateLabel -> HashMap RFuncLabel [AST.RFuncDef] -> NNF -> ([ProbabilityBounds], NNF)
gwmc query rfuncDefs nnf = (fmap PST.bounds psts, nnf') where
    (psts, nnf') = gwmcPSTs query rfuncDefs nnf

gwmcPSTs :: PredicateLabel -> HashMap RFuncLabel [AST.RFuncDef] -> NNF -> ([PST], NNF)
gwmcPSTs query rfuncDefs nnf = gwmc' nnf $ PST.initialNode $ NNF.uncondNodeLabel query
    where
        gwmc' :: NNF -> PSTNode -> ([PST], NNF)
        gwmc' nnf pstNode = case iterate nnf pstNode Map.empty of
            (nnf', pst@(PST.Finished _))              -> ([pst], nnf')
            (nnf', pst@(PST.Unfinished pstNode' _ _)) -> let (psts, nnf'') = gwmc' nnf' pstNode'
                                                         in  (pst : psts, nnf'')

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
                            (leftEntry,  nnf')  = NNF.conditionBool nnfLabel rf True nnf
                            (rightEntry, nnf'') = NNF.conditionBool nnfLabel rf False nnf'
                            left  = toPSTNode leftEntry
                            right = toPSTNode rightEntry
                    Just (AST.RealDist cdf icdf:_) -> (nnf'', PST.ChoiceReal rf p splitPoint left right, combineProbsChoice p left right, combineScoresChoice p left right)
                        where
                            p = (pUntilSplit-pUntilLower)/(pUntilUpper-pUntilLower)
                            pUntilLower = cdf' True curLower
                            pUntilUpper = cdf' False curUpper
                            pUntilSplit = cdf splitPoint
                            (leftEntry,  nnf')  = NNF.conditionReal nnfLabel rf (curLower, Open splitPoint) nnf
                            (rightEntry, nnf'') = NNF.conditionReal nnfLabel rf (Open splitPoint, curUpper) nnf'
                            left  = toPSTNode leftEntry
                            right = toPSTNode rightEntry
                            splitPoint = case (curLower, curUpper) of
                                (Inf, Inf)       -> 0.0
                                (Inf, Open u)    -> u-1.0
                                (Open l, Inf)    -> l+1.0
                                (Open l, Open u) -> (l+u)/2
                            (curLower, curUpper) = Map.lookupDefault (Inf, Inf) rf previousChoicesReal
                            cdf' lower Inf    = if lower then 0.0 else 1.0
                            cdf' _ (Open x)   = cdf x
                            cdf' _ (Closed x) = cdf x
                    _  -> error ("undefined rfunc " ++ rf)
                    where
                        xxx = sortWith (\(rf, (p,n)) -> -p+n) $ HashMap.toList $ NNF.entryScores $ NNF.augmentWithEntry nnfLabel nnf
                        --xxxy = trace (foldl (\str rf -> str ++ "\n" ++ (let (p,n) = NNF.heuristicScores rf nnfLabel nnf in show (p+n)) ++ " " ++ rf) ("\n" ++ show nnfLabel) xxx) xxx
                        rf = fst $ head xxx

                        toPSTNode entry = case NNF.entryNode entry of
                            NNF.Deterministic val -> PST.Finished $ if val then 1.0 else 0.0
                            _                     -> PST.Unfinished (PST.Leaf $ NNF.entryLabel entry) (0.0,1.0) (fromIntegral $ Set.size $ NNF.entryRFuncs entry)
            Just (op, decomposition) -> (nnf', PST.Decomposition op psts, (0.0,1.0), combineScoresDecomp psts)
                where
                    -- TODO: double NNF lookup!
                    (psts, nnf') = Set.foldr
                        (\dec (psts, nnf) ->
                            let (fresh, nnf') = if Set.size dec > 1 then
                                                    (\(e,nnf) -> (NNF.entryLabel e,nnf)) $ NNF.insertFresh (NNF.Operator op dec) nnf
                                                else
                                                    (getFirst dec, nnf)
                            in  (PST.Unfinished (PST.Leaf fresh) (0.0,1.0) (fromIntegral $ Set.size $ NNF.entryRFuncs (NNF.augmentWithEntry fresh nnf')):psts, nnf')
                        )
                        ([], nnf)
                        decomposition

        combineProbsChoice p left right = (p*leftLower+(1-p)*rightLower, p*leftUpper+(1-p)*rightUpper) where
            (leftLower,  leftUpper)  = PST.bounds left
            (rightLower, rightUpper) = PST.bounds right
        combineProbsDecomp NNF.And dec = foldr (\pst (l,u) -> let (l',u') = PST.bounds pst in (l'*l,u'*u)) (1.0, 1.0) dec
        combineProbsDecomp NNF.Or dec  = (1-nl, 1-nu) where
            (nl, nu) = foldr (\pst (l,u) -> let (l',u') = PST.bounds pst in (l*(1.0-l'), u*(1.0-u'))) (1.0, 1.0) dec

        combineScoresChoice p left right = (PST.score left + PST.score right)/2
        combineScoresDecomp dec          = foldr (\pst score -> score + PST.score pst) 0.0 dec/(fromIntegral $ length dec)::Double

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
                    | otherwise                                   = findFixpoint cur' curRFs' children'
                    where
                        (withSharedRFs, withoutSharedRFs) = List.partition (\c ->  not $ Set.null $ Set.intersection curRFs $ NNF.entryRFuncs c) $ Set.toList children
                        cur'      = Set.union cur $ Set.fromList withSharedRFs
                        curRFs'   = Set.foldr (\c curRFs -> Set.union curRFs $ NNF.entryRFuncs c) curRFs $ Set.fromList withSharedRFs
                        children' = Set.fromList withoutSharedRFs
