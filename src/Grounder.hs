-----------------------------------------------------------------------------
--
-- Module      :  Grounder
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

module Grounder
    ( groundPclp
    ) where
import AST (AST)
import qualified AST
import NNF (NNF)
import qualified NNF
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Data.Maybe (fromJust)
import BasicTypes
import Control.Arrow (first)

groundPclp :: AST -> (HashSet NNF.NodeRef, Maybe NNF.NodeRef, NNF)
groundPclp AST.AST {AST.queries=queries, AST.evidence=mbEvidence, AST.rules=rules} = case mbEvidence of
    Nothing -> (groundedQueries, Nothing, groundedNNF)
    Just ev -> let (groundedEvidence, groundedNNF') = groundRule ev groundedNNF
               in  (groundedQueries, Just groundedEvidence, groundedNNF')
    where
        (groundedQueries, groundedNNF) = Set.foldr (\q (refs,nnf) -> first (`Set.insert` refs) $ groundRule q nnf) (Set.empty, NNF.empty) queries

        groundRule :: PredicateLabel -> NNF -> (NNF.NodeRef, NNF)
        groundRule label nnf
            | NNF.member nnfLabel nnf = (NNF.RefComposed True nnfLabel, nnf) -- already added
            | nChildren == 0 = error "not implemented"
            | otherwise      = let (nnfChildren,nnf') = Set.foldr
                                    (\child (nnfChildren,nnf) ->
                                        let (newChild,nnf') = groundBody child nnf
                                        in  (Set.insert newChild nnfChildren, nnf')
                                    )
                                    (Set.empty,nnf)
                                    children
                               in first NNF.entryRef $ NNF.insert True nnfLabel NNF.Or nnfChildren nnf'
            where
                children = Map.lookupDefault (error "rule not found") label rules
                nChildren = Set.size children
                nnfLabel = NNF.uncondNodeLabel label

        groundBody :: AST.RuleBody -> NNF -> (NNF.NodeRef, NNF)
        groundBody (AST.RuleBody elements) nnf = case elements of
            []              -> error "not implemented"
            [singleElement] -> groundElement singleElement nnf
            elements        -> let (nnfChildren, nnf') = foldl
                                        (\(nnfChildren, nnf) el ->
                                            let (newChild,nnf') = groundElement el nnf
                                            in (Set.insert newChild nnfChildren, nnf')
                                        )
                                        (Set.empty, nnf)
                                        elements
                               in first NNF.entryRef $ NNF.insertFresh True NNF.And nnfChildren nnf'

        groundElement :: AST.RuleBodyElement -> NNF -> (NNF.NodeRef, NNF)
        groundElement (AST.UserPredicate label)   nnf = (NNF.RefComposed True $ NNF.uncondNodeLabel label, snd $ groundRule label nnf)
        groundElement (AST.BuildInPredicate pred) nnf = (NNF.RefBuildInPredicate pred, nnf)
