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
import qualified Data.HashSet as Set
import Data.Maybe (fromJust)
import BasicTypes

groundPclp :: AST -> NNF
groundPclp AST.AST {AST.queries=queries, AST.rules=rules} = Set.foldr groundRule NNF.empty queries
    where
        groundRule :: PredicateLabel -> NNF -> NNF
        groundRule label nnf
            | NNF.member nnfLabel nnf = nnf -- already added
            | nChildren == 0 = error "not implemented"
            | otherwise      = let (nnfChildren,nnf') = Set.foldr
                                    (\child (nnfChildren,nnf) ->
                                        let (newChild,nnf') = groundBody child nnf
                                        in  (Set.insert newChild nnfChildren, nnf')
                                    )
                                    (Set.empty,nnf)
                                    children
                               in snd $ NNF.insert True nnfLabel NNF.Or nnfChildren nnf'
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
                               in (\(e,nnf) -> (NNF.entryRef e, nnf)) $ NNF.insertFresh True NNF.And nnfChildren nnf'

        groundElement :: AST.RuleBodyElement -> NNF -> (NNF.NodeRef, NNF)
        groundElement (AST.UserPredicate label)   nnf = (NNF.RefComposed True $ NNF.uncondNodeLabel label, groundRule label nnf)
        groundElement (AST.BuildInPredicate pred) nnf = (NNF.RefBuildInPredicate pred, nnf)
