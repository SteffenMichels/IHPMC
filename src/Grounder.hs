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
import Control.Monad.Exception.Synchronous
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (fromJust)

groundPclp :: AST -> NNF
groundPclp AST.AST {AST.queries=queries, AST.rules=rules} = Set.fold NNF.simplify (Set.fold groundRule NNF.empty queries) queries where
    groundRule :: AST.PredicateLabel -> NNF -> NNF
    groundRule label nnf
        | NNF.member label nnf = nnf -- already added
        | nChildren == 0 = error "not implemented"
        | otherwise      = let (nnfChildren,nnf') = Set.fold
                                (\child (nnfChildren,nnf) ->
                                    let (newChild,nnf'') = groundBody child nnf
                                    in (Set.insert newChild nnfChildren, nnf'')
                                )
                                (Set.empty,nnf)
                                children
                           in NNF.insert label (NNF.Operator NNF.Or nnfChildren) nnf'
        where
            children = Map.findWithDefault (error "rule not found") label rules
            nChildren = Set.size children

    groundBody :: AST.RuleBody -> NNF -> (NNF.NodeLabel, NNF)
    groundBody (AST.RuleBody elements) nnf = case elements of
        []              -> error "not implemented"
        [singleElement] -> groundElement singleElement nnf
        elements        -> let (nnfChildren, nnf') = foldl
                                    (\(nnfChildren, nnf) el ->
                                        let (newChild,nnf'') = groundElement el nnf
                                        in (Set.insert newChild nnfChildren, nnf'')
                                    )
                                    (Set.empty, nnf)
                                    elements
                           in NNF.insertFresh (NNF.Operator NNF.And nnfChildren) nnf'

    groundElement :: AST.RuleBodyElement -> NNF -> (NNF.NodeLabel, NNF)
    groundElement (AST.UserPredicate label)   nnf = (label, groundRule label nnf)
    groundElement (AST.BuildInPredicate pred) nnf = NNF.insertFresh (NNF.BuildInPredicate pred) nnf
