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
import AST
import NNF (NNF)
import qualified NNF
import Control.Monad.Exception.Synchronous
import qualified Data.Map as Map
import qualified Data.Set as Set

groundPclp :: AST -> NNF
groundPclp AST {queries=queries, rules=rules} = foldl groundRule NNF.emptyNNF queries where
    groundRule :: NNF -> PredicateLabel -> NNF
    groundRule nnf label
        | NNF.member label nnf = nnf -- already added
        | otherwise =
            let children      = Map.findWithDefault [] label rules
                (newNode,nnf') = case children of
                    []            -> error "not implemented"
                    [singleChild] -> error "not implemented" -- mapFst (\label -> ) (groundBody singleChild)
                    children      -> let (nnfChildren,nnf'') = foldl
                                            (\(nnfChildren,nnf) child ->
                                                let (newChild,nnf''') = groundBody child nnf
                                                in (Set.insert newChild nnfChildren,nnf''')
                                            )
                                            (Set.empty,nnf)
                                            children
                                     in (NNF.Operator NNF.Or nnfChildren, nnf'')
            in NNF.insert label newNode nnf'

    groundBody :: RuleBody -> NNF -> (NNF.NodeLabel, NNF)
    groundBody (RuleBody elements) nnf =
        let (newNode,nnf') = case elements of
                []              -> error "not implemented"
                [singleElement] -> error "not implemented"
                elements        -> let (nnfChildren,nnf'') = foldl
                                        (\(nnfChildren,nnf) el ->
                                            let (newChild,nnf''') = groundElement el nnf
                                            in (Set.insert newChild nnfChildren,nnf''')
                                        )
                                        (Set.empty,nnf)
                                        elements
                                   in (NNF.Operator NNF.And nnfChildren, nnf'')
        in NNF.insertFresh newNode nnf'

    groundElement :: RuleBodyElement -> NNF -> (NNF.NodeLabel, NNF)
    groundElement (UserPredicate label)   nnf = (label, nnf)
    groundElement (BuildInPredicate pred) nnf = NNF.insertFresh (NNF.BuildInPredicate pred) nnf
