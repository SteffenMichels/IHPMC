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
import Data.Maybe (fromJust)

groundPclp :: AST -> NNF
groundPclp AST {queries=queries, rules=rules} = Set.fold NNF.simplify (foldl groundRule NNF.emptyNNF queries) (Set.fromList queries) where
    groundRule :: NNF -> PredicateLabel -> NNF
    groundRule nnf label
        | NNF.member label nnf = nnf -- already added
        | otherwise =
            let children = Map.findWithDefault [] label rules
            in case children of
            []            -> error "not implemented"
            children      -> let children = Map.findWithDefault [] label rules
                                 (nnfChildren,nnf') = foldl
                                        (\(nnfChildren,nnf) child ->
                                            let (newChild,nnf'') = groundBody child nnf
                                            in (Set.insert newChild nnfChildren, nnf'')
                                        )
                                        (Set.empty,nnf)
                                        children
                             in NNF.insert label (NNF.Operator NNF.Or nnfChildren) nnf'

    groundBody :: RuleBody -> NNF -> (NNF.NodeLabel, NNF)
    groundBody (RuleBody elements) nnf = case elements of
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

    groundElement :: RuleBodyElement -> NNF -> (NNF.NodeLabel, NNF)
    groundElement (UserPredicate label)   nnf = (label, groundRule nnf label)
    groundElement (BuildInPredicate pred) nnf = NNF.insertFresh (NNF.BuildInPredicate pred) nnf
