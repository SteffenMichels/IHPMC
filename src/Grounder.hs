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
                                        let (newChild,b,nnf') = groundBody child nnf
                                        in  (Set.insert (newChild,b) nnfChildren, nnf')
                                    )
                                    (Set.empty,nnf)
                                    children
                               in (\(_,_,nnf) -> nnf) $ NNF.insert nnfLabel NNF.Or nnfChildren nnf'
            where
                children = Map.lookupDefault (error "rule not found") label rules
                nChildren = Set.size children
                nnfLabel = NNF.uncondNodeLabel label

        groundBody :: AST.RuleBody -> NNF -> (NNF.NodeRef, Bool, NNF)
        groundBody (AST.RuleBody elements) nnf = case elements of
            []              -> error "not implemented"
            [singleElement] -> groundElement singleElement nnf
            elements        -> let (nnfChildren, nnf') = foldl
                                        (\(nnfChildren, nnf) el ->
                                            let (newChild,b,nnf') = groundElement el nnf
                                            in (Set.insert (newChild, b) nnfChildren, nnf')
                                        )
                                        (Set.empty, nnf)
                                        elements
                               in (\(e,b,nnf) -> (NNF.entryRef e,b,nnf)) $ NNF.insertFresh NNF.And nnfChildren nnf'

        groundElement :: AST.RuleBodyElement -> NNF -> (NNF.NodeRef, Bool, NNF)
        groundElement (AST.UserPredicate label)   nnf = (NNF.RefComposed $ NNF.uncondNodeLabel label, True, groundRule label nnf)
        groundElement (AST.BuildInPredicate pred) nnf = (NNF.RefBuildInPredicate pred, True, nnf)
