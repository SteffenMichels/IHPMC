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
import Formula (Formula)
import qualified Formula
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Data.Maybe (fromJust)
import BasicTypes
import Control.Arrow (first)
import Text.Printf (printf)

groundPclp :: AST -> (HashSet Formula.NodeRef, Maybe Formula.NodeRef, Formula)
groundPclp AST.AST {AST.queries=queries, AST.evidence=mbEvidence, AST.rules=rules} = case mbEvidence of
    Nothing -> (groundedQueries, Nothing, groundedFormula)
    Just ev -> let (groundedEvidence, groundedFormula') = groundRule ev groundedFormula
               in  (groundedQueries, Just groundedEvidence, groundedFormula')
    where
        (groundedQueries, groundedFormula) = Set.foldr (\q (refs,f) -> first (`Set.insert` refs) $ groundRule q f) (Set.empty, Formula.empty) queries

        groundRule :: PredicateLabel -> Formula -> (Formula.NodeRef, Formula)
        groundRule label f = case Formula.labelId fLabel f of
            Just nodeId        -> (Formula.RefComposed True nodeId, f)
            _ | nChildren == 0 -> error "not implemented"
            _                  -> let (fChildren,f',_) = Set.foldr
                                        (\child (fChildren,f,counter) ->
                                            let (newChild,f') = groundBody (printf "%s%i" label counter) child f
                                            in  (Set.insert newChild fChildren, f', counter+1)
                                        )
                                        (Set.empty,f,0::Int)
                                        children
                                  in first Formula.entryRef $ Formula.insert mbLabel True Formula.Or fChildren f'
            where
                mbLabel | Set.member label queries = Nothing
                        | otherwise                = Just $ Formula.uncondNodeLabel label
                children = Map.lookupDefault (error "rule not found") label rules
                nChildren = Set.size children
                fLabel = Formula.uncondNodeLabel label

        groundBody :: PredicateLabel -> AST.RuleBody -> Formula -> (Formula.NodeRef, Formula)
        groundBody label (AST.RuleBody elements) f = case elements of
            []              -> error "not implemented"
            [singleElement] -> groundElement singleElement f
            elements        -> let (fChildren, f') = foldl
                                        (\(fChildren, f) el ->
                                            let (newChild,f') = groundElement el f
                                            in (Set.insert newChild fChildren, f')
                                        )
                                        (Set.empty, f)
                                        elements
                               in first Formula.entryRef $ Formula.insert (Just $ Formula.uncondNodeLabel label) True Formula.And fChildren f'

        groundElement :: AST.RuleBodyElement -> Formula -> (Formula.NodeRef, Formula)
        groundElement (AST.UserPredicate label)   f = (ref, f') where
            (ref, f') = groundRule label f
        groundElement (AST.BuildInPredicate pred) f = (Formula.RefBuildInPredicate pred, f)
