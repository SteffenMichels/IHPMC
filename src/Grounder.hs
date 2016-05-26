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
import BasicTypes
import AST (AST)
import qualified AST
import Formula (Formula)
import qualified Formula
import qualified Data.HashMap.Lazy as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Data.Foldable (foldlM)
import Text.Printf (printf)
import Control.Monad.State.Strict
import Control.Arrow (first)
import Data.Hashable (Hashable)

type FState cachedInfo = State (Formula cachedInfo)

groundPclp :: (Eq cachedInfo, Hashable cachedInfo) => AST -> Formula.CacheComputations cachedInfo -> ((HashSet Formula.NodeRef, Maybe Formula.NodeRef), Formula cachedInfo)
groundPclp AST.AST {AST.queries=queries, AST.evidence=mbEvidence, AST.rules=rules} cachedInfoComps =
    runState (do groundedQueries <- foldlM (\gQueries query -> do ref <- groundRule query
                                                                  return $ Set.insert ref gQueries
                                           ) Set.empty queries
                 case mbEvidence of
                    Nothing -> return (groundedQueries, Nothing)
                    Just ev -> do groundedEvidence <- groundRule ev
                                  return (groundedQueries, Just groundedEvidence)
             ) (Formula.empty cachedInfoComps)
    where
        groundRule :: (Eq cachedInfo, Hashable cachedInfo) => PredicateLabel -> FState cachedInfo Formula.NodeRef
        groundRule label =
            do mbNodeId <- Formula.labelId fLabel <$> get
               case mbNodeId of
                   Just nodeId      -> return $ Formula.RefComposed True nodeId
                   _ | nBodies == 0 -> error "not implemented"
                   _ -> do (fBodies,_) <- foldM (\(fBodies,counter) body -> do newChild <- groundBody (printf "%s%i" label counter) body
                                                                               return (Set.insert newChild fBodies, counter+1)
                                                ) (Set.empty, 0::Int) bodies
                           state $ first Formula.entryRef . Formula.insert mbLabel True Formula.Or fBodies
            where
                fLabel = Formula.uncondNodeLabel label
                mbLabel | Set.member label queries = Nothing
                        | otherwise                = Just $ Formula.uncondNodeLabel label
                bodies = Map.lookupDefault (error "rule not found") label rules
                nBodies = Set.size bodies

        groundBody :: (Eq cachedInfo, Hashable cachedInfo) => PredicateLabel -> AST.RuleBody -> FState cachedInfo Formula.NodeRef
        groundBody label (AST.RuleBody elements) = case elements of
            []              -> error "not implemented"
            [singleElement] -> groundElement singleElement
            elements -> do fChildren <- foldlM (\fChildren el -> do newChild <- groundElement el
                                                                    return $ Set.insert newChild fChildren
                                               ) Set.empty elements
                           state $ first Formula.entryRef . Formula.insert (Just $ Formula.uncondNodeLabel label) True Formula.And fChildren

        groundElement :: (Eq cachedInfo, Hashable cachedInfo) => AST.RuleBodyElement -> FState cachedInfo Formula.NodeRef
        groundElement (AST.UserPredicate label)   = groundRule label
        groundElement (AST.BuildInPredicate pred) = return $ Formula.RefBuildInPredicate pred Map.empty
