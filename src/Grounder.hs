--The MIT License (MIT)
--
--Copyright (c) 2016 Steffen Michels (mail@steffen-michels.de)
--
--Permission is hereby granted, free of charge, to any person obtaining a copy of
--this software and associated documentation files (the "Software"), to deal in
--the Software without restriction, including without limitation the rights to use,
--copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the
--Software, and to permit persons to whom the Software is furnished to do so,
--subject to the following conditions:
--
--The above copyright notice and this permission notice shall be included in all
--copies or substantial portions of the Software.
--
--THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
--IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
--FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
--COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
--IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
--CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

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
                fLabel = Formula.uncondComposedLabel label
                mbLabel | Set.member label queries = Right (Map.empty, Map.empty)
                        | otherwise                = Left $ Formula.uncondComposedLabel label
                bodies = Map.lookupDefault (error "rule not found") label rules
                nBodies = Set.size bodies

        groundBody :: (Eq cachedInfo, Hashable cachedInfo) => PredicateLabel -> AST.RuleBody -> FState cachedInfo Formula.NodeRef
        groundBody label (AST.RuleBody elements) = case elements of
            []              -> error "not implemented"
            [singleElement] -> groundElement singleElement
            elements -> do fChildren <- foldlM (\fChildren el -> do newChild <- groundElement el
                                                                    return $ Set.insert newChild fChildren
                                               ) Set.empty elements
                           state $ first Formula.entryRef . Formula.insert (Left $ Formula.uncondComposedLabel label) True Formula.And fChildren

        groundElement :: (Eq cachedInfo, Hashable cachedInfo) => AST.RuleBodyElement -> FState cachedInfo Formula.NodeRef
        groundElement (AST.UserPredicate label)   = groundRule label
        groundElement (AST.BuildInPredicate pred) = return $ Formula.RefBuildInPredicate pred Map.empty
