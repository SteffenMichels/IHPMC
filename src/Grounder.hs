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
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Data.Foldable (foldlM)
--import Text.Printf (printf)
import Control.Monad.State.Strict
import Control.Arrow (first, second)
import Data.Hashable (Hashable)
import Text.Printf (printf)
import Data.List (intercalate)

type FState cachedInfo = State (Formula cachedInfo)
type Valuation = HashMap AST.VarName AST.ObjectLabel

groundPclp :: (Eq cachedInfo, Hashable cachedInfo) => AST -> Formula.CacheComputations cachedInfo -> ((HashSet Formula.NodeRef, Maybe Formula.NodeRef), Formula cachedInfo)
groundPclp AST.AST {AST.queries=queries, AST.evidence=mbEvidence, AST.rules=rules} cachedInfoComps =
    runState (do groundedQueries <- foldlM (\gQueries query -> do ref <- groundHead $ second assumeAllArgsGrounded query
                                                                  return $ Set.insert ref gQueries
                                           ) Set.empty queries
                 case mbEvidence of
                    Nothing -> return (groundedQueries, Nothing)
                    Just ev -> do groundedEvidence <- groundHead $ second assumeAllArgsGrounded ev
                                  return (groundedQueries, Just groundedEvidence)
             ) (Formula.empty cachedInfoComps)
    where
        assumeAllArgsGrounded = fmap (\x -> case x of
                                         AST.Variable _         -> error "only grounded query/evidence allowed"
                                         AST.ObjectLabel olabel -> olabel
                                     )

        groundHead :: (Eq cachedInfo, Hashable cachedInfo) => (PredicateLabel, [AST.ObjectLabel]) -> FState cachedInfo Formula.NodeRef
        groundHead (label, args) =
            do mbNodeId <- Formula.labelId labelWithArgs <$> get
               case mbNodeId of
                   Just nodeId -> return $ Formula.RefComposed True nodeId
                   _ -> do (fBodies,_) <- foldM (groundRule label args) (Set.empty, 0::Int) bodies
                           state $ first Formula.entryRef . Formula.insert (Left labelWithArgs) True Formula.Or fBodies
            where
                labelWithArgs = Formula.uncondComposedLabel $ predWithArgs label args
                bodies = Map.lookupDefault (error $ printf "head '%s' undefined" label) label rules

        groundRule :: (Eq cachedInfo, Hashable cachedInfo) => PredicateLabel -> [AST.ObjectLabel] -> (HashSet Formula.NodeRef, Int) -> ([AST.PredArgument], AST.RuleBody) -> FState cachedInfo (HashSet Formula.NodeRef, Int)
        groundRule label givenArgs (fBodies,counter) (args, body) = case mbValuation of
            Nothing -> return (fBodies,counter) -- given arguments do not match definition, do not add anything to set of bodies
            Just valuation -> do newChild <- groundBody (printf "%s%i" (predWithArgs label givenArgs) counter) body valuation
                                 return (Set.insert newChild fBodies, counter+1)
            where
                mbValuation
                    | length givenArgs /= length args = Nothing
                    | otherwise = foldr match (Just Map.empty) $ zip givenArgs args
                        where
                            match (givenObj, AST.ObjectLabel req) mbV
                                | givenObj == req = mbV
                                | otherwise       = Nothing
                            match (givenObj, AST.Variable var) mbV = do
                                v <- mbV
                                case Map.lookup var v of
                                    Nothing                    -> return $ Map.insert var givenObj v
                                    Just obj | obj == givenObj -> return v
                                    _                          -> Nothing

        groundBody :: (Eq cachedInfo, Hashable cachedInfo) => PredicateLabel -> AST.RuleBody -> Valuation -> FState cachedInfo Formula.NodeRef
        groundBody label (AST.RuleBody elements) valuation = case elements of
            []              -> error "Grounder.groundBody: empty rule body?"
            [singleElement] -> groundElement singleElement valuation
            elements -> do fChildren <- foldlM (\fChildren el -> do newChild <- groundElement el valuation
                                                                    return $ Set.insert newChild fChildren
                                               ) Set.empty elements
                           state $ first Formula.entryRef . Formula.insert (Left $ Formula.uncondComposedLabel label) True Formula.And fChildren

        groundElement :: (Eq cachedInfo, Hashable cachedInfo) => AST.RuleBodyElement -> Valuation -> FState cachedInfo Formula.NodeRef
        groundElement (AST.UserPredicate label args) valuation = groundHead (label, applyValuation valuation <$> args) where
            applyValuation _   (AST.ObjectLabel l) = l
            applyValuation val (AST.Variable v)    = Map.lookupDefault (error "Grounder.groundElement: no valuation for variable") v valuation
        groundElement (AST.BuildInPredicate pred)    _         = return $ Formula.RefBuildInPredicate pred Map.empty

        predWithArgs :: PredicateLabel -> [AST.ObjectLabel] -> String
        predWithArgs label objs = printf "%s(%s)" label $ intercalate "," objs

