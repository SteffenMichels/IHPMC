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

{-# LANGUAGE Strict #-}

module FormulaConverter ( convert
                        ) where
import GroundedAST (GroundedAST(..))
import qualified GroundedAST
import Formula (Formula)
import qualified Formula
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import qualified Data.HashMap.Strict as Map
import Data.Hashable (Hashable)
import Control.Monad.State.Strict
import Data.Foldable (foldrM)
import Text.Printf (printf)

convert :: (Eq cachedInfo, Hashable cachedInfo)
        => GroundedAST
        -> Formula.CacheComputations cachedInfo
        -> ((HashSet Formula.NodeRef, Maybe Formula.NodeRef), Formula cachedInfo)
convert GroundedAST{GroundedAST.queries=queries, GroundedAST.evidence=mbEvidence, GroundedAST.rules=rules} cachedInfoComps =
    runState (do groundedQueries <- foldrM (\query gQueries -> do ref <- headFormula query
                                                                  return $ Set.insert ref gQueries
                                           ) Set.empty queries
                 case mbEvidence of
                    Nothing -> return (groundedQueries, Nothing)
                    Just ev -> do groundedEvidence <- headFormula ev
                                  return (groundedQueries, Just groundedEvidence)
             ) (Formula.empty cachedInfoComps)
    where
    headFormula :: (Eq cachedInfo, Hashable cachedInfo)
                => GroundedAST.PredicateLabel
                -> Formula.FState cachedInfo Formula.NodeRef
    headFormula label = do
        mbNodeId <- Formula.labelId flabel
        case mbNodeId of
           Just nodeId -> return $ Formula.RefComposed True nodeId
           _ -> do (fBodies,_) <- foldM (ruleFormulas label) (Set.empty, 0::Integer) headRules
                   Formula.entryRef <$> Formula.insert (Left flabel) True Formula.Or fBodies
        where
        flabel    = Formula.uncondComposedLabel label
        headRules = Map.lookupDefault (error $ printf "FormulaConverter: head '%s' undefined" (show label)) label rules

    ruleFormulas :: (Eq cachedInfo, Hashable cachedInfo)
                 => GroundedAST.PredicateLabel
                 -> (HashSet Formula.NodeRef, Integer)
                 -> GroundedAST.RuleBody
                 -> Formula.FState cachedInfo (HashSet Formula.NodeRef, Integer)
    ruleFormulas (GroundedAST.PredicateLabel lbl) (fBodies, counter) body = do
        newChild <- bodyFormula (GroundedAST.PredicateLabel (printf "%s%i" lbl counter)) body
        return (Set.insert newChild fBodies, succ counter)

    bodyFormula :: (Eq cachedInfo, Hashable cachedInfo)
                => GroundedAST.PredicateLabel
                -> GroundedAST.RuleBody
                -> Formula.FState cachedInfo Formula.NodeRef
    bodyFormula label (GroundedAST.RuleBody elements) = case elements of
        []              -> error "FormulaConverter.bodyFormula: empty rule body?"
        [singleElement] -> elementFormula singleElement
        elements'       -> do fChildren <- foldrM (\el fChildren -> do newChild <- elementFormula el
                                                                       return $ Set.insert newChild fChildren
                                                  ) Set.empty elements'
                              Formula.entryRef <$> Formula.insert (Left $ Formula.uncondComposedLabel label) True Formula.And fChildren

    elementFormula :: (Eq cachedInfo, Hashable cachedInfo) => GroundedAST.RuleBodyElement -> Formula.FState cachedInfo Formula.NodeRef
    elementFormula (GroundedAST.UserPredicate label)  = headFormula label
    elementFormula (GroundedAST.BuildInPredicate prd) = return $ Formula.refBuildInPredicate prd
