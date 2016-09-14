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
import qualified Data.HashSet as Set
import qualified Data.HashMap.Strict as Map
import Control.Monad.State.Strict
import Data.Foldable (foldrM)
import Text.Printf (printf)
import Util

convert :: GroundedAST
        -> Formula.CacheComputations cachedInfo
        -> (([(GroundedAST.RuleBodyElement, Formula.NodeRef)], [Formula.NodeRef]), Formula cachedInfo)
convert GroundedAST{GroundedAST.queries=queries, GroundedAST.evidence=evidence, GroundedAST.rules=rules} cachedInfoComps =
    runState (do groundedQueries  <- forM (Set.toList queries)  (\q -> (\ref -> (q, ref)) <$> headFormula q)
                 groundedEvidence <- forM (Set.toList evidence) headFormula
                 return (groundedQueries, groundedEvidence)
             ) (Formula.empty cachedInfoComps)
    where
    headFormula :: GroundedAST.RuleBodyElement
                -> Formula.FState cachedInfo Formula.NodeRef
    headFormula (GroundedAST.UserPredicate label) = do
        mbNodeId <- Formula.labelId flabel
        case mbNodeId of
           Just nodeId -> return $ Formula.refComposed nodeId
           _ -> do (fBodies,_) <- foldM (ruleFormulas label) ([], 0::Integer) headRules
                   Formula.entryRef <$> Formula.insert (Left flabel) True Formula.Or fBodies
        where
        flabel    = Formula.uncondComposedLabel label
        headRules = Map.lookupDefault Set.empty label rules
    headFormula (GroundedAST.BuildInPredicate bip) = return $ Formula.refBuildInPredicate bip

    ruleFormulas :: GroundedAST.PredicateLabel
                 -> ([Formula.NodeRef], Integer)
                 -> GroundedAST.RuleBody
                 -> Formula.FState cachedInfo ([Formula.NodeRef], Integer)
    ruleFormulas (GroundedAST.PredicateLabel lbl) (fBodies, counter) body = do
        newChild <- bodyFormula (GroundedAST.PredicateLabel (printf "%s%i" lbl counter)) body
        return (newChild : fBodies, succ counter)

    bodyFormula :: GroundedAST.PredicateLabel
                -> GroundedAST.RuleBody
                -> Formula.FState cachedInfo Formula.NodeRef
    bodyFormula label (GroundedAST.RuleBody elements) = case length elements of
        0 -> return $ Formula.refDeterministic True
        1 -> headFormula $ getFirst elements
        _ -> do fChildren <- foldrM (\el fChildren -> do newChild <- headFormula el
                                                         return $ newChild : fChildren
                                    ) [] elements
                Formula.entryRef <$> Formula.insert (Left $ Formula.uncondComposedLabel label) True Formula.And fChildren
