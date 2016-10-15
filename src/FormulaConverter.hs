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

module FormulaConverter ( convert
                        ) where
import GroundedAST (GroundedAST(..))
import qualified GroundedAST
import Formula (Formula)
import qualified Formula
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import Control.Monad.State.Strict
import Data.Maybe (isJust, fromMaybe, isNothing)
import Control.Arrow (second, (***))
import Data.Foldable (foldrM, foldl')
import Util

convert :: GroundedAST
        -> Formula.CacheComputations cachedInfo
        -> (([(GroundedAST.RuleBodyElement, Formula.NodeRef)], [Formula.NodeRef]), Formula cachedInfo)
convert GroundedAST{GroundedAST.queries = queries, GroundedAST.evidence = evidence, GroundedAST.rules = rules} cachedInfoComps =
    runState (do groundedQueries  <- forM (Set.toList queries)  (\q -> (\ref -> (q, ref)) <$> headFormula q Set.empty)
                 groundedEvidence <- forM (Set.toList evidence) (`headFormula` Set.empty)
                 return (groundedQueries, groundedEvidence)
             ) (Formula.empty cachedInfoComps)
    where
    headFormula :: GroundedAST.RuleBodyElement
                -> HashSet GroundedAST.PredicateLabel
                -> Formula.FState cachedInfo Formula.NodeRef
    headFormula (GroundedAST.UserPredicate label) excludedGoals = do
            mbNodeId <- Formula.labelId flabel
            case mbNodeId of
                Just nodeId -> return $ Formula.refComposed nodeId
                _ -> do
                    (fBodies,_) <- foldM (ruleFormulas label) ([], 0::Integer) $ Map.lookupDefault Set.empty label rules
                    Formula.entryRef <$> Formula.insert (Formula.WithLabel flabel) True Formula.Or fBodies
            where
            flabel    = Formula.uncondComposedLabel $ GroundedAST.setExcluded excludedGoals' label
            excludedGoals' = Set.intersection excludedGoals children
            children = Map.lookupDefault (error "not in predChildren") label predChildren

            ruleFormulas :: GroundedAST.PredicateLabel
                         -> ([Formula.NodeRef], Integer)
                         -> GroundedAST.RuleBody
                         -> Formula.FState cachedInfo ([Formula.NodeRef], Integer)
            ruleFormulas label' (fBodies, counter) body = do
                newChild <- bodyFormula (GroundedAST.setBodyNr counter label') body
                return (newChild : fBodies, succ counter)

            bodyFormula :: GroundedAST.PredicateLabel
                        -> GroundedAST.RuleBody
                        -> Formula.FState cachedInfo Formula.NodeRef
            bodyFormula label' (GroundedAST.RuleBody elements)
                | any (`Set.member` excludedGoals'') [p | GroundedAST.UserPredicate p <- Set.toList elements] = return $ Formula.refDeterministic False
                | otherwise = case length elements of
                        0 -> return $ Formula.refDeterministic True
                        1 -> headFormula (getFirst elements) excludedGoals''
                        _ -> do fChildren <- foldrM (\el fChildren -> do newChild <- headFormula el excludedGoals''
                                                                         return $ newChild : fChildren
                                                    ) [] elements
                                Formula.entryRef <$> Formula.insert (Formula.WithLabel $ Formula.uncondComposedLabel label') True Formula.And fChildren
               where
               excludedGoals''
                   | Set.member label children = Set.insert label excludedGoals'
                   | otherwise                 = excludedGoals'
    headFormula (GroundedAST.BuildInPredicate bip) _ = return $ Formula.refBuildInPredicate bip

    predChildren = fst $ execState
        (do forM_ [q | GroundedAST.UserPredicate q <- Set.toList queries]  (\q -> (\ref -> (q, ref)) <$> determinePredChildren q)
            forM_ [e | GroundedAST.UserPredicate e <- Set.toList evidence] determinePredChildren
        ) (Map.empty, Map.empty)

    determinePredChildren :: GroundedAST.PredicateLabel
                 -> State (HashMap GroundedAST.PredicateLabel (HashSet GroundedAST.PredicateLabel), HashMap GroundedAST.PredicateLabel (HashSet GroundedAST.PredicateLabel)) ()
    determinePredChildren goal = do
        alreadyKnown <- gets $ isJust . Map.lookup goal . fst
        unless alreadyKnown $ do
            children <- fst <$> determineChildren goal Set.empty
            modify' (Map.insert goal children *** Map.delete goal)
            forM_ children determinePredChildren
        where
        determineChildren :: GroundedAST.PredicateLabel
                          -> HashSet GroundedAST.PredicateLabel
                          -> State (HashMap GroundedAST.PredicateLabel (HashSet GroundedAST.PredicateLabel), HashMap GroundedAST.PredicateLabel (HashSet GroundedAST.PredicateLabel)) (HashSet GroundedAST.PredicateLabel, Bool)
        determineChildren goal' activeGoals
            | Set.member goal' activeGoals = return (Set.empty, True)
            | otherwise = do
                mbChildren <- gets $ Map.lookup goal' . fst
                case mbChildren of
                    Just children -> return (children, False)
                    Nothing -> do
                        mbCachedDirChildren <- gets $ Map.lookup goal' . snd
                        let directChildren = fromMaybe
                                (Set.unions [ Set.fromList [child | GroundedAST.UserPredicate child <- Set.toList elements]
                                                           | GroundedAST.RuleBody elements <- Set.toList $ Map.lookupDefault Set.empty goal' rules ]
                                )
                                mbCachedDirChildren
                        let activeGoals' = Set.insert goal' activeGoals
                        childrensChildren <- forM (Set.toList directChildren) (`determineChildren` activeGoals')
                        let res@(allChildren, cycl) = foldl' (\(chldrnX, cycleX) (chldrnY, cycleY) -> (Set.union chldrnX chldrnY, cycleX || cycleY)) (directChildren, False) childrensChildren
                        unless cycl $ modify' (Map.insert goal' allChildren *** Map.delete goal')
                        when   (cycl && isNothing mbCachedDirChildren) $ modify' $ second $ Map.insert goal' directChildren -- cannot determine all children, cache at least direct ones
                        return res
