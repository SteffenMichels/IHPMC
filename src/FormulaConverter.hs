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
import Data.Maybe (isJust)
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
                    (fBodies,_) <- foldM ruleFormulas ([], 0::Int) $ Map.lookupDefault Set.empty label rules
                    Formula.entryRef <$> Formula.insert flabel True Formula.Or fBodies
            where
            flabel    = Formula.uncondComposedLabelExcluded label excludedGoals'
            excludedGoals' = Set.intersection excludedGoals children
            children = Map.lookupDefault (error "not in predChildren") label predChildren

            ruleFormulas :: ([Formula.NodeRef], Int)
                         -> GroundedAST.RuleBody
                         -> Formula.FState cachedInfo ([Formula.NodeRef], Int)
            ruleFormulas (fBodies, counter) body = do
                newChild <- bodyFormula counter body
                return (newChild : fBodies, succ counter)

            bodyFormula :: Int
                        -> GroundedAST.RuleBody
                        -> Formula.FState cachedInfo Formula.NodeRef
            bodyFormula counter (GroundedAST.RuleBody elements)
                | any (`Set.member` excludedGoals'') [p | GroundedAST.UserPredicate p <- Set.toList elements] = return $ Formula.refDeterministic False
                | otherwise = case length elements of
                        0 -> return $ Formula.refDeterministic True
                        1 -> headFormula (getFirst elements) excludedGoals''
                        _ -> do fChildren <- foldrM (\el fChildren -> do newChild <- headFormula el excludedGoals''
                                                                         return $ newChild : fChildren
                                                    ) [] elements
                                Formula.entryRef <$> Formula.insert (Formula.uncondComposedLabelNr label counter) True Formula.And fChildren
               where
               excludedGoals''
                   | Set.member label children = Set.insert label excludedGoals'
                   | otherwise                 = excludedGoals'
    headFormula (GroundedAST.BuildInPredicate bip) _ = return $ Formula.refBuildInPredicate bip

    predChildren = execState
        (do forM_ [q | GroundedAST.UserPredicate q <- Set.toList queries]  (\q -> (\ref -> (q, ref)) <$> determinePredChildren q)
            forM_ [e | GroundedAST.UserPredicate e <- Set.toList evidence] determinePredChildren
        ) Map.empty

    -- determins pred children for each query/evidence
    determinePredChildren :: GroundedAST.PredicateLabel
                          -> State (HashMap GroundedAST.PredicateLabel (HashSet GroundedAST.PredicateLabel)) ()
    determinePredChildren goal = do
        alreadyKnown <- get
        let childrAndDeps = childrAndDependencies goal alreadyKnown
        fillInDependencies goal childrAndDeps

    childrAndDependencies :: GroundedAST.PredicateLabel
                          -> HashMap GroundedAST.PredicateLabel (HashSet GroundedAST.PredicateLabel)
                          -> HashMap GroundedAST.PredicateLabel (HashSet GroundedAST.PredicateLabel, HashSet GroundedAST.PredicateLabel)
    childrAndDependencies goal pChildren = execState (determineChildrAndDeps goal Set.empty) Map.empty
        where
        determineChildrAndDeps :: GroundedAST.PredicateLabel
                               -> HashSet GroundedAST.PredicateLabel
                               -> State
                                      (HashMap GroundedAST.PredicateLabel (HashSet GroundedAST.PredicateLabel, HashSet GroundedAST.PredicateLabel))
                                      (HashSet GroundedAST.PredicateLabel)
        determineChildrAndDeps goal' activeGoals = case Map.lookup goal' pChildren of
            Just children -> return children
            Nothing -> do
                childrAndDeps <- get
                case Map.lookup goal' childrAndDeps of
                    Just (children, _) -> return children
                    Nothing -> do
                        curChildrAndDeps <- foldM
                            ( \(children, deps) child -> do
                                let children' = Set.insert child children
                                if   Set.member child activeGoals
                                then return (children', Set.insert child deps)
                                else do
                                    childChildren <- determineChildrAndDeps child $ Set.insert goal' activeGoals
                                    return (Set.union childChildren children', deps)
                            )
                            (Set.empty, Set.empty)
                            (directChildren goal')
                        modify' $ Map.insert goal' curChildrAndDeps
                        return $ fst curChildrAndDeps

    fillInDependencies :: GroundedAST.PredicateLabel
                       -> HashMap GroundedAST.PredicateLabel (HashSet GroundedAST.PredicateLabel, HashSet GroundedAST.PredicateLabel)
                       -> State (HashMap GroundedAST.PredicateLabel (HashSet GroundedAST.PredicateLabel)) ()
    fillInDependencies goal childrAndDeps = do
        pChildren <- get
        unless (isJust $ Map.lookup goal pChildren) $ do
            let (childr, deps) = Map.lookupDefault undefined goal childrAndDeps
            let childr'        = foldl' (\c dep -> Set.union c $ Map.lookupDefault undefined dep pChildren) childr deps
            put $ Map.insert goal childr' pChildren
            forM_ (directChildren goal) (`fillInDependencies` childrAndDeps)
            return ()
        return ()

    directChildren :: GroundedAST.PredicateLabel -> HashSet GroundedAST.PredicateLabel
    directChildren goal = Set.unions [ Set.fromList [child | GroundedAST.UserPredicate child <- Set.toList elements]
                                     | GroundedAST.RuleBody elements <- Set.toList $ Map.lookupDefault Set.empty goal rules ]
