--The MIT License (MIT)
--
--Copyright (c) 2016-2017 Steffen Michels (mail@steffen-michels.de)
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

{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE Strict #-}
#endif

module KnowledgeBaseConverter
    ( convert
    ) where
import GroundedAST (GroundedAST(..), GroundedASTPhase2)
import qualified GroundedAST
import qualified KnowledgeBase as KB
import Data.HashSet (Set)
import qualified Data.HashSet as Set
import Data.HashMap (Map)
import qualified Data.HashMap as Map
import Control.Monad.State.Strict
import Data.Maybe (isJust)
import Data.Foldable (foldlM)
import Util
import IdNrMap (IdNrMap)
import qualified IdNrMap

type CState s cachedInfo = StateT (IdNrMap KB.PredicateLabel) (KB.KBState cachedInfo)
type RuleBodyElement = GroundedAST.RuleBodyElementPhase2
type RuleBody = GroundedAST.RuleBodyPhase2

convert :: GroundedASTPhase2
        -> KB.KBState cachedInfo (([(RuleBodyElement, KB.NodeRef cachedInfo)], [KB.NodeRef cachedInfo]), IdNrMap KB.PredicateLabel)
convert GroundedAST{GroundedAST.queries = queries, GroundedAST.evidence = evidence, GroundedAST.rules = rules} = runStateT
    ( do groundedQueries  <- forM (Set.toList queries)  (\q -> (\entry -> (q, KB.entryRef entry)) <$> headFormula q Set.empty)
         groundedEvidence <- forM (Set.toList evidence) (\e -> KB.entryRef <$> headFormula e Set.empty)
         return (groundedQueries, groundedEvidence)
    )
    IdNrMap.empty
    where
    headFormula :: RuleBodyElement
                -> Set GroundedAST.PredicateLabel
                -> CState s cachedInfo (KB.RefWithNode cachedInfo)
    headFormula (GroundedAST.UserPredicate label) excludedGoals = do
            flabel <- KB.uncondComposedLabel . KB.PredicateId <$> state (IdNrMap.getIdNr plabel)
            mbNodeId <- lift $ KB.labelId flabel
            case mbNodeId of
                Just nodeId -> do
                    let nodeRef = KB.refComposed nodeId
                    lift $ KB.augmentWithEntryRef nodeRef
                _ -> do
                    (fBodies,_) <- foldM ruleFormulas ([], 0::Int) $ Set.toList $ Map.findWithDefault Set.empty label rules
                    lift $ KB.insert flabel True KB.Or fBodies
            where
            plabel         = KB.PredicateLabel label excludedGoals' Nothing
            excludedGoals' = Set.intersection excludedGoals children
            children       = Map.findWithDefault (error "not in predChildren") label predChildren

            ruleFormulas :: ([KB.RefWithNode cachedInfo], Int)
                         -> RuleBody
                         -> CState s cachedInfo ([KB.RefWithNode cachedInfo], Int)
            ruleFormulas (fBodies, counter) body = do
                newChild <- bodyFormula counter body
                return (newChild : fBodies, succ counter)

            bodyFormula :: Int
                        -> RuleBody
                        -> CState s cachedInfo (KB.RefWithNode cachedInfo)
            bodyFormula counter (GroundedAST.RuleBody elements)
                | any (`Set.member` excludedGoals'') [p | GroundedAST.UserPredicate p <- Set.toList elements] =
                    lift $ KB.augmentWithEntry $ KB.refDeterministic False
                | otherwise = case Set.size elements of
                        0 -> lift $ KB.augmentWithEntry $ KB.refDeterministic True
                        1 -> headFormula (getFirst elements) excludedGoals''
                        _ -> do
                            fChildren <- foldlM (\fChildren el -> do newChild <- headFormula el excludedGoals''
                                                                     return $! newChild : fChildren
                                                ) [] $ Set.toList elements
                            let plabel' = KB.PredicateLabel label excludedGoals' (Just counter)
                            flabel <- KB.uncondComposedLabel . KB.PredicateId <$> state (IdNrMap.getIdNr plabel')
                            lift $ KB.insert flabel True KB.And fChildren
               where
               excludedGoals''
                   | Set.member label children = Set.insert label excludedGoals'
                   | otherwise                 = excludedGoals'
    headFormula (GroundedAST.BuildInPredicate bip) _ = lift $ KB.augmentWithEntry $ KB.refBuildInPredicate bip

    predChildren = execState
        (do forM_ [q | GroundedAST.UserPredicate q <- Set.toList queries]  (\q -> (\ref -> (q, ref)) <$> determinePredChildren q)
            forM_ [e | GroundedAST.UserPredicate e <- Set.toList evidence] determinePredChildren
        ) Map.empty

    -- determins pred children for each query/evidence
    determinePredChildren :: GroundedAST.PredicateLabel
                          -> State (Map GroundedAST.PredicateLabel (Set GroundedAST.PredicateLabel)) ()
    determinePredChildren goal = do
        alreadyKnown <- get
        let childrAndDeps = childrAndDependencies goal alreadyKnown
        fillInDependencies goal childrAndDeps

    childrAndDependencies :: GroundedAST.PredicateLabel
                          -> Map GroundedAST.PredicateLabel (Set GroundedAST.PredicateLabel)
                          -> Map GroundedAST.PredicateLabel (Set GroundedAST.PredicateLabel, Set GroundedAST.PredicateLabel)
    childrAndDependencies goal pChildren = execState (determineChildrAndDeps goal Set.empty) Map.empty
        where
        determineChildrAndDeps :: GroundedAST.PredicateLabel
                               -> Set GroundedAST.PredicateLabel
                               -> State
                                      (Map GroundedAST.PredicateLabel (Set GroundedAST.PredicateLabel, Set GroundedAST.PredicateLabel))
                                      (Set GroundedAST.PredicateLabel)
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
                            (Set.toList $ directChildren goal')
                        modify' $ Map.insert goal' curChildrAndDeps
                        return $ fst curChildrAndDeps

    fillInDependencies :: GroundedAST.PredicateLabel
                       -> Map GroundedAST.PredicateLabel (Set GroundedAST.PredicateLabel, Set GroundedAST.PredicateLabel)
                       -> State (Map GroundedAST.PredicateLabel (Set GroundedAST.PredicateLabel)) ()
    fillInDependencies goal childrAndDeps = do
        pChildren <- get
        unless (isJust $ Map.lookup goal pChildren) $ do
            let (childr, deps) = Map.findWithDefault undefined goal childrAndDeps
            let childr'        = Set.fold (\dep c -> Set.union c $ Map.findWithDefault undefined dep pChildren) childr deps
            put $ Map.insert goal childr' pChildren
            forM_ (Set.toList $ directChildren goal) (`fillInDependencies` childrAndDeps)
            return ()
        return ()

    directChildren :: GroundedAST.PredicateLabel -> Set GroundedAST.PredicateLabel
    directChildren goal = Set.unions [ Set.fromList [child | GroundedAST.UserPredicate child <- Set.toList elements]
                                     | GroundedAST.RuleBody elements <- Set.toList $ Map.findWithDefault Set.empty goal rules ]

