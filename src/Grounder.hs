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
import AST (AST)
import qualified AST
import Formula (Formula)
import qualified Formula
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Control.Monad.State.Strict
import Control.Arrow (first, second)
import Data.Hashable (Hashable)
import Text.Printf (printf)
import Data.List (intercalate)
import Data.Foldable (foldrM)
import Data.Sequence (Seq, ViewL((:<)), (><))
import qualified Data.Sequence as Seq
import Data.Maybe (catMaybes)

type FState cachedInfo = State (Formula cachedInfo)
newtype Valuation = Valuation (HashMap AST.VarName AST.ObjectLabel)
data GroundingState = GroundingState
    { groundings  :: HashMap (AST.PredicateLabel,Int) (HashSet [AST.ObjectLabel])
    , varCount    :: Int
    , valuation   :: Valuation
    , provenGoals :: HashMap (AST.PredicateLabel,Int) (HashSet [AST.PredArgument])
    }

groundPclp :: (Eq cachedInfo, Hashable cachedInfo)
           => AST
           -> Formula.CacheComputations cachedInfo
           -> ((HashSet Formula.NodeRef, Maybe Formula.NodeRef), Formula cachedInfo)
groundPclp AST.AST {AST.queries=queries, AST.evidence=mbEvidence, AST.rules=rules} cachedInfoComps =
    runState (do groundedQueries <- foldrM (\query gQueries -> do ref <- headFormula query
                                                                  return $ Set.insert ref gQueries
                                           ) Set.empty queries'
                 case mbEvidence of
                    Nothing -> return (groundedQueries, Nothing)
                    Just ev -> do groundedEvidence <- headFormula $ second assumeAllArgsGrounded ev
                                  return (groundedQueries, Just groundedEvidence)
             ) (Formula.empty cachedInfoComps)
    where
    -- unwrap object arguments of query and evidence, assuming they are grounded
    queries'    = Set.map (second assumeAllArgsGrounded)     queries
    mbEvidence' =          second assumeAllArgsGrounded  <$> mbEvidence
    assumeAllArgsGrounded = fmap (\x -> case x of
                                     AST.Variable _    -> error "only grounded query/evidence allowed"
                                     AST.Object olabel -> olabel
                                 )

    headFormula :: (Eq cachedInfo, Hashable cachedInfo) => (AST.PredicateLabel, [AST.ObjectLabel]) -> FState cachedInfo Formula.NodeRef
    headFormula (label@(AST.PredicateLabel lStr), args) =
        do mbNodeId <- Formula.labelId labelWithArgs <$> get
           case mbNodeId of
               Just nodeId -> return $ Formula.RefComposed True nodeId
               _ -> do (fBodies,_) <- foldM (ruleFormulas label args) (Set.empty, 0::Int) headRules
                       state $ first Formula.entryRef . Formula.insert (Left labelWithArgs) True Formula.Or fBodies
        where
        labelWithArgs = Formula.uncondComposedLabel $ toPropLabel label args Nothing
        headRules     = Map.lookupDefault (error $ printf "head '%s/%i' undefined" lStr nArgs) (label, nArgs) rules
        nArgs         = length args

    ruleFormulas :: (Eq cachedInfo, Hashable cachedInfo)
                 => AST.PredicateLabel
                 -> [AST.ObjectLabel]
                 -> (HashSet Formula.NodeRef, Int)
                 -> ([AST.PredArgument], AST.RuleBody)
                 -> FState cachedInfo (HashSet Formula.NodeRef, Int)
    ruleFormulas label givenArgs (fBodies, counter) (args, body) = case completeValuation <$> matchArgs givenArgs args of
        Nothing         -> return (fBodies, counter) -- given arguments do not match definition OR domain of other vars in rule is empty, do not add anything to set of bodies
        Just valuations -> foldrM (\val (fBodies', counter') -> do newChild <- bodyFormula (toPropLabel label givenArgs $ Just counter') body val
                                                                   return (Set.insert newChild fBodies', counter' + 1)
                                  )
                                  (fBodies, counter)
                                  valuations
        where
        -- initial valuation based on matching given arguments with head definition
        matchArgs :: [AST.ObjectLabel] -> [AST.PredArgument] -> Maybe Valuation
        matchArgs givenArgs' args' = Valuation <$> foldr match (Just Map.empty) (zip givenArgs' args')
            where
            match (givenObj, AST.Object req) mbV
                | givenObj == req = mbV
                | otherwise       = Nothing
            match (givenObj, AST.Variable var) mbV = do
                v <- mbV
                case Map.lookup var v of
                    Nothing                    -> return $ Map.insert var givenObj v
                    Just obj | obj == givenObj -> return v
                    _                          -> Nothing

        -- valuations for all possible combination of values for vars not included in head valuation
        completeValuation :: Valuation -> [Valuation]
        completeValuation (Valuation valuation) = [Valuation $ Map.union valuation ibov | ibov <- inBodyOnlyValuations]
            where
            inBodyOnlyValuations = foldr updateDomains [Map.empty] bodyElements
            AST.RuleBody bodyElements = body

            updateDomains (AST.BuildInPredicate _)         doms = doms
            updateDomains (AST.UserPredicate label' args') doms = do
                valuation' <- doms
                catMaybes [ foldr (\(grArg, arg) mbVal -> do
                                      val <- mbVal
                                      case (grArg, arg) of
                                          (AST.Object objX,  objY) -> if objX == objY then return val else Nothing
                                          (AST.Variable var, objX) -> case Map.lookup var val of
                                              Nothing   -> return $ Map.insert var objX val
                                              Just objY -> if objX == objY then return val else Nothing
                                  )
                                  (Just valuation')
                                  (zip args' grArgs)
                          | grArgs <- Set.toList $ Map.lookupDefault Set.empty (label',length args') allGroundings
                          ]

    bodyFormula :: (Eq cachedInfo, Hashable cachedInfo)
                => Formula.PropPredicateLabel
                -> AST.RuleBody
                -> Valuation
                -> FState cachedInfo Formula.NodeRef
    bodyFormula label (AST.RuleBody elements) valuation = case elements of
        []              -> error "Grounder.bodyFormula: empty rule body?"
        [singleElement] -> elementFormula singleElement valuation
        elements'       -> do fChildren <- foldrM (\el fChildren -> do newChild <- elementFormula el valuation
                                                                       return $ Set.insert newChild fChildren
                                                  ) Set.empty elements'
                              state $ first Formula.entryRef . Formula.insert (Left $ Formula.uncondComposedLabel label) True Formula.And fChildren

    elementFormula :: (Eq cachedInfo, Hashable cachedInfo) => AST.RuleBodyElement -> Valuation -> FState cachedInfo Formula.NodeRef
    elementFormula (AST.UserPredicate label args) valuation = headFormula (label, applyValuation valuation <$> args)
    elementFormula (AST.BuildInPredicate prd)    _          = return $ Formula.RefBuildInPredicate prd Map.empty

    allGroundings :: HashMap (AST.PredicateLabel,Int) (HashSet [AST.ObjectLabel])
    allGroundings = groundings $ Set.foldr
                        (\(label,args) -> execState $ allGroundings' $ Seq.singleton $ AST.UserPredicate label $ fmap AST.Object args)
                        GroundingState{groundings = Map.empty, varCount = 0, valuation = Valuation Map.empty, provenGoals = Map.empty}
                        (Set.union queries'$ maybe Set.empty Set.singleton mbEvidence')
        where
        allGroundings' :: Seq AST.RuleBodyElement -> State GroundingState ()
        allGroundings' todo = case Seq.viewl todo of
            Seq.EmptyL           -> modify addGroundings
                where
                addGroundings st@GroundingState{groundings,provenGoals,valuation} = st {groundings = Map.foldrWithKey addGoundingsHead groundings provenGoals}
                    where
                    addGoundingsHead (label,nArgs) calls groundings' = foldr addGroundingsCall groundings' calls
                        where
                        addGroundingsCall args = Map.insertWith Set.union (label,nArgs) (Set.singleton $ applyValuation valuation <$> args)
            nextGoal :< todoRest -> case nextGoal of
                AST.BuildInPredicate _            -> allGroundings' todoRest
                AST.UserPredicate label@(AST.PredicateLabel lStr) givenArgs -> do
                    modify (\st -> st{provenGoals = Map.insertWith Set.union (label,nArgs) (Set.singleton givenArgs) $ provenGoals st})
                    forM_ headRules continueWithRule
                    where
                    headRules = Map.lookupDefault (error $ printf "head '%s/%i' undefined" lStr nArgs) (label, nArgs) rules
                    nArgs     = length givenArgs

                    continueWithRule (args, AST.RuleBody elements) = do
                        oldSt      <- get
                        mbElements <- foldM match (Just elements) $ zip givenArgs args
                        case mbElements of
                            Just els -> do
                                -- replace left-over (existentially quantified) vars
                                (els',_) <- foldM replaceEVars ([],Map.empty) els
                                -- continue with rest
                                allGroundings' (todoRest >< Seq.fromList els')
                                newSt <- get
                                -- recover previous state for next head rule, but keep groundings found
                                put $ oldSt {groundings = groundings newSt}
                            Nothing -> put oldSt -- recover old state

                    match :: Maybe [AST.RuleBodyElement]
                          -> (AST.PredArgument, AST.PredArgument)
                          -> State GroundingState (Maybe [AST.RuleBodyElement])
                    match Nothing _          = return Nothing
                    match (Just els) argPair = case argPair of
                        (x,              y@(AST.Variable _)) -> return $ Just $ replace x y <$> els
                        (AST.Object x,      AST.Object y)    -> return $ if x == y then Just els else Nothing
                        (AST.Variable x,    AST.Object y)    -> do
                            st <- get
                            let Valuation valu = valuation st
                            case Map.lookup x valu of
                                Just v  -> return $ if v == y then Just els else Nothing
                                Nothing -> put st{valuation = Valuation $ Map.insert x y valu} >>= \_ -> return $ Just els

                    replace x y (AST.UserPredicate label' args) = AST.UserPredicate label' $ replace' <$> args
                        where
                        replace' arg = if arg == y then x else y
                    replace _ _ bip@(AST.BuildInPredicate _) = bip

                    replaceEVars :: ([AST.RuleBodyElement], HashMap AST.VarName Int)
                                 -> AST.RuleBodyElement
                                 -> State GroundingState ([AST.RuleBodyElement], HashMap AST.VarName Int)
                    replaceEVars (els,vars2ids) bip@(AST.BuildInPredicate _)   = return (bip:els,vars2ids)
                    replaceEVars (els,vars2ids) (AST.UserPredicate label' args) = do
                        (args', vars2ids') <- foldM replaceEVars' ([],vars2ids) $ reverse args
                        return (AST.UserPredicate label' args':els, vars2ids')
                            where
                            replaceEVars' :: ([AST.PredArgument], HashMap AST.VarName Int)
                                          -> AST.PredArgument
                                          -> State GroundingState ([AST.PredArgument], HashMap AST.VarName Int)
                            replaceEVars' (args', vars2ids') obj@(AST.Object _) = return (obj:args', vars2ids')
                            replaceEVars' (args', vars2ids') (AST.Variable var) = case Map.lookup var vars2ids' of
                                Just i -> return ((AST.Variable $ AST.VarName $ show i):args', vars2ids')
                                Nothing -> do
                                    i <- state (\st -> let i = varCount st in (i, st{varCount=i+1}))
                                    return ((AST.Variable $ AST.VarName $ show i):args', Map.insert var i vars2ids')

-- turn predicate label from ordinary ones (with arguments) to propositional ones (after grounding)
toPropLabel :: AST.PredicateLabel -> [AST.ObjectLabel] -> Maybe Int -> Formula.PropPredicateLabel
toPropLabel (AST.PredicateLabel label) objs mbInt = Formula.PropPredicateLabel $ printf
    "%s(%s)%s"
    label
    (intercalate "," $ objLabelStr <$> objs)
    (maybe "" show mbInt)
    where
    objLabelStr (AST.ObjectStr str) = str
    objLabelStr (AST.ObjectInt int) = show int

applyValuation :: Valuation -> AST.PredArgument -> AST.ObjectLabel
applyValuation _               (AST.Object l)                      = l
applyValuation (Valuation val) (AST.Variable v@(AST.VarName vstr)) = Map.lookupDefault (error $ printf "Grounder.groundElement: no valuation for variable '%s'" vstr) v val
