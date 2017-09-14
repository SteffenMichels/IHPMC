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

module Grounder
    ( ground
    , Exception(..)
    , exceptionToText
    ) where
import AST (AST)
import qualified AST
import GroundedAST (GroundedAST(..))
import qualified GroundedAST
import Data.HashMap (Map)
import qualified Data.HashMap as Map
import Data.HashSet (Set)
import qualified Data.HashSet as Set
import qualified Data.Set as PQ -- set used as PQ here
import Control.Monad.State.Strict
import Data.Foldable (foldl', foldlM)
import Data.Maybe (isJust, catMaybes)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Control.Monad.Trans.Maybe (MaybeT, runMaybeT)
import Exception
import Util
import Data.Boolean (Boolean(..))
import IdNrMap (IdNrMap)
import qualified IdNrMap
import Data.Text (Text)
import Data.Monoid ((<>))
import TextShow

type PQ        = PQ.Set
type GState    = StateT GroundingState (Exceptional Exception)
data GoalDepth = Depth Integer | Infinite deriving Eq -- infininte = goal with cycle

instance Ord GoalDepth where
    _        <= Infinite = True
    Infinite <= _        = False
    Depth x  <= Depth y  = x <= y

data Exception = NonGroundPreds        [AST.RuleBodyElement] AST.PredicateLabel Int
               | NonGroundPfDef        AST.PFuncDef AST.PFuncLabel Int
               | TypeError             PropExprWithType PropExprWithType
               | UndefinedPf           AST.PFuncLabel Int
               | UndefinedPfValue      AST.PFuncLabel [AST.ConstantExpr]
               | UndefinedPred         AST.PredicateLabel Int
               | ProbabilisticFuncUsedAsArg
               | UnsolvableConstraints [Constraint]
               | NonGroundQuery        AST.RuleBodyElement
               | NonGroundEvidence     AST.RuleBodyElement
               | DefArgShouldBeObjPf   GroundedAST.PFuncLabel PropExprWithType

exceptionToText :: Exception -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder
exceptionToText (NonGroundPreds prds headLabel headNArgs) ids2str _ =
    "Could not ground predicate" <>
    (if length prds > 1 then "s " else " ") <>
    toTextLstEnc "'" "'" prds (`AST.ruleBodyElementToText` ids2str) <>
    " in a body of '" <>
    AST.predicateLabelToText headLabel ids2str <>
    "/" <>
    showb headNArgs <>
    "'."
exceptionToText (NonGroundPfDef def pfLabel pfNArgs) ids2str _ =
    "Could not ground probabilistic function definition '" <>
    AST.pFuncDefToText def ids2str <>
    "', which is a definition of '" <>
    AST.pFuncLabelToText pfLabel ids2str <>
    "/" <>
    showb pfNArgs <>
    "'."
exceptionToText (TypeError exprX exprY) ids2str ids2label =
    "Types of expressions " <>
    propExprWithTypeToText exprX ids2str ids2label <>
    " and " <>
    propExprWithTypeToText exprY ids2str ids2label <>
    " do not match."
exceptionToText (UndefinedPf pf n) ids2str _ =
    "Probabilistic function '" <>
    AST.pFuncLabelToText pf ids2str <>
    "/" <>
    showb n <>
    "' is undefined."
exceptionToText (UndefinedPfValue pf args) ids2str _ =
    "'" <>
    AST.pFuncLabelToText pf ids2str <>
    "(" <>  showbLst args <> ")" <>
    "' is undefined."
exceptionToText (UndefinedPred label n) ids2str _ =
    "Predicate '" <>
    AST.predicateLabelToText label ids2str <>
    "/" <>
    showb n <>
    "' is undefined."
exceptionToText ProbabilisticFuncUsedAsArg _ _=
    "Probabilistic functions may not be used in arguments of predicates and functions."
exceptionToText (UnsolvableConstraints constrs) ids2str _ =
    "Could not solve constraint" <> (if length constrs > 1 then "s" else "") <>
    toTextLstEnc "'" "'" constrs (`constraintToText` ids2str) <>
    "."
exceptionToText (NonGroundQuery q) ids2str _ =
    "All queries have to be ground. Query '" <>
    AST.ruleBodyElementToText q ids2str <>
    "' is not ground."
exceptionToText (NonGroundEvidence e) ids2str _ =
    "All evidence has to be ground. Evidence '" <>
    AST.ruleBodyElementToText e ids2str <>
    "' is not ground."
exceptionToText (DefArgShouldBeObjPf pf arg) ids2str ids2label =
    "Argument '" <>
    propExprWithTypeToText arg ids2str ids2label <>
    "' of definition of random function '" <>
    GroundedAST.pFuncLabelToText pf ids2str ids2label <>
    "' should be a random function of type 'Object'."

data Constraint = EqConstraint AST.Expr AST.Expr deriving (Eq, Generic, Ord)
constraintToText :: Constraint -> Map Int Text -> Builder
constraintToText (EqConstraint exprX exprY) ids2str = AST.exprToText exprX ids2str <> " = " <> AST.exprToText exprY ids2str
instance Hashable Constraint

data GroundingState = GroundingState
    { groundedRules     :: Map GroundedAST.PredicateLabel [GroundedAST.RuleBody]
    , groundedRfDefs    :: Map GroundedAST.PFuncLabel AST.PFuncDef
    , varCounter        :: Int
    -- keep non-ground rule body elements and ground elements as soon as all vars have a value
    , rulesInProof      :: Map (AST.PredicateLabel, Int) [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody, Set GoalId)]
    -- rules for which is it unknown whether they had to be selected for the proof
    -- as soon as it is known that the rule should not have been selected, all children are pruned
    , rulesMaybeInProof :: [RuleMaybeInProof]
    , proofConstraints  :: Set Constraint
    , nextId            :: GoalId
    , labelIdentifiers  :: IdNrMap (Int, [AST.ConstantExpr])
    }

data RuleMaybeInProof = RuleMaybeInProof
    { goalId        :: GoalId
    , label         :: AST.PredicateLabel
    , args          :: [AST.Expr]
    , nonGroundBody :: AST.RuleBody
    , groundBody    :: GroundedAST.RuleBody
    , ruleParents   :: Set GoalId
    }

newtype GoalId = GoalId Int deriving (Eq, Generic, Ord)
instance Hashable GoalId

-- | Converts an AST go a grounded AST.
-- Additionally, produces ID numbers for each constant expression, ocurring in the grounding.
ground :: AST -> Exceptional Exception (GroundedAST, IdNrMap (Int, [AST.ConstantExpr]))
ground ast = evalStateT
    (do
        (queries', evidence') <- computeResultState
        gRules <- gets groundedRules
        pIds   <- gets labelIdentifiers
        return ( GroundedAST { rules    = Map.map Set.fromList gRules
                             , queries  = queries'
                             , evidence = evidence'
                             }
               , pIds
               )
    )
    GroundingState{ groundedRules     = Map.empty
                  , groundedRfDefs    = Map.empty
                  , varCounter        = 0
                  , rulesInProof      = Map.empty
                  , rulesMaybeInProof = []
                  , proofConstraints  = Set.empty
                  , nextId            = GoalId 0
                  , labelIdentifiers  = IdNrMap.empty
                  }
    where
    AST.AST{AST.queries=queries, AST.evidence=evidence, AST.rules=rules, AST.pFuncDefs=pfDefs} = ast

    -- | Computes a state which contains all ground rules.
    -- Returns all queries and evidence as grounded elements.
    computeResultState :: GState (Set GroundedAST.RuleBodyElement, Set GroundedAST.RuleBodyElement)
    computeResultState = do
        queries'  <- forM queries  $ toPropQueryEvidence NonGroundQuery
        evidence' <- forM evidence $ toPropQueryEvidence NonGroundEvidence
        forM_ (queries ++ evidence) $
            \el -> computeGroundings $ PQ.singleton (goalDepth el, el, Set.empty)
        return (Set.fromList queries', Set.fromList evidence')
            where
            -- | Converts query or evidence elements into grounded elements.
            toPropQueryEvidence :: (AST.RuleBodyElement -> Exception) -- the exception in case the element is not ground
                                -> AST.RuleBodyElement                -- query/evidence which should be ground
                                -> GState GroundedAST.RuleBodyElement
            toPropQueryEvidence exception x
                | AST.varsInRuleBodyElement x = lift $ throw $ exception x
                | otherwise                   = toPropRuleElement x pfDefs

    -- | Computes all groundings given a current sequence of goal to still prove,
    -- together with for each goal a set of parent IDs, used for pruning proofs.
    computeGroundings :: PQ (GoalDepth, AST.RuleBodyElement, Set GoalId) -> GState ()
    computeGroundings todo = computeGroundings' todo [] Nothing
        where
        computeGroundings' :: PQ (GoalDepth, AST.RuleBodyElement, Set GoalId)
                           -> [(GoalDepth, AST.RuleBodyElement, Set GoalId)]
                           -> Maybe ((AST.RuleBodyElement, Set GoalId), PQ (GoalDepth, AST.RuleBodyElement, Set GoalId))
                           -> GState ()
        computeGroundings' todo' maybeTodo mbFirstMaybeTodo = case PQ.minView todo' of
            Nothing -> case mbFirstMaybeTodo of
                -- no goal left -> proof finished
                Nothing -> addGroundings
                -- we have to continue with goal of which we do not know yet whether it has to be proven
                Just (goal, todo'') -> computeGroundingsGoal goal True todo''
            Just (goalWithD@(_, goal, parents), todo'') -> do
                alreadyP <- alreadyProven goal
                inCurP   <- inCurProof    goal
                case alreadyP ||* inCurP of
                    -- filter goal which does not have to be proven any more
                    True3 -> computeGroundings' todo'' maybeTodo mbFirstMaybeTodo
                    -- continue with proving goal
                    False3 -> computeGroundingsGoal (goal, parents) False $ foldl' (\td (d, g, p) -> PQ.insert (d, g, p) td) todo'' maybeTodo
                    -- we don't know yet whether we have to proof this goal -> postpone
                    Unknown3 -> computeGroundings' todo'' (goalWithD : maybeTodo) $ case mbFirstMaybeTodo of
                        Nothing -> Just ((goal, parents), todo'')
                        _       -> mbFirstMaybeTodo

    -- | Continues computing groundings with the goal given.
    computeGroundingsGoal :: (AST.RuleBodyElement, Set GoalId)               -- the goal to continue with & set of parent IDs
                          -> Bool                                            -- is it not known whether we still have to prove the goal yet?
                          -> PQ (GoalDepth, AST.RuleBodyElement, Set GoalId) -- the remaining goals to prove
                          -> GState ()
    computeGroundingsGoal (goal, parents) maybeGoal remaining = case goal of
        AST.UserPredicate label givenArgs -> case Map.lookup (label, nArgs) rules of
            Just headRules -> forM_ headRules continueWithChosenRule
            Nothing        -> lift $ throw $ UndefinedPred label nArgs
            where
            nArgs = length givenArgs

            -- | Continues computing groundings with the rule given.
            continueWithChosenRule :: ([AST.HeadArgument], AST.RuleBody) -> GState ()
            continueWithChosenRule (args, AST.RuleBody elements) = do
                oldSt <- get
                mbResult <- lift $ runMaybeT $ applyArgs givenArgs args elements
                case mbResult of
                    -- successfully matched given with required rule arguments
                    Just (els, valu, constrs) -> do
                        -- replace left-over (existentially quantified) vars
                        els' <- doState $ replaceEVars els
                        parents' <- doState $ if maybeGoal then do
                                        -- add the goal to 'maybe proofs', add goal Id to set of parents for next goals,
                                        -- such that the goal can be pruned if it was not required to be proven
                                        goalId <- addRuleToMaybeProof els' parents
                                        return $ Set.insert goalId parents
                                    else do
                                        addRuleToProof els'
                                        return parents
                        -- add newly found constraints to state
                        modify' (\st -> st{proofConstraints = Set.union constrs $ proofConstraints st})
                        -- apply newly found variable values and check if proof is still consistent
                        consistent <- applyValuation valu pfDefs
                        mbToPrune  <- applyValuationMaybeInProof valu pfDefs
                        case (consistent, mbToPrune) of
                            -- valuation is consistent with proofs (and maybe proofs)
                            (True, Just toPrune) -> do
                                let remaining' = PQ.filter (\(_, _, parents'') -> Set.null $ Set.intersection toPrune parents'') remaining
                                modify' ( \st ->
                                            let rip   = Map.filter (not . null) $
                                                    filter (\(_, _, _, ruleParents) -> Set.null $ Set.intersection toPrune ruleParents) <$>
                                                    rulesInProof st
                                                rmbip = filter
                                                    (\RuleMaybeInProof{ruleParents} -> Set.null $ Set.intersection toPrune ruleParents)
                                                    (rulesMaybeInProof st)
                                            in st{rulesInProof = rip, rulesMaybeInProof = rmbip}
                                        )
                                if Set.null $ Set.intersection parents' toPrune then do
                                    let remaining'' = foldl' (\remain g -> PQ.insert (goalDepth g, g, parents') remain) remaining' els'
                                    continue remaining'' valu oldSt
                                else -- prune proof (continue without elements of current rule)
                                    continue remaining' valu oldSt
                            _ -> put oldSt -- recover old state
                    -- given did not match required arguments required rule arguments -> end proof
                    Nothing -> put oldSt -- recover old state
                where
                -- | Continues finding proof with given remainig goals
                continue :: PQ (GoalDepth, AST.RuleBodyElement, Set GoalId) -- old remaining goals to prove
                         -> Map AST.VarName AST.Expr              -- valuation to apply to old goals
                         -> GroundingState                        -- grounding state
                         -> StateT GroundingState (Exceptional Exception) ()
                continue remaining'' valu oldSt = do
                    -- also apply valuation found to remaining goals todo
                    remaining''' <- applyVal remaining'' valu
                    -- continue with rest (breadth-first)
                    computeGroundings remaining'''
                    -- recover previous state for next head rule, but keep groundings found
                    modify' (\newSt -> oldSt { groundedRules    = groundedRules newSt
                                             , groundedRfDefs   = groundedRfDefs newSt
                                             , labelIdentifiers = labelIdentifiers newSt
                                             })

                addRuleToProof :: [AST.RuleBodyElement] -> State GroundingState ()
                addRuleToProof elements' = modify' (\st -> st{rulesInProof = Map.insertWith
                    (\[x] -> (x :))
                    (label, nArgs)
                    [(givenArgs, AST.RuleBody elements', GroundedAST.RuleBody Set.empty, parents)]
                    (rulesInProof st)
                })

                addRuleToMaybeProof :: [AST.RuleBodyElement] -> Set GoalId -> State GroundingState GoalId
                addRuleToMaybeProof elements' parents' = state $ \st ->
                    let ident@(GoalId next) = nextId st
                    in (ident, st { rulesMaybeInProof = RuleMaybeInProof
                                   { goalId        = ident
                                   , label         = label
                                   , args          = givenArgs
                                   , nonGroundBody = AST.RuleBody elements'
                                   , groundBody    = GroundedAST.RuleBody Set.empty
                                   , ruleParents   = parents'
                                   } : rulesMaybeInProof st
                             , nextId = GoalId $ succ next
                             }
                       )

        AST.BuildInPredicate bip -> case mbEquality of
            Just (var, expr) -> do
                oldSt <- get
                -- apply newly found variable substitution and check if proof is still consistent
                let valu = Map.singleton var expr
                consistent <- applyValuation  valu pfDefs
                if consistent then do
                    -- also apply valuation found to remaining goals todo
                    remaining'      <- applyVal remaining valu
                    computeGroundings remaining'
                else
                    put oldSt -- recover old state
            Nothing -> computeGroundings remaining
            where
            mbEquality = case bip of
                AST.Equality True (AST.Variable var) expr -> Just (var, expr)
                AST.Equality True expr (AST.Variable var) -> Just (var, expr)
                _                                         -> Nothing
        where
        applyVal :: PQ (GoalDepth, AST.RuleBodyElement, Set GoalId)
                 -> Map AST.VarName AST.Expr
                 -> GState (PQ (GoalDepth, AST.RuleBodyElement, Set GoalId))
        applyVal goals valu = lift $ foldM
            (\goals' (d, r, parents') -> do
                r' <- AST.mapExprsInRuleBodyElementM
                    r
                    (fmap snd . applyValuArg valu)
                    (return . snd . applyValuExpr valu)
                return $ PQ.insert (d, r', parents') goals'
            )
            PQ.empty
            goals

    goalDepth :: AST.RuleBodyElement -> GoalDepth
    goalDepth goal = goalDepth' goal Set.empty
        where
        goalDepth' :: AST.RuleBodyElement -> Set (AST.PredicateLabel, Int) -> GoalDepth
        goalDepth' (AST.BuildInPredicate _) _ = Depth 0
        goalDepth' (AST.UserPredicate label args) alreadySeen
            | Set.member goalSign alreadySeen = Infinite
            | otherwise = case Map.lookup goalSign rules of
                Just bodies -> maximum $ bodyDepth <$> bodies
                Nothing     -> undefined
            where
            goalSign = (label, length args)

            bodyDepth :: ([AST.HeadArgument], AST.RuleBody) -> GoalDepth
            bodyDepth (_, AST.RuleBody bodyElements)
                | null bodyElements = Depth 0
                | otherwise = incGoalDepth $ maximum $
                              (`goalDepth'` Set.insert goalSign alreadySeen) <$> bodyElements

            incGoalDepth :: GoalDepth -> GoalDepth
            incGoalDepth Infinite  = Infinite
            incGoalDepth (Depth d) = Depth $ succ d

-- add groundigs after proof is found
addGroundings :: GState ()
addGroundings = do
    constrs   <- gets proofConstraints
    rsInProof <- gets rulesInProof
    if Set.null constrs then do
        rules <- lift $ forM (Map.toList rsInProof) checkAllElementsGrounded
        -- from here on we can assume that no vars are left in rule heads
        forM_ rules addGroundingsHead
    else
        lift $ throw $ UnsolvableConstraints $ Set.toList constrs
    where
    checkAllElementsGrounded :: ((AST.PredicateLabel, Int), [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody, Set GoalId)])
                             -> Exceptional Exception (AST.PredicateLabel, Int, [([AST.Expr], GroundedAST.RuleBody)])
    checkAllElementsGrounded ((label, nArgs), bodies) = do
        bodies' <- forM bodies checkAllElementsGrounded'
        return (label, nArgs, bodies')
        where
        checkAllElementsGrounded' :: ([AST.Expr], AST.RuleBody, GroundedAST.RuleBody, Set GoalId)
                                  -> Exceptional Exception ([AST.Expr], GroundedAST.RuleBody)
        checkAllElementsGrounded' (args, AST.RuleBody nonGroundBody, groundedBody, _)
            | null nonGroundBody = return (args, groundedBody)
            | otherwise          = throw $ NonGroundPreds nonGroundBody label nArgs

    addGroundingsHead :: (AST.PredicateLabel, Int, [([AST.Expr], GroundedAST.RuleBody)])
                      -> GState ()
    addGroundingsHead (label, _, bodies) = forM_ bodies addGroundingBody
        where
        addGroundingBody :: ([AST.Expr], GroundedAST.RuleBody)
                         -> GState ()
        addGroundingBody (args, groundedBody) = do
            args'  <- lift $ toPropArgs args
            pLabel <- toPropPredLabel label args'
            modify' (\st -> st{groundedRules = Map.insertWith
                (\[x] -> (x :))
                pLabel
                [groundedBody]
                (groundedRules st)
            })

-- turn constructs from ordinary ones (with arguments) to propositional ones (after grounding)
toPropPredLabel :: AST.PredicateLabel -> [AST.ConstantExpr] -> GState GroundedAST.PredicateLabel
toPropPredLabel (AST.PredicateLabel label) args =
        GroundedAST.PredicateLabel
    <$> state ( \st -> let (idNr, lIdents) = IdNrMap.getIdNr (label, args) $ labelIdentifiers st
                       in  (idNr, st{labelIdentifiers = lIdents})
              )

-- TODO: doesn't have to be a monadic function
toPropPFuncLabel :: AST.PFuncLabel -> [AST.ConstantExpr] -> GState GroundedAST.PFuncLabel
toPropPFuncLabel label{-(AST.PFuncLabel label)-} args = return $ GroundedAST.PFuncLabel label args
    {-GroundedAST.PFuncLabel <$>
    state ( \st -> let (idNr, lIdents) = IdNrMap.getIdNr (label, args) $ labelIdentifiers st
                   in  (idNr, st{labelIdentifiers = lIdents})
          )-}

-- precondition: no vars in expr
-- throws exception if there are PFs in expressions
toPropArgs :: [AST.Expr] -> Exceptional Exception [AST.ConstantExpr]
toPropArgs exprs = forM exprs toPropArg

-- precondition: no vars in expr
-- throws exception if there are PFs in expressions
toPropArg :: AST.Expr -> Exceptional Exception AST.ConstantExpr
-- convert to grounded expr to perform simplification (e.g. for constant expr '1 + 1')
toPropArg expr = do
    expr' <- toPropArgExpr expr
    case expr' of
        ExprBool (GroundedAST.ConstantExpr (GroundedAST.BoolConstant cnst)) -> return $ AST.BoolConstant cnst
        ExprReal (GroundedAST.ConstantExpr (GroundedAST.RealConstant cnst)) -> return $ AST.RealConstant cnst
        ExprInt  (GroundedAST.ConstantExpr (GroundedAST.IntConstant  cnst)) -> return $ AST.IntConstant  cnst
        ExprStr  (GroundedAST.ConstantExpr (GroundedAST.StrConstant  cnst)) -> return $ AST.StrConstant  cnst
        ExprObj  (GroundedAST.ConstantExpr (GroundedAST.ObjConstant  cnst)) -> return $ AST.ObjConstant  cnst
        ExprPh   (GroundedAST.ConstantExpr (GroundedAST.Placeholder  ph  )) -> return $ AST.Placeholder  ph
        _                                                                   -> error "precondition"
    where
    toPropArgExpr :: AST.Expr -> Exceptional Exception PropExprWithType
    toPropArgExpr expr' = mapPropExprWithType GroundedAST.simplifiedExpr <$> case expr' of
        AST.ConstantExpr cnst -> return $ toPropExprConst cnst
        AST.PFunc _ _ -> throw ProbabilisticFuncUsedAsArg
        AST.Sum exprX exprY -> do
            exprX' <- toPropArgExpr exprX
            exprY' <- toPropArgExpr exprY
            case (exprX', exprY') of
                (ExprReal exprX''', ExprReal exprY''') -> return $ ExprReal $ GroundedAST.Sum exprX''' exprY'''
                (ExprInt  exprX''', ExprInt  exprY''') -> return $ ExprInt  $ GroundedAST.Sum exprX''' exprY'''
                _                                      -> throw $ TypeError exprX' exprY'
        AST.Variable _ -> error "precondition"

-- precondition: no vars left in rule element
toPropRuleElement :: AST.RuleBodyElement
                  -> Map (AST.PFuncLabel, Int) [([AST.HeadArgument], AST.PFuncDef)]
                  -> GState GroundedAST.RuleBodyElement
toPropRuleElement (AST.UserPredicate label args) _ = do
    args'  <- lift $ toPropArgs args
    pLabel <- toPropPredLabel label args'
    return $ GroundedAST.UserPredicate pLabel
toPropRuleElement (AST.BuildInPredicate bip) pfDefs = GroundedAST.BuildInPredicate <$> toPropBuildInPred bip pfDefs

data PropExprWithType = ExprBool (GroundedAST.Expr Bool)
                      | ExprReal (GroundedAST.Expr GroundedAST.RealN)
                      | ExprStr  (GroundedAST.Expr Text)
                      | ExprInt  (GroundedAST.Expr Integer)
                      | ExprObj  (GroundedAST.Expr GroundedAST.Object)
                      | ExprPh   (GroundedAST.Expr GroundedAST.Placeholder)

propExprWithTypeToText :: PropExprWithType -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder
propExprWithTypeToText expr ids2str ids2label = "'" <> exprStr <> "' (of type " <> typeStr <> ")"
    where
    (exprStr, typeStr) = case expr of
        ExprBool expr' -> (GroundedAST.exprToText expr' ids2str ids2label, "Bool")
        ExprReal expr' -> (GroundedAST.exprToText expr' ids2str ids2label, "Real")
        ExprStr  expr' -> (GroundedAST.exprToText expr' ids2str ids2label, "String")
        ExprInt  expr' -> (GroundedAST.exprToText expr' ids2str ids2label, "Integer")
        ExprObj  expr' -> (GroundedAST.exprToText expr' ids2str ids2label, "Object")
        ExprPh   expr' -> (GroundedAST.exprToText expr' ids2str ids2label, "Placeholder")

mapPropExprWithType :: (forall a. GroundedAST.Expr a -> GroundedAST.Expr a) -> PropExprWithType -> PropExprWithType
mapPropExprWithType f (ExprBool expr) = ExprBool $ f expr
mapPropExprWithType f (ExprReal expr) = ExprReal $ f expr
mapPropExprWithType f (ExprStr  expr) = ExprStr  $ f expr
mapPropExprWithType f (ExprInt  expr) = ExprInt  $ f expr
mapPropExprWithType f (ExprObj  expr) = ExprObj  $ f expr
mapPropExprWithType f (ExprPh   expr) = ExprPh   $ f expr

-- precondition: no vars left in 'bip'
toPropBuildInPred :: AST.BuildInPredicate
                  -> Map (AST.PFuncLabel, Int) [([AST.HeadArgument], AST.PFuncDef)]
                  -> GState GroundedAST.BuildInPredicate
toPropBuildInPred bip pfDefs = GroundedAST.simplifiedBuildInPred <$> case bip of
    AST.Equality eq exprX exprY -> toPropBuildInPred'     (GroundedAST.Equality eq) exprX exprY
    AST.Ineq     op exprX exprY -> toPropBuildInPredIneq' (GroundedAST.Ineq     op) exprX exprY
    where
    toPropBuildInPred' :: (forall a. GroundedAST.Expr a -> GroundedAST.Expr a -> GroundedAST.TypedBuildInPred a)
                       -> AST.Expr
                       -> AST.Expr
                       -> GState GroundedAST.BuildInPredicate
    toPropBuildInPred' bipConstructor exprX exprY = do
        exprX' <- toPropExpr exprX pfDefs
        exprY' <- toPropExpr exprY pfDefs
        case (exprX', exprY') of
            (ExprReal exprX'', ExprReal exprY'') -> return $ GroundedAST.BuildInPredicateReal $ bipConstructor exprX'' exprY''
            (ExprBool exprX'', ExprBool exprY'') -> return $ GroundedAST.BuildInPredicateBool $ bipConstructor exprX'' exprY''
            (ExprInt  exprX'', ExprInt  exprY'') -> return $ GroundedAST.BuildInPredicateInt  $ bipConstructor exprX'' exprY''
            (ExprStr  exprX'', ExprStr  exprY'') -> return $ GroundedAST.BuildInPredicateStr  $ bipConstructor exprX'' exprY''
            (ExprObj  exprX'', ExprObj  exprY'') -> return $ GroundedAST.BuildInPredicateObj  $ bipConstructor exprX'' exprY''
            (ExprPh   exprX'', ExprPh   exprY'') -> return $ GroundedAST.BuildInPredicatePh   $ bipConstructor exprX'' exprY''
            _                                    -> lift $ throw $ TypeError exprX' exprY'

    toPropBuildInPredIneq' :: (forall a. GroundedAST.Ineq a => GroundedAST.Expr a -> GroundedAST.Expr a -> GroundedAST.TypedBuildInPred a)
                           -> AST.Expr
                           -> AST.Expr
                           -> GState GroundedAST.BuildInPredicate
    toPropBuildInPredIneq' bipConstructor exprX exprY = do
        exprX' <- toPropExpr exprX pfDefs
        exprY' <- toPropExpr exprY pfDefs
        case (exprX', exprY') of
            (ExprReal exprX'', ExprReal exprY'') -> return $ GroundedAST.BuildInPredicateReal $ bipConstructor exprX'' exprY''
            (ExprInt  exprX'', ExprInt  exprY'') -> return $ GroundedAST.BuildInPredicateInt  $ bipConstructor exprX'' exprY''
            _                                    -> lift $ throw $ TypeError exprX' exprY'

-- precondition: no vars left in 'expr' (PF defs with vars result in exceptions)
toPropExpr :: AST.Expr
           -> Map (AST.PFuncLabel, Int) [([AST.HeadArgument], AST.PFuncDef)]
           -> GState PropExprWithType
toPropExpr expr pfDefs = mapPropExprWithType GroundedAST.simplifiedExpr <$> case expr of
    AST.ConstantExpr cnst -> return $ toPropExprConst cnst
    AST.PFunc label args -> toPropPFunc label args
        where
        toPropPFunc :: AST.PFuncLabel -> [AST.Expr] -> GState PropExprWithType
        toPropPFunc label' args' = do
            gPfDefs <- gets groundedRfDefs
            propArgs <- lift $ toPropArgs args'
            propPFuncLabel <- toPropPFuncLabel label' propArgs
            pfDef <- case Map.lookup propPFuncLabel gPfDefs of
                Just def -> return def
                Nothing  -> do
                    (def, valu) <- lift $ pfDefFor label' propArgs pfDefs
                    def' <- lift $ applyValuPfDef valu def
                    modify' (\st -> st{groundedRfDefs =
                        Map.insert propPFuncLabel def' $ groundedRfDefs st
                    })
                    return def'
            case pfDef of
                AST.Flip p            -> return $ ExprBool $ GroundedAST.PFuncExpr $ GroundedAST.makePFuncBool   propPFuncLabel p
                AST.RealDist cdf cdf' -> return $ ExprReal $ GroundedAST.PFuncExpr $ GroundedAST.makePFuncReal   propPFuncLabel cdf cdf'
                AST.StrDist dist      -> return $ ExprStr  $ GroundedAST.PFuncExpr $ GroundedAST.makePFuncString propPFuncLabel dist
                AST.UniformObjDist nr -> return $ ExprObj  $ GroundedAST.PFuncExpr $ GroundedAST.makePFuncObj    propPFuncLabel nr
                AST.UniformOtherObjDist labelOther argsOther -> do
                    otherPf <- toPropPFunc labelOther argsOther
                    case otherPf of
                        ExprObj (GroundedAST.PFuncExpr otherPf') ->
                            return $ ExprObj  $ GroundedAST.PFuncExpr $ GroundedAST.makePFuncObjOther propPFuncLabel otherPf'
                        _ ->
                            lift $ throw $ DefArgShouldBeObjPf propPFuncLabel otherPf
            where
            applyValuPfDef :: Map AST.VarName AST.ConstantExpr -> AST.PFuncDef -> Exceptional Exception AST.PFuncDef
            applyValuPfDef valu def = case def of
                AST.UniformOtherObjDist labelOther argsOther -> do
                    argsOther' <- forM argsOther $ \arg -> do
                        (varP, arg') <- applyValuArg valu' arg
                        if varP then throw $ NonGroundPfDef def label' $ length args'
                                else return arg'
                    return $ AST.UniformOtherObjDist labelOther argsOther'
                _ -> return def
                where
                valu' = Map.map AST.ConstantExpr valu
    AST.Sum exprX exprY -> toPropExprPairAdd GroundedAST.Sum exprX exprY
        where
        toPropExprPairAdd :: (forall a. GroundedAST.Addition a => GroundedAST.Expr a -> GroundedAST.Expr a -> GroundedAST.Expr a)
                          -> AST.Expr
                          -> AST.Expr
                          -> GState PropExprWithType
        toPropExprPairAdd exprConstructor exprX' exprY' = do
            exprX'' <- toPropExpr exprX' pfDefs
            exprY'' <- toPropExpr exprY' pfDefs
            case (exprX'', exprY'') of
                (ExprReal exprX''', ExprReal exprY''') -> return $ ExprReal $ exprConstructor exprX''' exprY'''
                (ExprInt  exprX''', ExprInt  exprY''') -> return $ ExprInt  $ exprConstructor exprX''' exprY'''
                _                                      -> lift $ throw $ TypeError exprX'' exprY''
    AST.Variable _ -> error "precondition"

toPropExprConst :: AST.ConstantExpr -> PropExprWithType
toPropExprConst (AST.BoolConstant cnst) = ExprBool $ GroundedAST.ConstantExpr $ GroundedAST.BoolConstant cnst
toPropExprConst (AST.RealConstant cnst) = ExprReal $ GroundedAST.ConstantExpr $ GroundedAST.RealConstant cnst
toPropExprConst (AST.StrConstant  cnst) = ExprStr  $ GroundedAST.ConstantExpr $ GroundedAST.StrConstant  cnst
toPropExprConst (AST.IntConstant  cnst) = ExprInt  $ GroundedAST.ConstantExpr $ GroundedAST.IntConstant  cnst
toPropExprConst (AST.ObjConstant  cnst) = ExprObj  $ GroundedAST.ConstantExpr $ GroundedAST.ObjConstant  cnst
toPropExprConst (AST.Placeholder  ph)   = ExprPh   $ GroundedAST.ConstantExpr $ GroundedAST.Placeholder  ph

inCurProof :: AST.RuleBodyElement -> GState Bool3
inCurProof (AST.BuildInPredicate _) = return False3
inCurProof (AST.UserPredicate label givenArgs) = do
    rsInProof <- gets rulesInProof
    return $ case Map.lookup (label, nGivenArgs) rsInProof of
        Nothing -> False3
        Just rs -> foldl'
            (\inProof (args, _, _, _) -> inProof ||* compareArgs args)
            False3
            rs
        where
        nGivenArgs = length givenArgs
        compareArgs args
            | nGivenArgs == length args = foldl' (\eq (x, y) -> eq &&* compareArg x y) True3 $ zip givenArgs args
            | otherwise = False3

        compareArg (AST.ConstantExpr x) (AST.ConstantExpr y) = if x == y then True3 else False3
        compareArg _                    _                    = Unknown3

alreadyProven :: AST.RuleBodyElement -> GState Bool3
alreadyProven (AST.BuildInPredicate _) = return False3
alreadyProven (AST.UserPredicate label givenArgs) = do
    gRules <- gets groundedRules
    let allArgsGround = not $ any AST.varsInExpr givenArgs
    if allArgsGround then do
        args'  <- lift $ toPropArgs givenArgs
        pLabel <- toPropPredLabel label  args'
        return $ if isJust $ Map.lookup pLabel gRules
            then True3
            else False3
     else
        return False3

applyArgs :: [AST.Expr]
          -> [AST.HeadArgument]
          -> [AST.RuleBodyElement]
          -> MaybeT (Exceptional Exception) ([AST.RuleBodyElement], Map AST.VarName AST.Expr, Set Constraint)
applyArgs givenArgs args elements = do
        (intValu, extValu, constrs) <- doMaybe mbVals
        elements' <- lift $ forM elements (\e -> AST.mapExprsInRuleBodyElementM
                e
                (fmap snd . applyValuArg intValu)
                (return . snd . applyValuExpr intValu)
            )
        return (elements', extValu, constrs)
    where
    mbVals = foldl' applyArgs' (Just (Map.empty, Map.empty, Set.empty)) (zip givenArgs args)

    -- keep two valuation: an internal one for replacing variables in the current rule body
    --                     an external one for replacing existentially quantified variables in current proof
    applyArgs' :: Maybe (Map AST.VarName AST.Expr, Map AST.VarName AST.Expr, Set Constraint)
               -> (AST.Expr, AST.HeadArgument)
               -> Maybe (Map AST.VarName AST.Expr, Map AST.VarName AST.Expr, Set Constraint)
    applyArgs' mbVals' (given, req) = do
        (intValu, extValu, constrs) <- mbVals'
        case req of
            AST.ArgConstant cnstR -> case given of
                AST.ConstantExpr cnstG | cnstG == cnstR -> return (intValu, extValu, constrs)
                                       | otherwise      -> Nothing
                AST.Variable varG -> (\(extValu', constrs') -> (intValu, extValu', constrs')) <$>
                                     updateValu varG (AST.ConstantExpr cnstR) extValu constrs
                _ -> return (intValu, extValu, Set.insert (EqConstraint given $ AST.ConstantExpr cnstR) constrs)
            AST.ArgVariable varR -> case given of
                AST.Variable varG -> case Map.lookup varR intValu of
                    Just val -> (\(extValu', constrs') -> (intValu, extValu', constrs')) <$>
                                updateValu varG val extValu constrs
                    Nothing -> return (Map.insert varR given intValu, extValu, constrs)
                _ -> (\(intValu', constrs') -> (intValu', extValu, constrs')) <$>
                     updateValu varR given intValu constrs
            AST.ArgDontCareVariable -> return (intValu, extValu, constrs)
        where
        updateValu :: AST.VarName
                   -> AST.Expr
                   -> Map AST.VarName AST.Expr
                   -> Set Constraint
                   -> Maybe (Map AST.VarName AST.Expr, Set Constraint)
        updateValu var val valu constrs = case Map.lookup var valu of
            Just val' | val == val' -> Just (valu, constrs) -- this is type safe: if values are equal they are also of same type
                      | otherwise   -> Just (valu, Set.insert (EqConstraint val val') constrs)
            Nothing -> Just (Map.insert var val valu, constrs)

applyValuation :: Map AST.VarName AST.Expr
               -> Map (AST.PFuncLabel, Int) [([AST.HeadArgument], AST.PFuncDef)]
               -> GState Bool
applyValuation valu pfDefs = do
    rsInProof     <- gets rulesInProof
    pConstraints  <- gets proofConstraints
    mbRules       <- runMaybeT        $ foldlM applyValuRule       Map.empty $ Map.toList rsInProof
    mbConstraints <- lift $ runMaybeT $ foldlM applyValuConstraint Set.empty $ Set.toList pConstraints
    case (mbRules, mbConstraints) of
        (Just rules, Just constraints) -> do
            modify' (\st' -> st'{rulesInProof = rules, proofConstraints = constraints})
            return True
        _ ->
            return False
    where
    applyValuRule :: Map (AST.PredicateLabel, Int) [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody, Set GoalId)]
                  -> ((AST.PredicateLabel, Int), [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody, Set GoalId)])
                  -> MaybeT GState (Map (AST.PredicateLabel, Int) [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody, Set GoalId)])
    applyValuRule rules (signature, sigRules) = do
        sigRules' <- foldlM applyValu' [] sigRules
        return $ Map.insert signature sigRules' rules

    applyValu' :: [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody, Set GoalId)]
               -> ([AST.Expr], AST.RuleBody, GroundedAST.RuleBody, Set GoalId)
               -> MaybeT GState [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody, Set GoalId)]
    applyValu' rules (args, AST.RuleBody elements, GroundedAST.RuleBody gElements, parents) = do
        args' <- lift $ lift $ forM args $ fmap snd . applyValuArg valu
        (elements', gElements') <- foldlM (applyValuBodyEl valu pfDefs) ([], gElements) elements
        return $ (args', AST.RuleBody elements', GroundedAST.RuleBody gElements', parents) : rules

    applyValuConstraint :: Set Constraint -> Constraint -> MaybeT (Exceptional Exception) (Set Constraint)
    applyValuConstraint constraints (EqConstraint exprX exprY)
        | varsLeftX || varsLeftY  = return $ Set.insert constr' constraints
        | otherwise = do
            holds <- lift $ constraintHolds constr'
            if holds then return constraints -- true constraint can just be left out
                     else mzero              -- false constraint means proof becomes inconsistent
        where
        (varsLeftX, exprX') = applyValuExpr valu exprX
        (varsLeftY, exprY') = applyValuExpr valu exprY
        constr' = EqConstraint exprX' exprY'

applyValuationMaybeInProof :: Map AST.VarName AST.Expr
                           -> Map (AST.PFuncLabel, Int) [([AST.HeadArgument], AST.PFuncDef)]
                           -> GState (Maybe (Set GoalId))
applyValuationMaybeInProof valu pfDefs = do
    rsMbInProof <- gets rulesMaybeInProof
    mbRules     <- runMaybeT $ foldlM applyValuRule ([], Set.empty) rsMbInProof
    case mbRules of
        Just (rules, toPrune) -> do
            modify' (\st' -> st'{rulesMaybeInProof = rules})
            return $ Just toPrune
        _ ->
            return Nothing
    where
    applyValuRule :: ([RuleMaybeInProof], Set GoalId)
                  -> RuleMaybeInProof
                  -> MaybeT GState ([RuleMaybeInProof], Set GoalId)
    applyValuRule (rules, toPrune) rule@RuleMaybeInProof{goalId, label, args, nonGroundBody = AST.RuleBody elements, groundBody = GroundedAST.RuleBody gElements, ruleParents} = do
        args' <- lift $ lift $ forM args $ fmap snd . applyValuArg valu
        (elements', gElements') <- foldlM (applyValuBodyEl valu pfDefs) ([], gElements) elements
        inCProof <- lift $ inCurProof $ AST.UserPredicate label args'
        case inCProof of
            False3 -> do
                modify' ( \st -> st { rulesInProof = Map.insertWith
                        (++)
                        (label, length args')
                        [(args', AST.RuleBody elements', GroundedAST.RuleBody gElements', ruleParents)]
                        (rulesInProof st)
                    } )
                return (rules, toPrune)
            True3 -> return (rules, Set.insert goalId toPrune)
            Unknown3 -> return (rule
                { args          = args'
                , nonGroundBody = AST.RuleBody elements'
                , groundBody    = GroundedAST.RuleBody gElements'
                } : rules, toPrune)

applyValuBodyEl :: Map AST.VarName AST.Expr
                -> Map (AST.PFuncLabel, Int) [([AST.HeadArgument], AST.PFuncDef)]
                -> ([AST.RuleBodyElement], Set GroundedAST.RuleBodyElement)
                -> AST.RuleBodyElement
                -> MaybeT GState ([AST.RuleBodyElement], Set GroundedAST.RuleBodyElement)
applyValuBodyEl valu pfDefs (elements, gElements) el = do
    let (varPresent, el') = AST.mapAccExprsInRuleBodyElement
            (\varPresent' expr -> let (varPresent'', expr') = applyValuExpr valu expr
                                  in  (varPresent' || varPresent'', expr')
            )
            False
            el
    if varPresent then
        return (el' : elements, gElements)
    else do
        gEl <- lift $ toPropRuleElement el' pfDefs
        case gEl of
            GroundedAST.BuildInPredicate bip -> case GroundedAST.deterministicValue bip of
                Just True  -> return (elements, gElements)                -- true predicate can just be left out
                Just False -> mzero                                       -- false predicate means proof becomes inconsistent
                Nothing    -> return (elements, Set.insert gEl gElements) -- truthfullness depends on probabilistic functions
            _ -> return (elements, Set.insert gEl gElements)

-- returns whether still a non-valued variable is present
applyValuExpr :: Map AST.VarName AST.Expr -> AST.Expr -> (Bool, AST.Expr)
applyValuExpr valu = AST.mapAccExpr applyValuExpr' False
    where
    applyValuExpr' :: Bool -> AST.Expr -> (Bool, AST.Expr)
    applyValuExpr' varPresent expr'@(AST.Variable var) = case Map.lookup var valu of
        Just expr'' -> (varPresent || AST.varsInExpr expr'', expr'')
        _           -> (True,                                expr')
    applyValuExpr' varPresent expr' = (varPresent, expr')

-- simplifies if no vars are present any more
-- assumes no Rfs in expr (as it a predicate arg)
applyValuArg :: Map AST.VarName AST.Expr -> AST.Expr -> Exceptional Exception (Bool, AST.Expr)
applyValuArg valu expr
    | varPresent = return (True, expr')
    | otherwise = do
        arg <- toPropArg expr'
        return (False, AST.ConstantExpr arg)
    where
    (varPresent, expr') = applyValuExpr valu expr

-- replace existentially quantified (occuring in body, but not head) variables
replaceEVars :: [AST.RuleBodyElement] -> State GroundingState [AST.RuleBodyElement]
replaceEVars elements = state (\st -> let (varCounter', _, elements') = foldl'
                                              (\(c, v2ids, elements'') el ->
                                                  let ((c', v2ids'), el') = AST.mapAccExprsInRuleBodyElement replaceEVars' (c, v2ids) el
                                                  in  (c', v2ids', el' : elements'')
                                              )
                                              (varCounter st, Map.empty, [])
                                              elements
                                      in  (elements', st{varCounter = varCounter'})
                              )
    where
    replaceEVars' :: (Int, Map Text Int) -> AST.Expr -> ((Int, Map Text Int), AST.Expr)
    replaceEVars' (counter, vars2ids) expr = case expr of
        AST.Variable (AST.VarName var) -> case Map.lookup var vars2ids of
            Just i  -> ((counter, vars2ids), AST.Variable $ AST.TempVar i)
            Nothing -> ((succ counter, Map.insert var counter vars2ids), AST.Variable $ AST.TempVar counter)
        otherExpr -> ((counter, vars2ids), otherExpr)

pfDefFor :: AST.PFuncLabel
         -> [AST.ConstantExpr]
         -> Map (AST.PFuncLabel, Int) [([AST.HeadArgument], AST.PFuncDef)]
         -> Exceptional Exception (AST.PFuncDef, Map AST.VarName AST.ConstantExpr)
pfDefFor label args pfDefs = do
    defs <- exceptionalFromMaybe (UndefinedPf label nArgs) $ Map.lookup (label, nArgs) pfDefs
    let matchingDefs = catMaybes $ (\(defArgs, def) -> (def, ) <$> matchArgs args defArgs) <$> defs
    case matchingDefs of
        []         -> throw $ UndefinedPfValue label args
        (fstDef:_) -> return fstDef
    where
    nArgs = length args

    matchArgs :: [AST.ConstantExpr] -> [AST.HeadArgument] -> Maybe (Map AST.VarName AST.ConstantExpr)
    matchArgs givenArgs reqArgs = foldl' match (Just Map.empty) (zip givenArgs reqArgs)

    match :: Maybe (Map AST.VarName AST.ConstantExpr)
          -> (AST.ConstantExpr, AST.HeadArgument)
          -> Maybe (Map AST.VarName AST.ConstantExpr)
    match mbVal (given, req) = do
        val <- mbVal
        case req of
            AST.ArgConstant cnst -> if given == cnst then return val
                                                     else Nothing
            AST.ArgVariable var -> case Map.lookup var val of
                Nothing                   -> return $ Map.insert var given val
                Just cnst | cnst == given -> return val
                _                         -> Nothing
            AST.ArgDontCareVariable -> return val

-- precondition: no vars left in constraints
-- throws exception if PF is included in constr
constraintHolds :: Constraint -> Exceptional Exception Bool
constraintHolds (EqConstraint exprX exprY) =  do
    cnstX <- toPropArg exprX
    cnstY <- toPropArg exprY
    case (cnstX, cnstY) of
        (AST.BoolConstant x, AST.BoolConstant y) -> return $ x == y
        (AST.RealConstant x, AST.RealConstant y) -> return $ x == y
        (AST.IntConstant  x, AST.IntConstant  y) -> return $ x == y
        (AST.StrConstant  x, AST.StrConstant  y) -> return $ x == y
        _                                        -> throw $ TypeError (toPropExprConst cnstX) (toPropExprConst cnstY)
