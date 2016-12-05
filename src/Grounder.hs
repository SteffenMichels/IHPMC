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
    ( ground
    , Exception(..)
    , exceptionToText
    ) where
import AST (AST)
import qualified AST
import GroundedAST (GroundedAST(..))
import qualified GroundedAST
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Control.Monad.State.Strict
import Data.Foldable (foldl', foldlM)
import Data.Sequence (Seq, ViewL((:<)), (><))
import qualified Data.Sequence as Seq
import Data.Maybe (isJust)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Control.Monad.Trans.Maybe (MaybeT, runMaybeT)
import Exception
import Util
import Data.Boolean (Boolean(..))
import IdNrMap (IdNrMap)
import qualified IdNrMap
import Data.Text (Text)
import Data.Text.Lazy.Builder (Builder)
import Data.Monoid ((<>))
import TextShow

type GState = StateT GroundingState (Exceptional Exception)

data Exception = NonGroundPreds        [AST.RuleBodyElement] AST.PredicateLabel Int
               | TypeError             PropExprWithType PropExprWithType
               | UndefinedRf           AST.PFuncLabel Int
               | UndefinedRfValue      AST.PFuncLabel [AST.ConstantExpr]
               | UndefinedPred         AST.PredicateLabel Int
               | ProbabilisticFuncUsedAsArg
               | UnsolvableConstraints [Constraint]
               | NonGroundQuery        AST.RuleBodyElement
               | NonGroundEvidence     AST.RuleBodyElement

exceptionToText :: Exception -> HashMap Int Text -> HashMap Int (Int, [AST.ConstantExpr]) -> Builder
exceptionToText (NonGroundPreds prds headLabel headNArgs) ids2str _ =
        "Could not ground predicate" <>
        (if length prds > 1 then "s " else " ") <>
        toTextLstEnc "'" "'" prds (`AST.ruleBodyElementToText` ids2str) <>
        " in a body of '" <>
        AST.predicateLabelToText headLabel ids2str <>
        "/" <>
        showb headNArgs <>
        "'."
exceptionToText (TypeError exprX exprY) ids2str ids2label =
        "Types of expressions " <>
        propExprWithTypeToText exprX ids2str ids2label <>
        " and " <>
        propExprWithTypeToText exprY ids2str ids2label <>
        " do not match."
exceptionToText (UndefinedRf pf n) ids2str _ =
        "Probabilistic function '" <>
        AST.pFuncLabelToText pf ids2str <>
        "/" <>
        showb n <>
        "' is undefined."
exceptionToText (UndefinedRfValue pf args) ids2str _ =
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
exceptionToText ProbabilisticFuncUsedAsArg _ _ =
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

data Constraint = EqConstraint AST.Expr AST.Expr deriving (Eq, Generic)
constraintToText :: Constraint -> HashMap Int Text -> Builder
constraintToText (EqConstraint exprX exprY) ids2str = AST.exprToText exprX ids2str <> " = " <> AST.exprToText exprY ids2str
instance Hashable Constraint

data GroundingState = GroundingState
    { groundedRules     :: HashMap GroundedAST.PredicateLabel [GroundedAST.RuleBody]
    , groundedRfDefs    :: HashMap GroundedAST.PFuncLabel AST.PFuncDef
    , varCounter        :: Int
    -- keep non-ground rule body elements and to ground elements as soon as all vars have a value
    -- this pruning partial proofs if predicate is false
    , rulesInProof      :: HashMap (AST.PredicateLabel, Int) [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody, HashSet GoalId)]
    , rulesMaybeInProof :: [RuleMaybeInProof]
    , proofConstraints  :: HashSet Constraint
    , nextId            :: GoalId
    , labelIdentifiers  :: IdNrMap (Int, [AST.ConstantExpr])
    }

data RuleMaybeInProof = RuleMaybeInProof
    { goalId        :: GoalId
    , label         :: AST.PredicateLabel
    , args          :: [AST.Expr]
    , nonGroundBody :: AST.RuleBody
    , groundBody    :: GroundedAST.RuleBody
    , ruleParents   :: HashSet GoalId
    }

newtype GoalId = GoalId Int deriving (Eq, Generic, Show)
instance Hashable GoalId

-- | Converts an AST go a grounded AST.
-- Additionally, produces ID numbers for each constant expression, ocurring in the grounding.
ground :: AST -> Exceptional Exception (GroundedAST, IdNrMap (Int, [AST.ConstantExpr]))
ground AST.AST{AST.queries=queries, AST.evidence=evidence, AST.rules=rules, AST.pFuncDefs=pfDefs} = evalStateT
    (do
        (queries', evidence') <- computeResultState
        gRules <- gets groundedRules
        pIds   <- gets labelIdentifiers
        return ( GroundedAST { rules = Map.map Set.fromList gRules
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
    -- | Computes a state which contains all ground rules.
    -- Returns all queries and evidence as grounded elements.
    computeResultState :: GState (HashSet GroundedAST.RuleBodyElement, HashSet GroundedAST.RuleBodyElement)
    computeResultState = do
        queries'  <- forM queries  $ toPropQueryEvidence NonGroundQuery
        evidence' <- forM evidence $ toPropQueryEvidence NonGroundEvidence
        forM_ (queries ++ evidence) $
            \el -> computeGroundings $ Seq.singleton (el, Set.empty)
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
    computeGroundings :: Seq (AST.RuleBodyElement, HashSet GoalId) -> GState ()
    computeGroundings todo = do
        -- filter all goals which do not have to be proven any more
        todo' <- Seq.filter ((/= False3) . snd) <$> forM todo (\g -> (g,) <$> haveToProof (fst g))
        -- find the first goal that certainly has to be proven
        let (prefix, postfix) = Seq.breakl ((== True3) . snd) todo'
        case Seq.viewl postfix of
            -- continue with first goal
            (nextGoal, _) :< todoRest -> computeGroundingsGoal nextGoal False (fst <$> prefix >< todoRest)
            -- no goal has to be proven for sure
            Seq.EmptyL -> case Seq.viewl todo of
                    -- we have to continue with goal of which we do not know yet whether it has to be proven
                    nextGoal :< todoRest -> computeGroundingsGoal nextGoal True todoRest
                    -- no goal has to be proven at all -> finish proof
                    Seq.EmptyL           -> addGroundings

    -- | Continues computing groundings with the goal given.
    computeGroundingsGoal :: (AST.RuleBodyElement, HashSet GoalId)     -- the goal to continue with & set of parent IDs
                          -> Bool                                      -- is it not known whether we still have to prove the goal yet?
                          -> Seq (AST.RuleBodyElement, HashSet GoalId) -- the remaining goals to prove
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
                                let remaining' = Seq.filter (\(_, parents'') -> null $ Set.intersection toPrune parents'') remaining
                                modify' ( \st ->
                                            let rip   = Map.filter (not . null) $
                                                    filter (\(_, _, _, ruleParents) -> null $ Set.intersection toPrune ruleParents) <$>
                                                    rulesInProof st
                                                rmbip = filter
                                                    (\RuleMaybeInProof{ruleParents} -> null $ Set.intersection toPrune ruleParents)
                                                    (rulesMaybeInProof st)
                                            in st{rulesInProof = rip, rulesMaybeInProof = rmbip}
                                        )
                                if null $ Set.intersection parents toPrune then do
                                    let els'' = if   null $ Set.intersection toPrune parents'
                                                then Seq.fromList $ (, parents') <$> els'
                                                else Seq.empty
                                    continue remaining' els'' valu oldSt
                                else -- prune proof (continue without elements of current rule)
                                    continue remaining' Seq.empty valu oldSt
                            _ -> put oldSt -- recover old state
                    -- given did not match required arguments required rule arguments -> end proof
                    Nothing -> put oldSt -- recover old state
                where
                -- | Continues finding proof with given remainig goals
                continue :: Seq (AST.RuleBodyElement, HashSet GoalId) -- old remaining goals to prove
                         -> Seq (AST.RuleBodyElement, HashSet GoalId) -- new remaining goals to prove
                         -> HashMap AST.VarName AST.Expr              -- valuation to apply to old goals
                         -> GroundingState                            -- grounding state
                         -> StateT GroundingState (Exceptional Exception) ()
                continue remaining'' new valu oldSt = do
                    -- also apply valuation found to remaining goals todo
                    remaining''' <- applyVal remaining'' valu
                    -- continue with rest (breadth-first)
                    computeGroundings $ remaining''' >< new
                    -- recover previous state for next head rule, but keep groundings found
                    modify' (\newSt -> oldSt {groundedRules = groundedRules newSt, groundedRfDefs = groundedRfDefs newSt, labelIdentifiers = labelIdentifiers newSt})

                addRuleToProof :: [AST.RuleBodyElement] -> State GroundingState ()
                addRuleToProof elements' = modify' (\st -> st{rulesInProof = Map.insertWith
                    (\[x] -> (x :))
                    (label, nArgs)
                    [(givenArgs, AST.RuleBody elements', GroundedAST.RuleBody Set.empty, parents)]
                    (rulesInProof st)
                })

                addRuleToMaybeProof :: [AST.RuleBodyElement] -> HashSet GoalId -> State GroundingState GoalId
                addRuleToMaybeProof elements' parents' = do
                    st <- get
                    let ident@(GoalId next) = nextId st
                    put $ st { rulesMaybeInProof = RuleMaybeInProof
                                   { goalId        = ident
                                   , label         = label
                                   , args          = givenArgs
                                   , nonGroundBody = AST.RuleBody elements'
                                   , groundBody    = GroundedAST.RuleBody Set.empty
                                   , ruleParents   = parents'
                                   } : rulesMaybeInProof st
                             , nextId = GoalId $ succ next
                             }
                    return ident

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
        applyVal :: Seq (AST.RuleBodyElement, HashSet GoalId) -> HashMap AST.VarName AST.Expr -> GState (Seq (AST.RuleBodyElement, HashSet GoalId))
        applyVal goals valu = lift $ forM goals (\(r, parents') -> do
                r' <- AST.mapExprsInRuleBodyElementM
                    r
                    (applyValuArg valu)
                    (return . snd . applyValuExpr valu)
                return (r', parents')
            )
-- add groundigs after proof is found
addGroundings :: GState ()
addGroundings = do
    st <- get
    let constrs = proofConstraints st
    if null constrs then do
        rules <- lift $ forM (Map.toList $ rulesInProof st) checkAllElementsGrounded
        -- from here on we can assume that no vars are left in rule heads
        forM_ rules addGroundingsHead
    else
        lift $ throw $ UnsolvableConstraints $ Set.toList constrs
    where
    checkAllElementsGrounded :: ((AST.PredicateLabel, Int), [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody, HashSet GoalId)])
                             -> Exceptional Exception (AST.PredicateLabel, Int, [([AST.Expr], GroundedAST.RuleBody)])
    checkAllElementsGrounded ((label, nArgs), bodies) = do
        bodies' <- forM bodies checkAllElementsGrounded'
        return (label, nArgs, bodies')
        where
        checkAllElementsGrounded' :: ([AST.Expr], AST.RuleBody, GroundedAST.RuleBody, HashSet GoalId)
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

toPropPFuncLabel :: AST.PFuncLabel -> [AST.ConstantExpr] -> GState GroundedAST.PFuncLabel
toPropPFuncLabel (AST.PFuncLabel label) args =
        GroundedAST.PFuncLabel
    <$> state ( \st -> let (idNr, lIdents) = IdNrMap.getIdNr (label, args) $ labelIdentifiers st
                       in  (idNr, st{labelIdentifiers = lIdents})
              )

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
                  -> HashMap (AST.PFuncLabel, Int) [([AST.HeadArgument], AST.PFuncDef)]
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

propExprWithTypeToText :: PropExprWithType -> HashMap Int Text -> HashMap Int (Int, [AST.ConstantExpr]) -> Builder
propExprWithTypeToText expr ids2str ids2label = "'" <> exprStr <> "' (of type " <> typeStr <> ")"
    where
    (exprStr, typeStr) = case expr of
        ExprBool expr' -> (GroundedAST.exprToText expr' ids2str ids2label, "Bool")
        ExprReal expr' -> (GroundedAST.exprToText expr' ids2str ids2label, "Real")
        ExprStr  expr' -> (GroundedAST.exprToText expr' ids2str ids2label, "String")
        ExprInt  expr' -> (GroundedAST.exprToText expr' ids2str ids2label, "Integer")

mapPropExprWithType :: (forall a. GroundedAST.Expr a -> GroundedAST.Expr a) -> PropExprWithType -> PropExprWithType
mapPropExprWithType f (ExprBool expr) = ExprBool $ f expr
mapPropExprWithType f (ExprReal expr) = ExprReal $ f expr
mapPropExprWithType f (ExprStr  expr) = ExprStr  $ f expr
mapPropExprWithType f (ExprInt  expr) = ExprInt  $ f expr

-- precondition: no vars left in 'bip'
toPropBuildInPred :: AST.BuildInPredicate
                  -> HashMap (AST.PFuncLabel, Int) [([AST.HeadArgument], AST.PFuncDef)]
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

-- precondition: no vars left in 'expr'
toPropExpr :: AST.Expr
           -> HashMap (AST.PFuncLabel, Int) [([AST.HeadArgument], AST.PFuncDef)]
           -> GState PropExprWithType
toPropExpr expr pfDefs = mapPropExprWithType GroundedAST.simplifiedExpr <$> case expr of
    AST.ConstantExpr cnst -> return $ toPropExprConst cnst
    AST.PFunc label args -> do
        gPfDefs <- gets groundedRfDefs
        propArgs <- lift $ toPropArgs args
        propPFuncLabel <- toPropPFuncLabel label propArgs
        pfDef <- case Map.lookup propPFuncLabel gPfDefs of
            Just def -> return def
            Nothing  -> do
                def <- lift $ pfDefFor label propArgs pfDefs
                modify' (\st -> st{groundedRfDefs =
                    Map.insert propPFuncLabel def $ groundedRfDefs st
                })
                return def
        case pfDef of
            AST.Flip p            -> return $ ExprBool $ GroundedAST.PFuncExpr $ GroundedAST.makePFuncBool propPFuncLabel p
            AST.RealDist cdf cdf' -> return $ ExprReal $ GroundedAST.PFuncExpr $ GroundedAST.makePFuncReal propPFuncLabel cdf cdf'
            AST.StrDist dist      -> return $ ExprStr  $ GroundedAST.PFuncExpr $ GroundedAST.makePFuncString propPFuncLabel dist
    AST.Sum exprX exprY ->toPropExprPairAdd GroundedAST.Sum exprX exprY
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

haveToProof :: AST.RuleBodyElement -> GState Bool3
haveToProof (AST.BuildInPredicate _) = return True3
haveToProof (AST.UserPredicate label givenArgs) = do
    let nGivenArgs = length givenArgs
    rsInProof <- gets rulesInProof
    let inCurProof = case Map.lookup (label, nGivenArgs) rsInProof of
            Nothing -> False3
            Just rs -> foldl'
                (\inProof (args, _, _, _) -> inProof ||* compareArgs args)
                False3
                rs
            where
            compareArgs args
                | nGivenArgs == length args = foldl' (\eq (x, y) -> eq &&* compareArg x y) True3 $ zip givenArgs args
                | otherwise = False3

            compareArg (AST.ConstantExpr x) (AST.ConstantExpr y) = if x == y then True3 else False3
            compareArg _                    _                    = Unknown3
    return $ notB inCurProof

applyArgs :: [AST.Expr]
          -> [AST.HeadArgument]
          -> [AST.RuleBodyElement]
          -> MaybeT (Exceptional Exception) ([AST.RuleBodyElement], HashMap AST.VarName AST.Expr, HashSet Constraint)
applyArgs givenArgs args elements = do
        (intValu, extValu, constrs) <- doMaybe mbVals
        elements' <- lift $ forM elements (\e -> AST.mapExprsInRuleBodyElementM
                e
                (applyValuArg intValu)
                (return . snd . applyValuExpr intValu)
            )
        return (elements', extValu, constrs)
    where
    mbVals = foldl' applyArgs' (Just (Map.empty, Map.empty, Set.empty)) (zip givenArgs args)

    -- keep two valuation: an internal one for replacing variables in the current rule body
    --                     an external one for replacing existentially quantified variables in current proof
    applyArgs' :: Maybe (HashMap AST.VarName AST.Expr, HashMap AST.VarName AST.Expr, HashSet Constraint)
               -> (AST.Expr, AST.HeadArgument)
               -> Maybe (HashMap AST.VarName AST.Expr, HashMap AST.VarName AST.Expr, HashSet Constraint)
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
                   -> HashMap AST.VarName AST.Expr
                   -> HashSet Constraint
                   -> Maybe (HashMap AST.VarName AST.Expr, HashSet Constraint)
        updateValu var val valu constrs = case Map.lookup var valu of
            Just val' | val == val' -> Just (valu, constrs) -- this is type safe: if values are equal they are also of same type
                      | otherwise   -> Just (valu, Set.insert (EqConstraint val val') constrs)
            Nothing -> Just (Map.insert var val valu, constrs)

applyValuation :: HashMap AST.VarName AST.Expr
               -> HashMap (AST.PFuncLabel, Int) [([AST.HeadArgument], AST.PFuncDef)]
               -> GState Bool
applyValuation valu pfDefs = do
    st            <- get
    mbRules       <- runMaybeT        $ foldlM applyValuRule       Map.empty $ Map.toList $ rulesInProof st
    mbConstraints <- lift $ runMaybeT $ foldlM applyValuConstraint Set.empty $ proofConstraints st
    case (mbRules, mbConstraints) of
        (Just rules, Just constraints) -> do
            modify' (\st' -> st'{rulesInProof = rules, proofConstraints = constraints})
            return True
        _ ->
            return False
    where
    applyValuRule :: HashMap (AST.PredicateLabel, Int) [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody, HashSet GoalId)]
                  -> ((AST.PredicateLabel, Int), [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody, HashSet GoalId)])
                  -> MaybeT GState (HashMap (AST.PredicateLabel, Int) [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody, HashSet GoalId)])
    applyValuRule rules (signature, sigRules) = do
        sigRules' <- foldlM applyValu' [] sigRules
        return $ Map.insert signature sigRules' rules

    applyValu' :: [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody, HashSet GoalId)]
               -> ([AST.Expr], AST.RuleBody, GroundedAST.RuleBody, HashSet GoalId)
               -> MaybeT GState [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody, HashSet GoalId)]
    applyValu' rules (args, AST.RuleBody elements, GroundedAST.RuleBody gElements, parents) = do
        args' <- lift $ lift $ forM args $ applyValuArg valu
        (elements', gElements') <- foldlM (applyValuBodyEl valu pfDefs) ([], gElements) elements
        return $ (args', AST.RuleBody elements', GroundedAST.RuleBody gElements', parents) : rules

    applyValuConstraint :: HashSet Constraint -> Constraint -> MaybeT (Exceptional Exception) (HashSet Constraint)
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

applyValuationMaybeInProof :: HashMap AST.VarName AST.Expr
                           -> HashMap (AST.PFuncLabel, Int) [([AST.HeadArgument], AST.PFuncDef)]
                           -> GState (Maybe (HashSet GoalId))
applyValuationMaybeInProof valu pfDefs = do
    st            <- get
    mbRules       <- runMaybeT $ foldlM applyValuRule ([], Set.empty) $ rulesMaybeInProof st
    case mbRules of
        Just (rules, toPrune) -> do
            modify' (\st' -> st'{rulesMaybeInProof = rules})
            return $ Just toPrune
        _ ->
            return Nothing
    where
    applyValuRule :: ([RuleMaybeInProof], HashSet GoalId)
                  -> RuleMaybeInProof
                  -> MaybeT GState ([RuleMaybeInProof], HashSet GoalId)
    applyValuRule (rules, toPrune) rule@RuleMaybeInProof{goalId, label, args, nonGroundBody = AST.RuleBody elements, groundBody = GroundedAST.RuleBody gElements, ruleParents} = do
        args' <- lift $ lift $ forM args $ applyValuArg valu
        (elements', gElements') <- foldlM (applyValuBodyEl valu pfDefs) ([], gElements) elements
        toProof <- lift $ haveToProof $ AST.UserPredicate label args'
        case toProof of
            True3 -> do
                modify' ( \st -> st { rulesInProof = Map.insertWith
                        (++)
                        (label, length args')
                        [(args', AST.RuleBody elements', GroundedAST.RuleBody gElements', ruleParents)]
                        (rulesInProof st)
                    } )
                return (rules, toPrune)
            False3 -> return (rules, Set.insert goalId toPrune)
            Unknown3 -> return (rule
                { args          = args'
                , nonGroundBody = AST.RuleBody elements'
                , groundBody    = GroundedAST.RuleBody gElements'
                } : rules, toPrune)

applyValuBodyEl :: HashMap AST.VarName AST.Expr
                -> HashMap (AST.PFuncLabel, Int) [([AST.HeadArgument], AST.PFuncDef)]
                -> ([AST.RuleBodyElement], HashSet GroundedAST.RuleBodyElement)
                -> AST.RuleBodyElement
                -> MaybeT GState ([AST.RuleBodyElement], HashSet GroundedAST.RuleBodyElement)
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
applyValuExpr :: HashMap AST.VarName AST.Expr -> AST.Expr -> (Bool, AST.Expr)
applyValuExpr valu = AST.mapAccExpr applyValuExpr' False
    where
    applyValuExpr' :: Bool -> AST.Expr -> (Bool, AST.Expr)
    applyValuExpr' varPresent expr'@(AST.Variable var) = case Map.lookup var valu of
        Just expr'' -> (varPresent || AST.varsInExpr expr'', expr'')
        _           -> (True,                                expr')
    applyValuExpr' varPresent expr' = (varPresent, expr')

-- simplifies if no vars are present any more
-- assumes no Rfs in expr (as it a predicate arg)
applyValuArg :: HashMap AST.VarName AST.Expr -> AST.Expr-> Exceptional Exception AST.Expr
applyValuArg valu expr
    | varPresent = return expr'
    | otherwise = do
        arg <- toPropArg expr'
        return $ AST.ConstantExpr arg
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
    replaceEVars' :: (Int, HashMap Text Int) -> AST.Expr -> ((Int, HashMap Text Int), AST.Expr)
    replaceEVars' (counter, vars2ids) expr = case expr of
        AST.Variable (AST.VarName var) -> case Map.lookup var vars2ids of
            Just i  -> ((counter, vars2ids), AST.Variable $ AST.TempVar i)
            Nothing -> ((succ counter, Map.insert var counter vars2ids), AST.Variable $ AST.TempVar counter)
        otherExpr -> ((counter, vars2ids), otherExpr)

pfDefFor :: AST.PFuncLabel
         -> [AST.ConstantExpr]
         -> HashMap (AST.PFuncLabel, Int) [([AST.HeadArgument], AST.PFuncDef)]
         -> Exceptional Exception AST.PFuncDef
pfDefFor label args pfDefs = do
    defs <- exceptionalFromMaybe (UndefinedRf label nArgs) $ Map.lookup (label, nArgs) pfDefs
    let matchingDefs = filter (\(defArgs, _) -> matchArgs args defArgs) defs
    case matchingDefs of
        []             -> throw $ UndefinedRfValue label args
        ((_,fstDef):_) -> return fstDef
    where
    nArgs = length args

    matchArgs :: [AST.ConstantExpr] -> [AST.HeadArgument] -> Bool
    matchArgs givenArgs reqArgs = isJust $ foldl' match (Just Map.empty) (zip givenArgs reqArgs)

match :: Maybe (HashMap AST.VarName AST.ConstantExpr)
      -> (AST.ConstantExpr, AST.HeadArgument)
      -> Maybe (HashMap AST.VarName AST.ConstantExpr)
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
