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

module Grounder
    ( ground
    , Exception(..)
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
import Text.Printf (printf)
import Data.Foldable (foldl', foldlM)
import Data.Traversable (forM)
import Data.Sequence (Seq, ViewL((:<)), (><))
import qualified Data.Sequence as Seq
import Data.Maybe (isJust)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Control.Monad.Trans.Maybe (MaybeT, runMaybeT)
import Exception
import Util
import Data.Boolean (Boolean(..))

type GState = StateT GroundingState (Exceptional Exception)

data Exception = NonGroundPreds   [AST.RuleBodyElement] AST.PredicateLabel Int
               | TypeError        PropExprWithType PropExprWithType
               | UndefinedRf      AST.RFuncLabel Int
               | UndefinedRfValue AST.RFuncLabel [AST.ConstantExpr]
               | RandomFuncUsedAsArg

instance Show Exception
    where
    show (NonGroundPreds prds headLabel headNArgs) = printf
        "Could not ground predicate%s %s in a body of '%s/%i'."
        (if length prds > 1 then "s" else "")
        (showLstEnc "'" "'" prds)
        (show headLabel)
        headNArgs
    show (TypeError exprX exprY) = printf
        "Types of expressions %s and %s do not match."
        (show exprX)
        (show exprY)
    show (UndefinedRf label n) = printf
        "Random function '%s/%i' is undefined."
        (show label)
        n
    show (UndefinedRfValue rf args) = printf
        "'%s(%s)' is undefined."
        (show rf)
        (showLst args)
    show RandomFuncUsedAsArg = "Random functions may not be used in arguments of predicates and functions."

data Constraint = EqConstraint AST.Expr AST.Expr deriving (Eq, Generic, Show)
instance Hashable Constraint

data GroundingState = GroundingState
    { groundedRules    :: HashMap GroundedAST.PredicateLabel [GroundedAST.RuleBody]
    , groundedRfDefs   :: HashMap GroundedAST.RFuncLabel GroundedAST.RFuncDef
    , varCounter       :: Integer
    -- keep non-ground rule body elements and to ground elements as soon as all vars have a value
    -- this pruning partial proofs if predicate is false
    , rulesInProof     :: HashMap (AST.PredicateLabel, Int) [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody)]
    , proofConstraints :: HashSet Constraint
    }

ground :: AST -> Exceptional Exception GroundedAST
ground AST.AST{AST.queries=queries, AST.evidence=evidence, AST.rules=rules, AST.rFuncDefs=rfDefs} = evalStateT
    (do
        (queries', evidence') <- computeResultState
        gRules <- gets groundedRules
        return GroundedAST { rules = Map.map Set.fromList gRules
                           , queries  = queries'
                           , evidence = evidence'
                           }
    )
    GroundingState{ groundedRules    = Map.empty
                  , groundedRfDefs   = Map.empty
                  , varCounter       = 0
                  , rulesInProof     = Map.empty
                  , proofConstraints = Set.empty
                  }
    where
    computeResultState :: GState (HashSet GroundedAST.RuleBodyElement, HashSet GroundedAST.RuleBodyElement)
    computeResultState = do
        queries'  <- forM queries  (`toPropRuleElement` rfDefs)
        evidence' <- forM evidence (`toPropRuleElement` rfDefs)
        forM_ (queries ++ evidence) $
            \el -> computeGroundings $ Seq.singleton el
        return (Set.fromList queries', Set.fromList evidence')

    computeGroundings :: Seq AST.RuleBodyElement -> GState ()
    computeGroundings todo = do
        todo' <- Seq.filter ((/= False3) . snd) <$> forM todo (\g -> (g,) <$> goalHaveToProof g)
        let (prefix, postfix) = Seq.breakl ((== True3) . snd) todo'
        case Seq.viewl postfix of
            (nextGoal, _) :< todoRest -> computeGroundingsGoal nextGoal (fst <$> prefix >< todoRest)
            Seq.EmptyL -> do
                let (prefix', postfix') = Seq.breakl ((== Unknown3) . snd) todo'
                case Seq.viewl postfix' of
                    (nextGoal, _) :< todoRest -> computeGroundingsGoal nextGoal (fst <$> prefix' >< todoRest)
                    Seq.EmptyL                -> addGroundings -- no goal left

    goalHaveToProof :: AST.RuleBodyElement -> GState Bool3
    goalHaveToProof (AST.BuildInPredicate _) = return True3
    goalHaveToProof (AST.UserPredicate label givenArgs) = do
        let nGivenArgs = length givenArgs
        rsInProof <- gets rulesInProof
        gRules    <- gets groundedRules
        let inCurProof = case Map.lookup (label, nGivenArgs) rsInProof of
                Nothing -> False3
                Just rs -> foldl'
                    (\inProof (args, _, _) -> inProof ||* compareArgs args)
                    False3
                    rs
                where
                compareArgs args
                    | nGivenArgs == length args = foldl' (\eq (x, y) -> eq &&* compareArg x y) True3 $ zip givenArgs args
                    | otherwise = False3

                compareArg (AST.ConstantExpr x) (AST.ConstantExpr y) = if x == y then True3 else False3
                compareArg _                    _                    = Unknown3

        let allArgsGround = not $ any AST.varsInExpr givenArgs
        alreadyProven <- if allArgsGround then do
            args' <- lift $ toPropArgs givenArgs
            return $ if isJust $ Map.lookup (toPropPredLabel label  args') gRules
                then True3
                else False3
         else
            return False3
        return $ notB (inCurProof ||* alreadyProven)

    computeGroundingsGoal :: AST.RuleBodyElement -> Seq AST.RuleBodyElement -> GState ()
    computeGroundingsGoal goal remaining = case goal of
        AST.UserPredicate label givenArgs -> forM_ headRules continueWithChosenRule
            where
            headRules = Map.lookupDefault (error $ printf "head '%s/%i' undefined" (show label) nArgs) (label, nArgs) rules
            nArgs     = length givenArgs

            continueWithChosenRule :: ([AST.HeadArgument], AST.RuleBody) -> GState ()
            continueWithChosenRule (args, AST.RuleBody elements) = do
                oldSt <- get
                mbResult <- lift $ runMaybeT $ applyArgs givenArgs args elements
                case mbResult of
                    Just (els, valu, constrs) -> do
                        let valu' = Map.map AST.ConstantExpr valu
                        -- replace left-over (existentially quantified) vars
                        els' <- doState $ replaceEVars els
                        doState $ addRuleToProof els'
                        -- add newly found constraints to state
                        modify (\st -> st{proofConstraints = Set.union constrs $ proofConstraints st})
                        -- apply newly found variable values and check if proof is still consistent
                        consistent <- applyValuation valu' rfDefs
                        if consistent then do
                            -- also apply valuation found to remaining goals todo
                            remaining'      <- applyVal remaining valu'
                            -- continue with rest
                            computeGroundings (remaining' >< Seq.fromList els')
                            -- recover previous state for next head rule, but keep groundings found
                            modify (\newSt -> oldSt {groundedRules = groundedRules newSt})
                        else
                            put oldSt -- recover old state
                    Nothing -> put oldSt -- recover old state
                where
                addRuleToProof :: [AST.RuleBodyElement] -> State GroundingState ()
                addRuleToProof elements' = modify (\st -> st{rulesInProof = Map.insertWith
                    (\[x] -> (x :))
                    (label, nArgs)
                    [(givenArgs, AST.RuleBody elements', GroundedAST.RuleBody Set.empty)]
                    (rulesInProof st)
                })

        AST.BuildInPredicate bip -> case mbEquality of
            Just (var, expr) -> do
                oldSt <- get
                -- apply newly found variable substitution and check if proof is still consistent
                let valu = Map.singleton var expr
                consistent <- applyValuation  valu rfDefs
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
        applyVal :: Seq AST.RuleBodyElement -> HashMap AST.VarName AST.Expr -> GState (Seq AST.RuleBodyElement)
        applyVal goals valu = lift $ forM goals (\r -> AST.mapExprsInRuleBodyElementM
                r
                (applyValuArg valu)
                (return . snd . applyValuExpr valu)
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
        error $ printf "constraints could not be grounded: %s" $ show constrs
    where
    checkAllElementsGrounded :: ((AST.PredicateLabel, Int), [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody)])
                             -> Exceptional Exception (AST.PredicateLabel, Int, [([AST.Expr], GroundedAST.RuleBody)])
    checkAllElementsGrounded ((label, nArgs), bodies) = do
        bodies' <- forM bodies checkAllElementsGrounded'
        return (label, nArgs, bodies')
        where
        checkAllElementsGrounded' :: ([AST.Expr], AST.RuleBody, GroundedAST.RuleBody)
                                  -> Exceptional Exception ([AST.Expr], GroundedAST.RuleBody)
        checkAllElementsGrounded' (args, AST.RuleBody nonGroundBody, groundedBody)
            | null nonGroundBody = return (args, groundedBody)
            | otherwise          = throw $ NonGroundPreds nonGroundBody label nArgs

    addGroundingsHead :: (AST.PredicateLabel, Int, [([AST.Expr], GroundedAST.RuleBody)])
                      -> GState ()
    addGroundingsHead (label, _, bodies) = forM_ bodies addGroundingBody
        where
        addGroundingBody :: ([AST.Expr], GroundedAST.RuleBody)
                         -> GState ()
        addGroundingBody (args, groundedBody) = do
            args' <- lift $ toPropArgs args
            modify (\st -> st{groundedRules = Map.insertWith
                (\[x] -> (x :))
                (toPropPredLabel label args')
                [groundedBody]
                (groundedRules st)
            })

-- turn constructs from ordinary ones (with arguments) to propositional ones (after grounding)
toPropPredLabel :: AST.PredicateLabel -> [AST.ConstantExpr] -> GroundedAST.PredicateLabel
toPropPredLabel (AST.PredicateLabel label) args = GroundedAST.PredicateLabel $ printf
    "%s%s"
    label
    (if null args then "" else printf "(%s)" (showLst args))

toPropRFuncLabel :: AST.RFuncLabel -> [AST.ConstantExpr] -> GroundedAST.RFuncLabel
toPropRFuncLabel (AST.RFuncLabel label) args = GroundedAST.RFuncLabel $ printf
    "%s%s"
    label
    (if null args then "" else printf "(%s)" (showLst args))

-- precondition: no vars in expr
-- throws exception if there are RFs in expressions
toPropArgs :: [AST.Expr] -> Exceptional Exception [AST.ConstantExpr]
toPropArgs exprs = forM exprs toPropArg

-- precondition: no vars in expr
-- throws exception if there are RFs in expressions
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
        AST.RFunc _ _ -> throw RandomFuncUsedAsArg
        AST.Sum exprX exprY -> do
            exprX' <- toPropArgExpr exprX
            exprY' <- toPropArgExpr exprY
            return $ case (exprX', exprY') of
                (ExprReal exprX''', ExprReal exprY''') -> ExprReal $ GroundedAST.Sum exprX''' exprY'''
                (ExprInt  exprX''', ExprInt  exprY''') -> ExprInt  $ GroundedAST.Sum exprX''' exprY'''
                _                                      -> error "type error"
        AST.Variable _ -> error "precondition"

-- precondition: no vars left in rule element
toPropRuleElement :: AST.RuleBodyElement
                  -> HashMap (AST.RFuncLabel, Int) [([AST.HeadArgument], AST.RFuncDef)]
                  -> GState GroundedAST.RuleBodyElement
toPropRuleElement (AST.UserPredicate label args) _ = do
    args' <- lift $ toPropArgs args
    return $ GroundedAST.UserPredicate $ toPropPredLabel label args'
toPropRuleElement (AST.BuildInPredicate bip) rfDefs = GroundedAST.BuildInPredicate <$> toPropBuildInPred bip rfDefs

data PropExprWithType = ExprBool (GroundedAST.Expr Bool)
                      | ExprReal (GroundedAST.Expr GroundedAST.RealN)
                      | ExprStr  (GroundedAST.Expr String)
                      | ExprInt  (GroundedAST.Expr Integer)

instance Show PropExprWithType
    where
    show expr = printf "'%s' (of type %s)" exprStr typeStr
        where
        (exprStr, typeStr) = case expr of
            ExprBool expr' -> (show expr', "Bool")
            ExprReal expr' -> (show expr', "Real")
            ExprStr  expr' -> (show expr', "String")
            ExprInt  expr' -> (show expr', "Integer")

mapPropExprWithType :: (forall a. GroundedAST.Expr a -> GroundedAST.Expr a) -> PropExprWithType -> PropExprWithType
mapPropExprWithType f (ExprBool expr) = ExprBool $ f expr
mapPropExprWithType f (ExprReal expr) = ExprReal $ f expr
mapPropExprWithType f (ExprStr  expr) = ExprStr  $ f expr
mapPropExprWithType f (ExprInt  expr) = ExprInt  $ f expr

-- precondition: no vars left in 'bip'
toPropBuildInPred :: AST.BuildInPredicate
                  -> HashMap (AST.RFuncLabel, Int) [([AST.HeadArgument], AST.RFuncDef)]
                  -> GState GroundedAST.BuildInPredicate
toPropBuildInPred bip rfDefs = GroundedAST.simplifiedBuildInPred <$> case bip of
    AST.Equality eq exprX exprY -> toPropBuildInPred' (GroundedAST.Equality eq) exprX exprY
    AST.Ineq     op exprX exprY -> toPropBuildInPred' (GroundedAST.Ineq     op) exprX exprY
    where
    toPropBuildInPred' :: (forall a. GroundedAST.Expr a -> GroundedAST.Expr a -> GroundedAST.TypedBuildInPred a)
                       -> AST.Expr
                       -> AST.Expr
                       -> GState GroundedAST.BuildInPredicate
    toPropBuildInPred' bipConstructor exprX exprY = do
        exprX' <- toPropExpr exprX rfDefs
        exprY' <- toPropExpr exprY rfDefs
        case (exprX', exprY') of
            (ExprReal exprX'', ExprReal exprY'') -> return $ GroundedAST.BuildInPredicateReal $ bipConstructor exprX'' exprY''
            (ExprBool exprX'', ExprBool exprY'') -> return $ GroundedAST.BuildInPredicateBool $ bipConstructor exprX'' exprY''
            (ExprInt  exprX'', ExprInt  exprY'') -> return $ GroundedAST.BuildInPredicateInt  $ bipConstructor exprX'' exprY''
            (ExprStr  exprX'', ExprStr  exprY'') -> return $ GroundedAST.BuildInPredicateStr  $ bipConstructor exprX'' exprY''
            _                                    -> lift $ throw $ TypeError exprX' exprY'

-- precondition: no vars left in 'expr'
toPropExpr :: AST.Expr
           -> HashMap (AST.RFuncLabel, Int) [([AST.HeadArgument], AST.RFuncDef)]
           -> GState PropExprWithType
toPropExpr expr rfDefs = mapPropExprWithType GroundedAST.simplifiedExpr <$> case expr of
    AST.ConstantExpr cnst -> return $ toPropExprConst cnst
    AST.RFunc label args -> do
        gRfDefs <- gets groundedRfDefs
        propArgs <- lift $ toPropArgs args
        let propRFuncLabel = toPropRFuncLabel label propArgs
        rfDef <- case Map.lookup propRFuncLabel gRfDefs of
            Just def -> return def
            Nothing  -> do
                def <- lift $ rfDefFor label propArgs rfDefs
                modify (\st -> st{groundedRfDefs =
                    Map.insert propRFuncLabel def $ groundedRfDefs st
                })
                return def
        let rf = GroundedAST.makeRFunc propRFuncLabel rfDef
        case rfDef of
            AST.Flip _       -> return $ ExprBool $ GroundedAST.RFuncExpr rf
            AST.RealDist _ _ -> return $ ExprReal $ GroundedAST.RFuncExpr rf
    AST.Sum exprX exprY ->toPropExprPairAdd GroundedAST.Sum exprX exprY
        where
        toPropExprPairAdd :: (forall a. GroundedAST.Addition a => GroundedAST.Expr a -> GroundedAST.Expr a -> GroundedAST.Expr a)
                          -> AST.Expr
                          -> AST.Expr
                          -> GState PropExprWithType
        toPropExprPairAdd exprConstructor exprX' exprY' = do
            exprX'' <- toPropExpr exprX' rfDefs
            exprY'' <- toPropExpr exprY' rfDefs
            case (exprX'', exprY'') of
                (ExprReal exprX''', ExprReal exprY''') -> return $ ExprReal $ exprConstructor exprX''' exprY'''
                (ExprInt  exprX''', ExprInt  exprY''') -> return $ ExprInt  $ exprConstructor exprX''' exprY'''
                _                                      -> lift $ throw $ TypeError exprX'' exprY''
    AST.Variable _ -> error "toPropExpr: precondition"

toPropExprConst :: AST.ConstantExpr -> PropExprWithType
toPropExprConst (AST.BoolConstant cnst) = ExprBool $ GroundedAST.ConstantExpr $ GroundedAST.BoolConstant cnst
toPropExprConst (AST.RealConstant cnst) = ExprReal $ GroundedAST.ConstantExpr $ GroundedAST.RealConstant cnst
toPropExprConst (AST.StrConstant  cnst) = ExprStr  $ GroundedAST.ConstantExpr $ GroundedAST.StrConstant  cnst
toPropExprConst (AST.IntConstant  cnst) = ExprInt  $ GroundedAST.ConstantExpr $ GroundedAST.IntConstant  cnst

applyArgs :: [AST.Expr]
          -> [AST.HeadArgument]
          -> [AST.RuleBodyElement]
          -> MaybeT (Exceptional Exception) ([AST.RuleBodyElement], HashMap AST.VarName AST.ConstantExpr, HashSet Constraint)
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
    applyArgs' :: Maybe (HashMap AST.VarName AST.Expr, HashMap AST.VarName AST.ConstantExpr, HashSet Constraint)
               -> (AST.Expr, AST.HeadArgument)
               -> Maybe (HashMap AST.VarName AST.Expr, HashMap AST.VarName AST.ConstantExpr, HashSet Constraint)
    applyArgs' mbVals' givenReqArg = do
        (intValu, extValu, constrs) <- mbVals'
        case givenReqArg of
            (AST.Variable var, AST.ArgConstant cnst) -> case Map.lookup var extValu of
                Just cnst' -> if cnst == cnst' then
                                  return (intValu, extValu, constrs)
                              else
                                  Nothing
                Nothing -> return (intValu, Map.insert var cnst extValu, constrs)
            (expr, AST.ArgVariable var) -> case Map.lookup var intValu of
                Just expr'  -> return (intValu, extValu, Set.insert (EqConstraint expr expr') constrs)
                Nothing -> return (Map.insert var expr intValu, extValu, constrs)
            (expr, AST.ArgConstant cnst) -> return (intValu, extValu, Set.insert (EqConstraint expr $ AST.ConstantExpr cnst) constrs)
            (_, AST.ArgDontCareVariable) -> return (intValu, extValu, constrs)

applyValuation :: HashMap AST.VarName AST.Expr
               -> HashMap (AST.RFuncLabel, Int) [([AST.HeadArgument], AST.RFuncDef)]
               -> GState Bool
applyValuation valu rfDefs = do
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
    applyValuRule :: HashMap (AST.PredicateLabel, Int) [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody)]
                  -> ((AST.PredicateLabel, Int), [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody)])
                  -> MaybeT GState (HashMap (AST.PredicateLabel, Int) [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody)])
    applyValuRule rules (signature, sigRules) = do
        sigRules' <- foldlM applyValu' [] sigRules
        return $ Map.insert signature sigRules' rules

    applyValu' :: [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody)]
               -> ([AST.Expr], AST.RuleBody, GroundedAST.RuleBody)
               -> MaybeT GState [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody)]
    applyValu' rules (args, AST.RuleBody elements, GroundedAST.RuleBody gElements) = do
        args' <- lift $ lift $ forM args $ applyValuArg valu
        (elements', gElements') <- foldlM applyValuBodyEl ([], gElements) elements
        return $ (args', AST.RuleBody elements', GroundedAST.RuleBody gElements') : rules

    applyValuBodyEl :: ([AST.RuleBodyElement], HashSet GroundedAST.RuleBodyElement)
                    -> AST.RuleBodyElement
                    -> MaybeT GState ([AST.RuleBodyElement], HashSet GroundedAST.RuleBodyElement)
    applyValuBodyEl (elements, gElements) el = do
        let (varPresent, el') = AST.mapAccExprsInRuleBodyElement
                (\varPresent' expr -> let (varPresent'', expr') = applyValuExpr valu expr
                                      in  (varPresent' || varPresent'', expr')
                )
                False
                el
        if varPresent then
            return (el' : elements, gElements)
        else do
            gEl <- lift $ toPropRuleElement el' rfDefs
            case gEl of
                GroundedAST.BuildInPredicate bip -> case GroundedAST.deterministicValue bip of
                    Just True  -> return (elements, gElements)                -- true predicate can just be left out
                    Just False -> mzero                                       -- false predicate means proof becomes inconsistent
                    Nothing    -> return (elements, Set.insert gEl gElements) -- truthfullness depends on random functions
                _ -> return (elements, Set.insert gEl gElements)

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
    replaceEVars' :: (Integer, HashMap String Integer) -> AST.Expr -> ((Integer, HashMap String Integer), AST.Expr)
    replaceEVars' (counter, vars2ids) expr = case expr of
        AST.Variable (AST.VarName var) -> case Map.lookup var vars2ids of
            Just i  -> ((counter, vars2ids), AST.Variable $ AST.TempVar i)
            Nothing -> ((succ counter, Map.insert var counter vars2ids), AST.Variable $ AST.TempVar counter)
        otherExpr -> ((counter, vars2ids), otherExpr)

rfDefFor :: AST.RFuncLabel
         -> [AST.ConstantExpr]
         -> HashMap (AST.RFuncLabel, Int) [([AST.HeadArgument], AST.RFuncDef)]
         -> Exceptional Exception AST.RFuncDef
rfDefFor label args rfDefs = do
    defs <- exceptionalFromMaybe (UndefinedRf label nArgs) $ Map.lookup (label, nArgs) rfDefs
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
-- throws exception if RF is included in constr
constraintHolds :: Constraint -> Exceptional Exception Bool
constraintHolds (EqConstraint exprX exprY) =  do
    cnstX <- toPropArg exprX
    cnstY <- toPropArg exprY
    return $ case (cnstX, cnstY) of
        (AST.BoolConstant x, AST.BoolConstant y) -> x == y
        (AST.RealConstant x, AST.RealConstant y) -> x == y
        (AST.IntConstant  x, AST.IntConstant  y) -> x == y
        (AST.StrConstant  x, AST.StrConstant  y) -> x == y
        _                                        -> error $ printf "Types of expressions %s and %s do not match." (show exprX) (show exprY)
