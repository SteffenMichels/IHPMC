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
import BasicTypes
import AST (AST)
import qualified AST
import GroundedAST (GroundedAST(..))
import qualified GroundedAST
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Control.Monad.State.Strict
import Control.Arrow (second)
import Text.Printf (printf)
import Data.Foldable (foldl', foldlM)
import Data.Traversable (mapAccumL)
import Data.Sequence (Seq, ViewL((:<)), (><))
import qualified Data.Sequence as Seq
import Data.Maybe (isJust)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Control.Monad.Trans.Maybe (MaybeT, runMaybeT)
import Exception

type GState = ExceptionalT Exception (State GroundingState)

data Exception = NonGroundPreds [AST.RuleBodyElement] AST.PredicateLabel Int
               deriving Eq

instance Show Exception
    where
    show (NonGroundPreds prds headLabel headNArgs) = printf
        "Could not ground predicate%s %s in a body of '%s/%i'."
        (if length prds > 1 then "s" else "")
        (showLstEnc "'" "'" prds)
        (show headLabel)
        headNArgs

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
    } deriving Show

ground :: AST -> Exceptional Exception GroundedAST
ground AST.AST{AST.queries=queries, AST.evidence=evidence, AST.rules=rules, AST.rFuncDefs=rfDefs} = evalState
    ground'
    GroundingState{ groundedRules    = Map.empty
                  , groundedRfDefs   = Map.empty
                  , varCounter       = 0
                  , rulesInProof     = Map.empty
                  , proofConstraints = Set.empty
                  }
    where
    ground' :: State GroundingState (Exceptional Exception GroundedAST)
    ground' = do
        mbRes <- computeResultState
        case mbRes of
            Success _ -> do
                groundedRules' <- gets groundedRules
                return $ Success $ GroundedAST { rules    = Map.map Set.fromList groundedRules'
                                               , queries  = Set.fromList queries'
                                               , evidence = Set.fromList evidence'
                                               }
            Exception e -> return $ Exception e

    computeResultState :: State GroundingState (Exceptional Exception ())
    computeResultState = runExceptionalT $ forM_ (queries ++ evidence) $
        \(label, args) -> computeGroundings $ Seq.singleton $ AST.UserPredicate label args

    queries'  = map toPropPred queries
    evidence' = map toPropPred evidence
    toPropPred (label, args) = toPropPredLabel label $ toPropArgs args

    computeGroundings :: Seq AST.RuleBodyElement -> GState ()
    computeGroundings todo = case Seq.viewl todo of
        Seq.EmptyL           -> addGroundings
        nextGoal :< todoRest -> computeGroundingsGoal nextGoal todoRest
    addGroundings :: GState ()
    addGroundings = do
        st <- lift get
        let constrs = proofConstraints st
        if null constrs then
            forM_ (Map.toList $ rulesInProof st) addGroundingsHead
        else
            error $ printf "constraints could not be grounded: %s" $ show constrs

    addGroundingsHead :: ((AST.PredicateLabel, Int), [([AST.Expr], AST.RuleBody, GroundedAST.RuleBody)])
                      -> GState ()
    addGroundingsHead ((label, nArgs), bodies) = forM_ bodies addGroundingBody
        where
        addGroundingBody :: ([AST.Expr], AST.RuleBody, GroundedAST.RuleBody)
                         -> GState ()
        addGroundingBody (args, AST.RuleBody nonGroundBody, groundedBody)
            | null nonGroundBody =
                lift $ modify (\st -> st{groundedRules= Map.insertWith
                    (\[x] -> (x :))
                    (toPropPredLabel label $ toPropArgs args)
                    [groundedBody]
                    (groundedRules st)
                })
            | otherwise = throwT $ NonGroundPreds nonGroundBody label nArgs

    computeGroundingsGoal :: AST.RuleBodyElement -> Seq AST.RuleBodyElement -> GState ()
    computeGroundingsGoal goal remaining = case goal of
        AST.UserPredicate label givenArgs -> forM_ headRules continueWithChosenRule
            where
            headRules = Map.lookupDefault (error $ printf "head '%s/%i' undefined" (show label) nArgs) (label, nArgs) rules
            nArgs     = length givenArgs

            continueWithChosenRule :: ([AST.HeadArgument], AST.RuleBody) -> GState ()
            continueWithChosenRule (args, AST.RuleBody elements) = do
                oldSt <- lift get
                case applyArgs givenArgs args elements of
                    Just (els, valu, constrs) -> do
                        let valu' = (Map.map AST.ConstantExpr valu)
                        -- replace left-over (existentially quantified) vars
                        els' <- lift $ replaceEVars els
                        lift $ addRuleToProof els'
                        -- add newly found constraints to state
                        lift $ modify (\st -> st{proofConstraints = Set.union constrs $ proofConstraints st})
                        -- apply newly found variable values and check if proof is still consistent
                        consistent <- applyValuation valu' rfDefs
                        if consistent then do
                            -- also apply valuation found to remaining goals todo
                            let remaining' = mapExprsInRuleBodyElement (snd . applyValuExpr valu') <$> remaining
                            -- continue with rest
                            computeGroundings (remaining' >< Seq.fromList els')
                            -- recover previous state for next head rule, but keep groundings found
                            lift $ modify (\newSt -> oldSt {groundedRules = groundedRules newSt})
                        else
                            lift $ put oldSt -- recover old state
                    Nothing -> lift $ put oldSt -- recover old state

            addRuleToProof :: [AST.RuleBodyElement] -> State GroundingState ()
            addRuleToProof elements = modify (\st -> st{rulesInProof = Map.insertWith
                (\[x] -> (x :))
                (label, nArgs)
                [(givenArgs, AST.RuleBody elements, GroundedAST.RuleBody Set.empty)]
                (rulesInProof st)
            })

        AST.BuildInPredicate bip -> case mbEquality of
            Just (var, expr) -> do
                oldSt <- lift get
                -- apply newly found variable substitution and check if proof is still consistent
                let valu = Map.singleton var expr
                consistent <- applyValuation  valu rfDefs
                if consistent then
                    -- also apply valuation found to remaining goals todo
                    computeGroundings $ mapExprsInRuleBodyElement (snd . applyValuExpr valu) <$> remaining
                else
                    lift $ put oldSt -- recover old state
            Nothing          -> computeGroundings remaining
            where
            mbEquality = case bip of
                AST.Equality True (AST.Variable var) expr -> Just (var, expr)
                AST.Equality True expr (AST.Variable var) -> Just (var, expr)
                _                                         -> Nothing

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

toPropArgs :: [AST.Expr] -> [AST.ConstantExpr]
toPropArgs exprs = toPropArg <$> exprs
    where
    toPropArg :: AST.Expr -> AST.ConstantExpr
    -- convert to grounded expr to perform simplification (e.g. for constant expr '1 + 1')
    toPropArg expr = case toPropExprWithoutRfs expr of
        ExprBool (GroundedAST.ConstantExpr (GroundedAST.BoolConstant cnst)) -> AST.BoolConstant cnst
        ExprReal (GroundedAST.ConstantExpr (GroundedAST.RealConstant cnst)) -> AST.RealConstant cnst
        ExprInt  (GroundedAST.ConstantExpr (GroundedAST.IntConstant cnst))  -> AST.IntConstant  cnst
        ExprStr  (GroundedAST.ConstantExpr (GroundedAST.StrConstant cnst))  -> AST.StrConstant  cnst
        expr'                                                               -> error $ printf "non constant expr '%s'" $ show expr'

-- precondition: no vars left in 'args'/'bip'
toPropRuleElement :: AST.RuleBodyElement
                  -> HashMap (AST.RFuncLabel, Int) [([AST.HeadArgument], AST.RFuncDef)]
                  -> GState GroundedAST.RuleBodyElement
toPropRuleElement (AST.UserPredicate label args) _ =
    return $ GroundedAST.UserPredicate $ toPropPredLabel label $ toPropArgs args
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
        return $ case (exprX', exprY') of
            (ExprReal exprX'', ExprReal exprY'') -> GroundedAST.BuildInPredicateReal $ bipConstructor exprX'' exprY''
            (ExprBool exprX'', ExprBool exprY'') -> GroundedAST.BuildInPredicateBool $ bipConstructor exprX'' exprY''
            (ExprInt  exprX'', ExprInt  exprY'') -> GroundedAST.BuildInPredicateInt  $ bipConstructor exprX'' exprY''
            (ExprStr  exprX'', ExprStr  exprY'') -> GroundedAST.BuildInPredicateStr  $ bipConstructor exprX'' exprY''
            _                                    -> error $ printf "Types of expressions %s and %s do not match." (show exprX') (show exprY')

-- precondition: no vars left in 'expr'
toPropExpr :: AST.Expr
           -> HashMap (AST.RFuncLabel, Int) [([AST.HeadArgument], AST.RFuncDef)]
           -> GState PropExprWithType
toPropExpr expr rfDefs = mapPropExprWithType GroundedAST.simplifiedExpr <$> case expr of
    AST.ConstantExpr cnst -> return $ toPropExprConst cnst
    AST.RFunc label args -> do
        gRfDefs <- lift $ gets groundedRfDefs
        rfDef <- case Map.lookup propRFuncLabel gRfDefs of
            Just def -> return def
            Nothing  -> do
                let def = rfDefFor label propArgs rfDefs
                lift $ modify (\st -> st{groundedRfDefs =
                    Map.insert propRFuncLabel def $ groundedRfDefs st
                })
                return def
        let rf = GroundedAST.makeRFunc propRFuncLabel rfDef
        case rfDef of
            AST.Flip _       -> return $ ExprBool $ GroundedAST.RFuncExpr rf
            AST.RealDist _ _ -> return $ ExprReal $ GroundedAST.RFuncExpr rf
        where
        propArgs       = toPropArgs args
        propRFuncLabel = toPropRFuncLabel label propArgs
    AST.Sum exprX exprY ->toPropExprPairAdd GroundedAST.Sum exprX exprY
        where
        toPropExprPairAdd :: (forall a. GroundedAST.Addition a => GroundedAST.Expr a -> GroundedAST.Expr a -> GroundedAST.Expr a)
                          -> AST.Expr
                          -> AST.Expr
                          -> GState PropExprWithType
        toPropExprPairAdd exprConstructor exprX' exprY' = do
            exprX'' <- toPropExpr exprX' rfDefs
            exprY'' <- toPropExpr exprY' rfDefs
            return $ case (exprX'', exprY'') of
                (ExprReal exprX''', ExprReal exprY''') -> ExprReal $ exprConstructor exprX''' exprY'''
                (ExprInt  exprX''', ExprInt  exprY''') -> ExprInt  $ exprConstructor exprX''' exprY'''
                _                                      -> error "type error"
    AST.Variable _ -> error "toPropExpr: precondition"

-- assumes that there are not RFs in expression
toPropExprWithoutRfs :: AST.Expr -> PropExprWithType
toPropExprWithoutRfs expr = mapPropExprWithType GroundedAST.simplifiedExpr $ case expr of
    AST.ConstantExpr cnst -> toPropExprConst cnst
    AST.RFunc _ _ -> error "assumed no RFs"
    AST.Sum exprX exprY -> toPropExprPairAdd GroundedAST.Sum exprX exprY
        where
        toPropExprPairAdd :: (forall a. GroundedAST.Addition a => GroundedAST.Expr a -> GroundedAST.Expr a -> GroundedAST.Expr a)
                          -> AST.Expr
                          -> AST.Expr
                          -> PropExprWithType
        toPropExprPairAdd exprConstructor exprX' exprY' = case (toPropExprWithoutRfs exprX', toPropExprWithoutRfs exprY') of
            (ExprReal exprX''', ExprReal exprY''') -> ExprReal $ exprConstructor exprX''' exprY'''
            (ExprInt  exprX''', ExprInt  exprY''') -> ExprInt  $ exprConstructor exprX''' exprY'''
            _                                      -> error "type error"
    AST.Variable var -> error $ printf "Cannot determine ground value for variable '%s' in expression '%s'." (show var) "BIP"

toPropExprConst :: AST.ConstantExpr -> PropExprWithType
toPropExprConst (AST.BoolConstant cnst) = ExprBool $ GroundedAST.ConstantExpr $ GroundedAST.BoolConstant cnst
toPropExprConst (AST.RealConstant cnst) = ExprReal $ GroundedAST.ConstantExpr $ GroundedAST.RealConstant cnst
toPropExprConst (AST.StrConstant  cnst) = ExprStr  $ GroundedAST.ConstantExpr $ GroundedAST.StrConstant  cnst
toPropExprConst (AST.IntConstant  cnst) = ExprInt  $ GroundedAST.ConstantExpr $ GroundedAST.IntConstant  cnst

applyArgs :: [AST.Expr]
          -> [AST.HeadArgument]
          -> [AST.RuleBodyElement]
          -> Maybe ([AST.RuleBodyElement], HashMap AST.VarName AST.ConstantExpr, HashSet Constraint)
applyArgs givenArgs args elements = do
        (intValu, extValu, constrs) <- mbVals
        let elements' = map (mapExprsInRuleBodyElement (replaceVars intValu)) elements
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

    replaceVars :: HashMap AST.VarName AST.Expr -> AST.Expr -> AST.Expr
    replaceVars valu expr = case expr of
        AST.Variable var -> Map.lookupDefault expr var valu
        _                -> expr

applyValuation :: HashMap AST.VarName AST.Expr
               -> HashMap (AST.RFuncLabel, Int) [([AST.HeadArgument], AST.RFuncDef)]
               -> GState Bool
applyValuation valu rfDefs = do
    st            <- lift get
    mbRules       <- runMaybeT $ foldlM applyValuRule Map.empty $ Map.toList $ rulesInProof st
    mbConstraints <- return $ foldlM applyValuConstraint Set.empty $ proofConstraints st
    let
    case (mbRules, mbConstraints) of
        (Just rules, Just constraints) -> do
            lift $ modify' (\st' -> st'{rulesInProof = rules, proofConstraints = constraints})
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
        let args' = snd . applyValuExpr valu <$> args
        (elements', gElements') <- foldlM applyValuBodyEl ([], gElements) elements
        return $ (args', AST.RuleBody elements', GroundedAST.RuleBody gElements') : rules

    applyValuBodyEl :: ([AST.RuleBodyElement], HashSet GroundedAST.RuleBodyElement)
                    -> AST.RuleBodyElement
                    -> MaybeT GState ([AST.RuleBodyElement], HashSet GroundedAST.RuleBodyElement)
    applyValuBodyEl (elements, gElements) el = do
        let (varPresent, el') = mapAccExprsInRuleBodyElement
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

    applyValuConstraint :: HashSet Constraint -> Constraint -> Maybe (HashSet Constraint)
    applyValuConstraint constraints (EqConstraint exprX exprY)
        | varsLeftX || varsLeftY = return $ Set.insert constr' constraints
        | holds                  = return constraints -- true constraint can just be left out
        | otherwise              = Nothing            -- false constraint means proof becomes inconsistent
        where
        constr' = EqConstraint exprX' exprY'
        holds   = constraintHolds constr'
        (varsLeftX, exprX') = applyValuExpr valu exprX
        (varsLeftY, exprY') = applyValuExpr valu exprY

-- returns whether still a non-valued variable is present
applyValuExpr :: HashMap AST.VarName AST.Expr -> AST.Expr -> (Bool, AST.Expr)
applyValuExpr valu expr@(AST.Variable var) = case Map.lookup var valu of
    Just expr' -> (not $ null $ AST.exprRandomFunctions expr', expr')
    _          -> (True,                                       expr)
applyValuExpr _ expr = (False, expr)

-- replace existentially quantified (occuring in body, but not head) variables
replaceEVars :: [AST.RuleBodyElement] -> State GroundingState [AST.RuleBodyElement]
replaceEVars elements = state (\st -> let (varCounter', _, elements') = foldl'
                                              (\(c, v2ids, elements'') el ->
                                                  let ((c', v2ids'), el') = mapAccExprsInRuleBodyElement replaceEVars' (c, v2ids) el
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
         -> AST.RFuncDef
rfDefFor label args rfDefs = case matchingDefs of
    []             -> error "Grounder: no matching RF def"
    ((_,fstDef):_) -> fstDef
    where
    defs = Map.lookupDefault (error "Grounder: RF not defined") (label, length args) rfDefs
    matchingDefs = filter (\(defArgs, _) -> matchArgs args defArgs) defs

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

constraintHolds :: Constraint -> Bool
constraintHolds (EqConstraint exprX exprY) =  case (toPropExprWithoutRfs exprX, toPropExprWithoutRfs exprY) of
    (ExprReal exprX', ExprReal exprY') -> checkEq exprX' exprY'
    (ExprBool exprX', ExprBool exprY') -> checkEq exprX' exprY'
    (ExprInt  exprX', ExprInt  exprY') -> checkEq exprX' exprY'
    (ExprStr  exprX', ExprStr  exprY') -> checkEq exprX' exprY'
    _                                  -> error $ printf "Types of expressions %s and %s do not match." (show exprX) (show exprY)
    where
    checkEq :: GroundedAST.Expr a -> GroundedAST.Expr a -> Bool
    checkEq (GroundedAST.ConstantExpr cnstX) (GroundedAST.ConstantExpr cnstY) = cnstX == cnstY
    checkEq _ _ = error "constraint could not be solved"

-- traverses top-down
mapExprsInRuleBodyElement :: (AST.Expr -> AST.Expr) -> AST.RuleBodyElement -> AST.RuleBodyElement
mapExprsInRuleBodyElement f el = snd $ mapAccExprsInRuleBodyElement (\a e -> (a, f e)) () el

mapAccExprsInRuleBodyElement :: (a -> AST.Expr -> (a, AST.Expr)) -> a -> AST.RuleBodyElement -> (a, AST.RuleBodyElement)
mapAccExprsInRuleBodyElement f acc el = case el of
    AST.UserPredicate label args -> second (AST.UserPredicate label) $ mapAccumL mapAccExpr acc args
    AST.BuildInPredicate bip -> second AST.BuildInPredicate $ case bip of
        AST.Equality eq exprX exprY -> let (acc',  exprX') = mapAccExpr acc  exprX
                                           (acc'', exprY') = mapAccExpr acc' exprY
                                       in  (acc'', AST.Equality eq exprX' exprY')
        AST.Ineq op exprX exprY     -> let (acc',  exprX') = mapAccExpr acc  exprX
                                           (acc'', exprY') = mapAccExpr acc' exprY
                                       in  (acc'', AST.Ineq op exprX' exprY')
    where
    mapAccExpr acc' expr = case expr' of
        AST.Sum exprX exprY -> let (acc''',  exprX') = f acc''  exprX
                                   (acc'''', exprY') = f acc''' exprY
                               in (acc'''', AST.Sum exprX' exprY')
        AST.RFunc label args -> second (AST.RFunc label) $ mapAccumL mapAccExpr acc'' args
        _ -> (acc'', expr')
        where
        (acc'', expr') = f acc' expr
