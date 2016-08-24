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
import Control.Arrow (second)
import Text.Printf (printf)
import Data.List (intercalate)
import Data.Foldable (foldl')
import Data.Traversable (mapAccumL, forM)
import Data.Sequence (Seq, ViewL((:<)), (><))
import qualified Data.Sequence as Seq
import Data.Maybe (isJust)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)

data Constraint = EqConstraint AST.Expr AST.Expr deriving (Eq, Generic, Show)
instance Hashable Constraint

data GroundingState = GroundingState
    { groundedRules    :: HashMap GroundedAST.PredicateLabel (HashSet GroundedAST.RuleBody)
    , groundedRfDefs   :: HashMap GroundedAST.RFuncLabel GroundedAST.RFuncDef
    , varCounter       :: Integer
    , rulesInProof     :: HashMap (AST.PredicateLabel, Int) (HashSet ([AST.Expr], AST.RuleBody))
    , proofConstraints :: HashSet Constraint
    } deriving Show

ground :: AST -> GroundedAST
ground AST.AST{AST.queries=queries, AST.evidence=mbEvidence, AST.rules=rules, AST.rFuncDefs=rfDefs} =
    GroundedAST{ rules    = groundedRules'
               , queries  = queries'
               , evidence = mbEvidence'
               }
    where
    queries'    = Set.map toPropPred     queries
    mbEvidence' =         toPropPred <$> mbEvidence
    toPropPred (label, args) = toPropPredLabel label $ toPropArgs args

    GroundingState{groundedRules = groundedRules'} = foldl'
        (\st (label,args) -> execState (computeGroundings $ Seq.singleton $ AST.UserPredicate label args) st)
        GroundingState{ groundedRules    = Map.empty
                      , groundedRfDefs   = Map.empty
                      , varCounter       = 0
                      , rulesInProof     = Map.empty
                      , proofConstraints = Set.empty
                      }
        (Set.union queries $ maybe Set.empty Set.singleton mbEvidence)

    computeGroundings :: Seq AST.RuleBodyElement -> State GroundingState ()
    computeGroundings todo = case Seq.viewl todo of
        Seq.EmptyL           -> addGroundings
        nextGoal :< todoRest -> computeGroundingsGoal nextGoal todoRest
    addGroundings :: State GroundingState ()
    addGroundings = do
        constraints <- gets proofConstraints
        when (all constraintHolds constraints) $ do
            rsInProof <- gets rulesInProof
            forM_ (Map.toList rsInProof) addGroundingsHead

    addGroundingsHead :: ((AST.PredicateLabel, Int), HashSet ([AST.Expr], AST.RuleBody))
                      -> State GroundingState ()
    addGroundingsHead ((label, _), bodies) = forM_ bodies addGroundingBody
        where
        addGroundingBody :: ([AST.Expr], AST.RuleBody)
                         -> State GroundingState ()
        addGroundingBody (args, body) = do
            groundedBody <- toPropRuleBody body rfDefs
            modify (\st -> st{groundedRules= Map.insertWith
                Set.union
                (toPropPredLabel label $ toPropArgs args)
                (Set.singleton groundedBody)
                (groundedRules st)
            })

    computeGroundingsGoal :: AST.RuleBodyElement -> Seq AST.RuleBodyElement -> State GroundingState ()
    computeGroundingsGoal goal remaining = case goal of
        AST.UserPredicate label givenArgs -> forM_ headRules continueWithChosenRule
            where
            headRules = Map.lookupDefault (error $ printf "head '%s/%i' undefined" (show label) nArgs) (label, nArgs) rules
            nArgs     = length givenArgs

            continueWithChosenRule :: ([AST.HeadArgument], AST.RuleBody) -> State GroundingState ()
            continueWithChosenRule (args, AST.RuleBody elements) = continueWithChoice givenArgs args elements remaining addGroundedRule

            addGroundedRule elements = modify (\st -> st{rulesInProof = Map.insertWith
                Set.union
                (label, nArgs)
                (Set.singleton (givenArgs, AST.RuleBody elements)) $ rulesInProof st
            })

        AST.BuildInPredicate bip -> if null predRfs then
                                        computeGroundings remaining
                                    else
                                        forM_ predRfs computeGroundingsRf
            where
            predRfs = AST.predRandomFunctions bip

            computeGroundingsRf :: (AST.RFuncLabel, [AST.Expr]) -> State GroundingState ()
            computeGroundingsRf (label, givenArgs) = forM_ defsForRf continueWithChosenDef
                where
                defsForRf = Map.lookupDefault (error $ printf "RF '%s/%i' undefined" (show label) nArgs) (label, nArgs) rfDefs
                nArgs     = length givenArgs

                continueWithChosenDef :: ([AST.HeadArgument], AST.RFuncDef) -> State GroundingState ()
                continueWithChosenDef (args, _) = continueWithChoice givenArgs args [] remaining (const $ return ())

    continueWithChoice :: [AST.Expr]
                       -> [AST.HeadArgument]
                       -> [AST.RuleBodyElement]
                       -> Seq AST.RuleBodyElement
                       -> ([AST.RuleBodyElement] -> State GroundingState ())
                       -> State GroundingState ()
    continueWithChoice givenArgs args elements remaining addGrounding = do
        oldSt <- get
        case applyArgs givenArgs args elements of
            Just (els, valu, constrs) -> do
                -- replace left-over (existentially quantified) vars
                els' <- replaceEVars els
                addGrounding els'
                -- add newly found constraints to state
                modify (\st -> st{proofConstraints = Set.union constrs $ proofConstraints st})
                -- apply newly found variable values and check if proof is still consistent
                consistent <- applyValuation valu
                if consistent then do
                    -- also apply valuation found to remaining goals todo
                    let remaining' = mapExprsInRuleBodyElement (applyValuExpr valu) <$> remaining
                    -- continue with rest
                    computeGroundings (remaining' >< Seq.fromList els')
                    -- recover previous state for next head rule, but keep groundings found
                    modify (\newSt -> oldSt {groundedRules = groundedRules newSt})
                else
                    put oldSt -- recover old state
            Nothing -> put oldSt -- recover old state

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

-- turn constructs from ordinary ones (with arguments) to propositional ones (after grounding)
toPropPredLabel :: AST.PredicateLabel -> [AST.ConstantExpr] -> GroundedAST.PredicateLabel
toPropPredLabel (AST.PredicateLabel label) args = GroundedAST.PredicateLabel $ printf
    "%s%s"
    label
    (if null args then "" else printf "(%s)" (intercalate "," $ show <$> args))

toPropRFuncLabel :: AST.RFuncLabel -> [AST.ConstantExpr] -> GroundedAST.RFuncLabel
toPropRFuncLabel (AST.RFuncLabel label) args = GroundedAST.RFuncLabel $ printf
    "%s%s"
    label
    (if null args then "" else printf "(%s)" (intercalate "," $ show <$> args))

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

toPropRuleBody :: AST.RuleBody
               -> HashMap (AST.RFuncLabel, Int) [([AST.HeadArgument], AST.RFuncDef)]
               -> State GroundingState GroundedAST.RuleBody
toPropRuleBody (AST.RuleBody elements) rfDefs = GroundedAST.RuleBody <$> forM elements toPropRuleElement
    where
    toPropRuleElement :: AST.RuleBodyElement -> State GroundingState GroundedAST.RuleBodyElement
    toPropRuleElement (AST.UserPredicate label args) =
        return $ GroundedAST.UserPredicate $ toPropPredLabel label $ toPropArgs args
    toPropRuleElement (AST.BuildInPredicate bip) = GroundedAST.BuildInPredicate <$> toPropBuildInPred bip rfDefs

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

toPropBuildInPred :: AST.BuildInPredicate
                  -> HashMap (AST.RFuncLabel, Int) [([AST.HeadArgument], AST.RFuncDef)]
                  -> State GroundingState GroundedAST.BuildInPredicate
toPropBuildInPred bip rfDefs = GroundedAST.simplifiedBuildInPred <$> case bip of
    AST.Equality eq exprX exprY -> toPropBuildInPred' (GroundedAST.Equality eq) exprX exprY
    AST.Ineq     op exprX exprY -> toPropBuildInPred' (GroundedAST.Ineq     op) exprX exprY
    where
    toPropBuildInPred' :: (forall a. GroundedAST.Expr a -> GroundedAST.Expr a -> GroundedAST.TypedBuildInPred a)
                       -> AST.Expr
                       -> AST.Expr
                       -> State GroundingState GroundedAST.BuildInPredicate
    toPropBuildInPred' bipConstructor exprX exprY = do
        exprX' <- toPropExpr exprX rfDefs
        exprY' <- toPropExpr exprY rfDefs
        return $ case (exprX', exprY') of
            (ExprReal exprX'', ExprReal exprY'') -> GroundedAST.BuildInPredicateReal $ bipConstructor exprX'' exprY''
            (ExprBool exprX'', ExprBool exprY'') -> GroundedAST.BuildInPredicateBool $ bipConstructor exprX'' exprY''
            (ExprInt  exprX'', ExprInt  exprY'') -> GroundedAST.BuildInPredicateInt  $ bipConstructor exprX'' exprY''
            (ExprStr  exprX'', ExprStr  exprY'') -> GroundedAST.BuildInPredicateStr  $ bipConstructor exprX'' exprY''
            _                                    -> error $ printf "Types of expressions %s and %s do not match." (show exprX') (show exprY')

toPropExpr :: AST.Expr
           -> HashMap (AST.RFuncLabel, Int) [([AST.HeadArgument], AST.RFuncDef)]
           -> State GroundingState PropExprWithType
toPropExpr expr rfDefs = mapPropExprWithType GroundedAST.simplifiedExpr <$> case expr of
    AST.ConstantExpr cnst -> return $ toPropExprConst cnst
    AST.RFunc label args -> do
        gRfDefs <- gets groundedRfDefs
        rfDef <- case Map.lookup propRFuncLabel gRfDefs of
            Just def -> return def
            Nothing  -> do
                let def = rfDefFor label propArgs rfDefs
                modify (\st -> st{groundedRfDefs =
                    Map.insert propRFuncLabel def $ groundedRfDefs st
                })
                return def
        let rf = GroundedAST.RFunc propRFuncLabel rfDef
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
                          -> State GroundingState PropExprWithType
        toPropExprPairAdd exprConstructor exprX' exprY' = do
            exprX'' <- toPropExpr exprX' rfDefs
            exprY'' <- toPropExpr exprY' rfDefs
            return $ case (exprX'', exprY'') of
                (ExprReal exprX''', ExprReal exprY''') -> ExprReal $ exprConstructor exprX''' exprY'''
                (ExprInt  exprX''', ExprInt  exprY''') -> ExprInt  $ exprConstructor exprX''' exprY'''
                _                                      -> error "type error"
    AST.Variable var -> error $ printf "Cannot determine ground value for variable '%s' in expression '%s'." (show var) "BIP"

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
        let elements' = mapExprsInRuleBodyElement (replaceVars intValu) <$> elements
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

    replaceVars :: HashMap AST.VarName AST.Expr -> AST.Expr -> AST.Expr
    replaceVars valu expr = case expr of
        AST.Variable var -> Map.lookupDefault expr var valu
        _                -> expr

applyValuation :: HashMap AST.VarName AST.ConstantExpr -> State GroundingState Bool
applyValuation valu = state (\st -> case mapAccumL applyValuRule True $ rulesInProof st of
        (True, rules) -> (True,  st{rulesInProof = rules, proofConstraints = Set.map applyValuConstraint $ proofConstraints st})
        (False, _)    -> (False, st)
    )
    where
    applyValuRule :: Bool
              -> HashSet ([AST.Expr], AST.RuleBody)
              -> (Bool, HashSet ([AST.Expr], AST.RuleBody))
    applyValuRule False _    = (False, error "Grounder: inconsistent rules")
    applyValuRule True rules = case foldl' applyValu' (Just Set.empty) rules of
        Just rules' -> (True,  rules')
        Nothing     -> (False, error "Grounder: inconsistent rules")

    applyValu' :: Maybe (HashSet ([AST.Expr], AST.RuleBody))
               -> ([AST.Expr], AST.RuleBody)
               -> Maybe (HashSet ([AST.Expr], AST.RuleBody))
    applyValu' mbRules (args, AST.RuleBody elements) = do
        rules <- mbRules
        let args' = applyValuExpr valu <$> args
        elements' <- foldl' applyValuBodyEl (Just []) elements
        return $ Set.insert (args', AST.RuleBody elements') rules

    applyValuBodyEl :: Maybe [AST.RuleBodyElement] -> AST.RuleBodyElement -> Maybe [AST.RuleBodyElement]
    applyValuBodyEl mbElements el = do
        elements <- mbElements
        return $ mapExprsInRuleBodyElement (applyValuExpr valu) el:elements

    applyValuConstraint :: Constraint -> Constraint
    applyValuConstraint (EqConstraint exprX exprY) = EqConstraint (applyValuExpr valu exprX) (applyValuExpr valu exprY)

applyValuExpr :: HashMap AST.VarName AST.ConstantExpr -> AST.Expr -> AST.Expr
applyValuExpr valu expr@(AST.Variable var) = case Map.lookup var valu of
    Just cnst -> AST.ConstantExpr cnst
    _         -> expr
applyValuExpr _ expr = expr

-- replace existentially quantified (occuring in body, but not head) variables
replaceEVars :: [AST.RuleBodyElement] -> State GroundingState [AST.RuleBodyElement]
replaceEVars elements = state (\st -> let ((varCounter', _), elements') = mapAccumL
                                              (mapAccExprsInRuleBodyElement replaceEVars')
                                              (varCounter st, Map.empty)
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
