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
import Data.Maybe (catMaybes, isJust)
import GHC.Generics (Generic)

type FState cachedInfo = State (Formula cachedInfo)
newtype Valuation = Valuation (HashMap AST.VarName AST.ObjectLabel) deriving (Show, Eq, Generic)
instance Hashable Valuation
data GroundingState = GroundingState
    { predGroundings :: HashMap (AST.PredicateLabel, Int) (HashSet [AST.ObjectLabel])
    , rfGroundings   :: HashMap (AST.RFuncLabel,     Int) (HashSet [AST.ObjectLabel])
    , varCount       :: Integer
    , valuation      :: Valuation
    , provenGoals    :: HashMap (AST.PredicateLabel, Int) (HashSet [AST.Argument])
    , rfsInProof     :: HashMap (AST.RFuncLabel,     Int) (HashSet [AST.Argument])
    }
    deriving Show

groundPclp :: (Eq cachedInfo, Hashable cachedInfo)
           => AST
           -> Formula.CacheComputations cachedInfo
           -> ((HashSet Formula.NodeRef, Maybe Formula.NodeRef), Formula cachedInfo)
groundPclp AST.AST {AST.queries=queries, AST.evidence=mbEvidence, AST.rules=rules, AST.rFuncDefs=rFuncDefs} cachedInfoComps =
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
        labelWithArgs = Formula.uncondComposedLabel $ toPropPredLabel label args Nothing
        headRules     = Map.lookupDefault (error $ printf "head '%s/%i' undefined" lStr nArgs) (label, nArgs) rules
        nArgs         = length args

    ruleFormulas :: (Eq cachedInfo, Hashable cachedInfo)
                 => AST.PredicateLabel
                 -> [AST.ObjectLabel]
                 -> (HashSet Formula.NodeRef, Int)
                 -> ([AST.Argument], AST.RuleBody)
                 -> FState cachedInfo (HashSet Formula.NodeRef, Int)
    ruleFormulas label givenArgs (fBodies, counter) (args, body) = case completeValuation <$> matchArgs givenArgs args of
        Nothing         -> return (fBodies, counter) -- given arguments do not match definition OR domain of other vars in rule is empty, do not add anything to set of bodies
        Just valuations -> foldrM (\val (fBodies', counter') -> do newChild <- bodyFormula (toPropPredLabel label givenArgs $ Just counter') body val
                                                                   return (Set.insert newChild fBodies', counter' + 1)
                                  )
                                  (fBodies, counter)
                                  valuations
        where
        -- valuations for all possible combination of values for vars not included in head valuation
        completeValuation :: Valuation -> HashSet Valuation
        completeValuation (Valuation valuation) = Set.map (Valuation . Map.union valuation) inBodyOnlyValuations
            where
            inBodyOnlyValuations = foldr updateDomains (Set.singleton Map.empty) bodyElements
            AST.RuleBody bodyElements = body

            updateDomains :: AST.RuleBodyElement -> HashSet (HashMap AST.VarName AST.ObjectLabel) -> HashSet (HashMap AST.VarName AST.ObjectLabel)
            updateDomains (AST.BuildInPredicate bip) doms = case bip of
                AST.Equality _ exprX exprY -> updateDomains'' exprX $ updateDomains'' exprY doms
                AST.RealIneq _ exprX exprY -> updateDomains'' exprX $ updateDomains'' exprY doms
                where
                updateDomains'' :: AST.Expr -> HashSet (HashMap AST.VarName AST.ObjectLabel) -> HashSet (HashMap AST.VarName AST.ObjectLabel)
                updateDomains'' (AST.ConstantExpr _)      doms' = doms'
                updateDomains'' (AST.RealSum exprX exprY) doms' = updateDomains'' exprX $ updateDomains'' exprY doms'
                updateDomains'' (AST.RFunc label' args')  doms' = Set.fromList $ updateDomains' label' args' (Set.toList doms') allRFGroundings
            updateDomains (AST.UserPredicate label' args') doms = Set.fromList $ updateDomains' label' args' (Set.toList doms)  allPredGroundings

            updateDomains' :: (Eq label, Hashable label)
                           => label
                           -> [AST.Argument]
                           -> [HashMap AST.VarName AST.ObjectLabel]
                           -> HashMap (label, Int) (HashSet [AST.ObjectLabel])
                           -> [HashMap AST.VarName AST.ObjectLabel]
            updateDomains' label' args' doms grnds = do
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
                          | grArgs <- Set.toList $ Map.lookupDefault Set.empty (label',length args') grnds
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
    elementFormula (AST.UserPredicate label args) valuation = headFormula (label, applyValuation valuation args False)
    elementFormula (AST.BuildInPredicate prd)     valuation = return $ Formula.RefBuildInPredicate (toPropBuildInPred prd valuation groundedRfDefs) Map.empty

    GroundingState{predGroundings = allPredGroundings, rfGroundings = allRFGroundings} = Set.foldr
        (\(label,args) -> execState $ allGroundings' $ Seq.singleton $ AST.UserPredicate label $ AST.Object <$> args)
        GroundingState{ predGroundings = Map.empty
                      , rfGroundings   = Map.empty
                      , varCount       = 0
                      , valuation      = Valuation Map.empty
                      , provenGoals    = Map.empty
                      , rfsInProof     = Map.empty
                      }
        (Set.union queries'$ maybe Set.empty Set.singleton mbEvidence')
        where
        allGroundings' :: Seq AST.RuleBodyElement -> State GroundingState ()
        allGroundings' todo = case Seq.viewl todo of
            Seq.EmptyL -> modify addGroundings
                where
                addGroundings st@GroundingState{predGroundings, provenGoals, rfGroundings, rfsInProof, valuation} =
                    st { predGroundings = Map.foldrWithKey addGroundingsHead predGroundings provenGoals
                       , rfGroundings   = Map.foldrWithKey addGroundingsRf   rfGroundings   rfsInProof
                       }
                    where
                    addGroundingsHead (label, nArgs) calls groundings' = foldr addGroundingCall groundings' calls
                        where
                        addGroundingCall args  = Map.insertWith Set.union (label, nArgs) (Set.singleton $ applyValuation valuation args True)
                    addGroundingsRf (label, nArgs) usages groundings' = foldr addGroundingUsage groundings' usages
                        where
                        addGroundingUsage args = Map.insertWith Set.union (label, nArgs) (Set.singleton $ applyValuation valuation args False)
            nextGoal :< todoRest -> case nextGoal of
                AST.BuildInPredicate bip -> if null predRfs then
                                                allGroundings' todoRest
                                            else
                                                forM_ predRfs allGroundings''
                    where
                    predRfs = AST.predRandomFunctions bip

                    allGroundings'' (label, givenArgs) = do
                        modify (\st -> st{rfsInProof = Map.insertWith Set.union (label, nArgs) (Set.singleton givenArgs) $ rfsInProof st})
                        forM_ rfDefs continueWithDef
                        where
                        rfDefs = Map.lookupDefault (error $ printf "RF '%s/%i' undefined" (show label) nArgs) (label, nArgs) rFuncDefs
                        nArgs  = length givenArgs

                        continueWithDef (args, _) = do
                            oldSt   <- get
                            mbMatch <- foldM (match undefined) (Just ()) $ zip givenArgs args
                            case mbMatch of
                                Just _ -> do
                                    -- continue with rest
                                    allGroundings' todoRest
                                    -- recover previous state for next head rule, but keep groundings found
                                    modify (\newSt -> oldSt {predGroundings = predGroundings newSt, rfGroundings = rfGroundings newSt})
                                Nothing -> put oldSt -- recover old state
                AST.UserPredicate label givenArgs -> do
                    modify (\st -> st{provenGoals = Map.insertWith Set.union (label,nArgs) (Set.singleton givenArgs) $ provenGoals st})
                    forM_ headRules continueWithRule
                    where
                    headRules = Map.lookupDefault (error $ printf "head '%s/%i' undefined" (show label) nArgs) (label, nArgs) rules
                    nArgs     = length givenArgs

                    continueWithRule (args, AST.RuleBody elements) = do
                        oldSt      <- get
                        mbElements <- foldM (match $ \x y -> fmap $ replace x y) (Just elements) (zip givenArgs args)
                        case mbElements of
                            Just els -> do
                                -- replace left-over (existentially quantified) vars
                                (els',_) <- foldM replaceEVars ([],Map.empty) els
                                -- continue with rest
                                allGroundings' (todoRest >< Seq.fromList els')
                                -- recover previous state for next head rule, but keep groundings found
                                modify (\newSt -> oldSt {predGroundings = predGroundings newSt, rfGroundings = rfGroundings newSt})
                            Nothing -> put oldSt -- recover old state

                    -- replace 'y' with 'x'
                    replace x y el = case el of
                        (AST.UserPredicate label' args) -> AST.UserPredicate label' $ replace' <$> args
                        (AST.BuildInPredicate bip)      -> AST.BuildInPredicate $ case bip of
                            AST.Equality eq exprX exprY -> AST.Equality   eq (replaceExpr exprX) (replaceExpr exprY)
                            AST.RealIneq op exprX exprY -> AST.RealIneq op (replaceExpr exprX) (replaceExpr exprY)
                        where
                        replace' arg = if arg == y then x else arg

                        replaceExpr :: AST.Expr -> AST.Expr
                        replaceExpr cnst@(AST.ConstantExpr _)      = cnst
                        replaceExpr      (AST.RealSum exprX exprY) = AST.RealSum (replaceExpr exprX) (replaceExpr exprY)
                        replaceExpr      (AST.RFunc label' args)   = AST.RFunc label' $ replace' <$> args

                    -- replace existentially quantified (occuring in body, but not head) variables
                    replaceEVars :: ([AST.RuleBodyElement], HashMap AST.VarName Integer)
                                 -> AST.RuleBodyElement
                                 -> State GroundingState ([AST.RuleBodyElement], HashMap AST.VarName Integer)
                    replaceEVars (els,vars2ids) (AST.BuildInPredicate bip) = do
                        (bip', vars2ids') <- case bip of
                            AST.Equality eq exprX exprY -> do
                                (exprX', vars2ids')  <- replaceEVarsExpr exprX vars2ids
                                (exprY', vars2ids'') <- replaceEVarsExpr exprY vars2ids'
                                return (AST.Equality eq exprX' exprY', vars2ids'')
                            AST.RealIneq op exprX exprY -> do
                                (exprX', vars2ids')  <- replaceEVarsExpr exprX vars2ids
                                (exprY', vars2ids'') <- replaceEVarsExpr exprY vars2ids'
                                return (AST.RealIneq op exprX' exprY', vars2ids'')
                        return (AST.BuildInPredicate bip':els, vars2ids')
                            where
                            replaceEVarsExpr :: AST.Expr -> HashMap AST.VarName Integer -> State GroundingState (AST.Expr, HashMap AST.VarName Integer)
                            replaceEVarsExpr cnst@(AST.ConstantExpr _)      vars2ids' = return (cnst, vars2ids')
                            replaceEVarsExpr      (AST.RealSum exprX exprY) vars2ids' = do
                                (exprX', vars2ids'')  <- replaceEVarsExpr exprX vars2ids'
                                (exprY', vars2ids''') <- replaceEVarsExpr exprY vars2ids''
                                return (AST.RealSum exprX' exprY', vars2ids''')
                            replaceEVarsExpr      (AST.RFunc label' args)   vars2ids' = do
                                (args', vars2ids'') <- foldM replaceEVarsArgs ([],vars2ids') $ reverse args
                                return (AST.RFunc label' args', vars2ids'')
                    replaceEVars (els,vars2ids) (AST.UserPredicate label' args) = do
                        (args', vars2ids') <- foldM replaceEVarsArgs ([],vars2ids) $ reverse args
                        return (AST.UserPredicate label' args':els, vars2ids')

                    replaceEVarsArgs :: ([AST.Argument], HashMap AST.VarName Integer)
                                     -> AST.Argument
                                     -> State GroundingState ([AST.Argument], HashMap AST.VarName Integer)
                    -- only replace variable which are not temporary (AST.VarName, but not AST.TempVar)
                    replaceEVarsArgs (args', vars2ids') (AST.Variable var@(AST.VarName _)) = case Map.lookup var vars2ids' of
                        Just i -> return ((AST.Variable $ AST.VarName $ show i):args', vars2ids')
                        Nothing -> do
                            i <- state (\st -> let i = varCount st in (i, st{varCount = i + 1}))
                            return ((AST.Variable $ AST.TempVar i):args', Map.insert var i vars2ids')
                    replaceEVarsArgs (args', vars2ids') arg = return (arg:args', vars2ids')
                where
                match :: (AST.Argument -> AST.Argument -> a -> a)
                      -> Maybe a
                      -> (AST.Argument, AST.Argument)
                      -> State GroundingState (Maybe a)
                match _       Nothing    _       = return Nothing
                match updFunc (Just els) argPair = case argPair of
                    (x,              y@(AST.Variable _)) -> return $ Just $ updFunc x y els
                    (AST.Object x,      AST.Object y)    -> return $ if x == y then Just els else Nothing
                    (AST.Variable x,    AST.Object y)    -> do
                        st <- get
                        let Valuation valu = valuation st
                        case Map.lookup x valu of
                            Just v  -> return $ if v == y then Just els else Nothing
                            Nothing -> put st{valuation = Valuation $ Map.insert x y valu} >>= \_ -> return $ Just els

    groundedRfDefs :: HashMap Formula.PropRFuncLabel AST.RFuncDef
    groundedRfDefs = Map.foldrWithKey addDef Map.empty allRFGroundings
        where
        addDef :: (AST.RFuncLabel, Int)
               -> HashSet [AST.ObjectLabel]
               -> HashMap Formula.PropRFuncLabel AST.RFuncDef
               -> HashMap Formula.PropRFuncLabel AST.RFuncDef
        addDef (label, nArgs) grnds defs = Set.foldr fstDef defs grnds
            where
            rfDefs = Map.lookupDefault (error "Grounder: RF not defined") (label, nArgs) rFuncDefs
            fstDef args defs' = case matchingDefs of
                []           -> error "Grounder: no matching RF def"
                ((_,fstD):_) -> Map.insert (toPropRFuncLabel label args) fstD defs'
                where
                matchingDefs = filter (\(defArgs, _) -> isJust $ matchArgs args defArgs) rfDefs

-- initial valuation based on matching given arguments with head/rf definition
matchArgs :: [AST.ObjectLabel] -> [AST.Argument] -> Maybe Valuation
matchArgs givenArgs args = Valuation <$> foldr match (Just Map.empty) (zip givenArgs args)
    where
    match (given, req) mbVal = do
        val <- mbVal
        case req of
            AST.Object cnst -> if given == cnst then return val
                                                else Nothing
            AST.Variable var -> case Map.lookup var val of
                                    Nothing                   -> return $ Map.insert var given val
                                    Just cnst | cnst == given -> return val
                                    _                         -> Nothing

-- turn constructs from ordinary ones (with arguments) to propositional ones (after grounding)
toPropPredLabel :: AST.PredicateLabel -> [AST.ObjectLabel] -> Maybe Int -> Formula.PropPredicateLabel
toPropPredLabel (AST.PredicateLabel label) objs mbInt = Formula.PropPredicateLabel $ printf
    "%s%s%s"
    label
    (if null objs then "" else printf "(%s)" (intercalate "," $ objLabelStr <$> objs))
    (maybe "" show mbInt)

data PropExprWithType = ExprBool (Formula.PropExpr Bool)
                      | ExprReal (Formula.PropExpr Formula.RealN)
                      | ExprStr  (Formula.PropExpr String)
                      | ExprInt  (Formula.PropExpr Integer)

instance Show PropExprWithType
    where
    show expr = printf "'%s' (of type %s)" exprStr typeStr
        where
        (exprStr, typeStr) = case expr of
            ExprBool expr' -> (show expr', "Bool")
            ExprReal expr' -> (show expr', "Real")
            ExprStr  expr' -> (show expr', "String")
            ExprInt  expr' -> (show expr', "Integer")

toPropBuildInPred :: AST.BuildInPredicate
                  -> Valuation
                  -> HashMap Formula.PropRFuncLabel AST.RFuncDef
                  -> Formula.PropBuildInPredicate
toPropBuildInPred bip valuation rfDefs = case bip of
    AST.Equality eq exprX exprY -> toPropBuildInPred'     (Formula.Equality eq) exprX exprY
    AST.RealIneq op exprX exprY -> toPropBuildInPredReal' (Formula.RealIneq op) exprX exprY
    where
    toPropBuildInPred' :: (forall a. Formula.PropExpr a -> Formula.PropExpr a -> Formula.TypedPropBuildInPred a)
                       -> AST.Expr
                       -> AST.Expr
                       -> Formula.PropBuildInPredicate
    toPropBuildInPred' bipConstructor exprX exprY = case (toPropExpr exprX, toPropExpr exprY) of
        (ExprReal exprX', ExprReal exprY') -> Formula.BuildInPredicateReal $ bipConstructor exprX' exprY'
        (ExprBool exprX', ExprBool exprY') -> Formula.BuildInPredicateBool $ bipConstructor exprX' exprY'
        (ExprInt  exprX', ExprInt  exprY') -> Formula.BuildInPredicateInt  $ bipConstructor exprX' exprY'
        (ExprStr  exprX', ExprStr  exprY') -> Formula.BuildInPredicateStr  $ bipConstructor exprX' exprY'
        (exprX',          exprY')          -> error $ printf "Types of expressions %s and %s do not match." (show exprX') (show exprY')

    toPropBuildInPredReal' :: (Formula.PropExpr Formula.RealN -> Formula.PropExpr Formula.RealN -> Formula.TypedPropBuildInPred Formula.RealN)
                           -> AST.Expr
                           -> AST.Expr
                           -> Formula.PropBuildInPredicate
    toPropBuildInPredReal' bipConstructor exprX exprY = case (toPropExpr exprX, toPropExpr exprY) of
        (ExprReal exprX', ExprReal exprY') -> Formula.BuildInPredicateReal $ bipConstructor exprX' exprY'
        _                                  -> error "type error"

    toPropExpr :: AST.Expr -> PropExprWithType
    toPropExpr (AST.ConstantExpr cnst) = toPropExprConst cnst
    toPropExpr (AST.RFunc label args)  = case Map.lookup propRFuncLabel rfDefs of
        Just def@(AST.Flip _)       -> ExprBool $ Formula.RFunc $ Formula.PropRFunc propRFuncLabel def
        Just def@(AST.RealDist _ _) -> ExprReal $ Formula.RFunc $ Formula.PropRFunc propRFuncLabel def
        Nothing                     -> error "Grounder: RF not found"
        where
        propRFuncLabel = toPropRFuncLabel label $ applyValuation valuation args False
    toPropExpr (AST.RealSum exprX exprY) = toPropExprPairReal Formula.RealSum exprX exprY

    toPropExprConst :: AST.ConstantExpr -> PropExprWithType
    toPropExprConst (AST.BoolConstant cnst) = ExprBool $ Formula.ConstantExpr $ Formula.BoolConstant cnst
    toPropExprConst (AST.RealConstant cnst) = ExprReal $ Formula.ConstantExpr $ Formula.RealConstant cnst
    toPropExprConst (AST.StrConstant  cnst) = ExprStr  $ Formula.ConstantExpr $ Formula.StrConstant  cnst
    toPropExprConst (AST.IntConstant  cnst) = ExprInt  $ Formula.ConstantExpr $ Formula.IntConstant  cnst

    toPropExprPairReal :: (Formula.PropExpr Formula.RealN -> Formula.PropExpr Formula.RealN -> Formula.PropExpr Formula.RealN)
                       -> AST.Expr
                       -> AST.Expr
                       -> PropExprWithType
    toPropExprPairReal exprConstructor exprX exprY = case (toPropExpr exprX, toPropExpr exprY) of
        (ExprReal exprX', ExprReal exprY') -> ExprReal $ exprConstructor exprX' exprY'
        _                                  -> error "type error"

toPropRFuncLabel :: AST.RFuncLabel -> [AST.ObjectLabel] -> Formula.PropRFuncLabel
toPropRFuncLabel (AST.RFuncLabel label) objs = Formula.PropRFuncLabel $ printf
    "%s%s"
    label
    (if null objs then "" else printf "(%s)" (intercalate "," $ objLabelStr <$> objs))

objLabelStr :: AST.ObjectLabel -> String
objLabelStr (AST.ObjectStr str) = str
objLabelStr (AST.ObjectInt int) = show int

applyValuation :: Valuation -> [AST.Argument] -> Bool -> [AST.ObjectLabel]
applyValuation (Valuation val) args placeholderObj = applyValuation' <$> args
    where
    applyValuation' (AST.Object l)   = l
    applyValuation' (AST.Variable v) = Map.lookupDefault defaultCnst v val
        where
        defaultCnst | placeholderObj = AST.ObjectStr "*"
                    | otherwise      = error $ printf "Grounder.groundElement: no valuation for variable '%s'" $ show v
