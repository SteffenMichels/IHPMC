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

module Formula
    ( Formula
    , Node(..)
    , NodeType(..)
    , NodeRef(..) -- TODO: constructors should not be exposed
    , refBuildInPredicate
    , RefWithNode(entryRef,entryNode,entryRFuncs,entryCachedInfo)
    , CacheComputations(..)
    , ComposedId(..)
    , Conditions(..)
    , PropPredicateLabel(..)
    , PropRFunc(..)
    , PropRFuncLabel(..)
    , PropBuildInPredicate(..)
    , TypedPropBuildInPred(..)
    , PropExpr(..)
    , PropConstantExpr(..)
    , RealN
    , Addition
    , FState
    , negatePred
    , predRandomFunctions
    , exprRandomFunctions
    , checkRealIneqPred
    , empty
    , insert
    , augmentWithEntry
    , labelId
    , exportAsDot
    , uncondComposedLabel
    , conditionBool
    , conditionReal
    , Formula.negate
    , entryChoices
    ) where
import BasicTypes
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import System.IO
import Exception
import Data.Maybe (fromJust, fromMaybe)
import Text.Printf (printf)
import qualified Data.Foldable as Foldable
import qualified AST
import GHC.Generics (Generic)
import Data.Hashable (Hashable)
import qualified Data.Hashable as Hashable
import qualified Data.List as List
import Interval (Interval, (~<), (~>), (~<=), (~>=))
import qualified Interval
import Data.Char (toLower)
import Numeric (fromRat)
import Control.Monad.State.Strict

-- INTERFACE
data Node = Composed NodeType (HashSet NodeRef)
          | BuildInPredicate PropBuildInPredicate (HashMap PropRFunc Interval) -- store only real choices, as bool choices eliminate rfs
          | Deterministic Bool
          deriving (Show, Eq)

data RefWithNode cachedInfo = RefWithNode
    { entryRef        :: NodeRef
    , entryNode       :: Node
    , entryLabel      :: Maybe ComposedLabel
    , entryRFuncs     :: HashSet PropRFunc
    , entryCachedInfo :: cachedInfo
    } deriving (Eq)
instance Hashable (RefWithNode cachedInfo)
    where
    hash                                    = Hashable.hashWithSalt 0
    hashWithSalt salt RefWithNode{entryRef} = Hashable.hashWithSalt salt entryRef

type FState cachedInfo = State (Formula cachedInfo)

empty :: CacheComputations cachedInfo -> Formula cachedInfo
empty cacheComps = Formula { nodes        = Map.empty
                           , freshCounter = 0
                           , labels2ids   = Map.empty
                           , buildinCache = Map.empty
                           , cacheComps   = cacheComps
                           }

insert :: (Hashable cachedInfo, Eq cachedInfo)
       => Either ComposedLabel Conditions
       -> Bool
       -> NodeType
       -> HashSet NodeRef
       -> FState cachedInfo (RefWithNode cachedInfo)
insert labelOrConds sign op children = do
    (simplifiedNode, simplifiedSign) <- simplify op children
    children' <- foldM
        (\cs c -> do
            e <- augmentWithEntry c
            return $ Set.insert e cs
        )
        Set.empty
        (nodeChildren simplifiedNode)
    Formula{cacheComps, freshCounter, labels2ids, nodes} <- get
    let cachedInfo = cachedInfoComposed cacheComps (Set.map entryCachedInfo children')
    case simplifiedNode of
        Composed nType nChildren -> do
            let label = case labelOrConds of
                    Left label' -> label'
                    Right conds -> let label' = PropPredicateLabel $ show freshCounter
                                   in  ComposedLabel label' conds $ Hashable.hash label' -- only use label as hash (ignore conds) as node is unique anyhow
            let rFuncs = case simplifiedNode of
                    Deterministic _        -> Set.empty
                    BuildInPredicate prd _ -> predRandomFunctions prd
                    Composed _ _           -> Set.foldr (\child rfuncs -> Set.union rfuncs $ entryRFuncs child) Set.empty children'
            modify (\f -> f{ nodes        = Map.insert (ComposedId freshCounter) (label, FormulaEntry nType nChildren rFuncs cachedInfo) nodes
                           , freshCounter = succ freshCounter
                           , labels2ids   = Map.insert label (ComposedId freshCounter) labels2ids
                           }
                   )
            return RefWithNode { entryRef        = RefComposed (sign == simplifiedSign) $ ComposedId freshCounter
                               , entryNode       = simplifiedNode
                               , entryLabel      = Just label
                               , entryRFuncs     = rFuncs
                               , entryCachedInfo = cachedInfo
                               }
        BuildInPredicate prd rConds -> return $ predRefWithNode (if sign then prd else negatePred prd) rConds cachedInfo
        Deterministic val           -> return $ deterministicRefWithNode (val == sign) cachedInfo
    where
    simplify :: NodeType -> HashSet NodeRef -> FState cachedInfo (Node, Bool)
    simplify operator childRefs = case nChildren of
        0 -> return (Deterministic filterValue, True)
        1 -> do
            let onlyChild = getFirst newChildRefs
                sign' = case onlyChild of
                    RefComposed sign'' _ -> sign''
                    _                    -> True
            e <- augmentWithEntry onlyChild
            return (entryNode e, sign')
        _ | Foldable.any (RefDeterministic singleDeterminismValue ==) childRefs  ->
            return (Deterministic singleDeterminismValue, True)
        _ ->
            return (Composed operator newChildRefs, True)
        where
        newChildRefs = Set.filter (RefDeterministic filterValue /=) childRefs
        nChildren    = Set.size newChildRefs
        -- truth value that causes determinism if at least a single child has it
        singleDeterminismValue = operator == Or
        -- truth value that can be filtered out
        filterValue = operator == And

    nodeChildren :: Node -> HashSet NodeRef
    nodeChildren (Composed _ children'') = children''
    nodeChildren _                       = Set.empty

augmentWithEntry :: NodeRef -> FState cachedInfo (RefWithNode cachedInfo)
augmentWithEntry label = fromMaybe (error $ printf "Formula: non-existing Formula node '%s'" $ show label)
                         <$>
                         tryAugmentWithEntry label

tryAugmentWithEntry :: NodeRef -> FState cachedInfo (Maybe (RefWithNode cachedInfo))
tryAugmentWithEntry ref@(RefComposed _ i) = do
    Formula{nodes} <- get
    case Map.lookup i nodes of
        Just (label, FormulaEntry nType nChildren rFuncs cachedInfo) -> return $ Just RefWithNode
            { entryRef        = ref
            , entryNode       = Composed nType nChildren
            , entryLabel      = Just label
            , entryRFuncs     = rFuncs
            , entryCachedInfo = cachedInfo
            }
        Nothing -> return Nothing
tryAugmentWithEntry (RefBuildInPredicate prd prevChoicesReal) = state (\f@Formula{buildinCache, cacheComps} ->
        let (cachedInfo, buildinCache') = cachedInfoBuildInPredCached prevChoicesReal prd (cachedInfoBuildInPred cacheComps) buildinCache
        in  (Just $ predRefWithNode prd prevChoicesReal cachedInfo, f {buildinCache=buildinCache'})
    )
tryAugmentWithEntry (RefDeterministic val) = do
    Formula{cacheComps} <- get
    return $ Just $ deterministicRefWithNode val $ cachedInfoDeterministic cacheComps val

predRefWithNode :: PropBuildInPredicate -> HashMap PropRFunc Interval -> cachedInfo -> RefWithNode cachedInfo
predRefWithNode prd prevChoicesReal cachedInfo = RefWithNode
    { entryRef        = RefBuildInPredicate prd prevChoicesReal
    , entryNode       = BuildInPredicate prd prevChoicesReal
    , entryLabel      = Nothing
    , entryRFuncs     = rFuncs
    , entryCachedInfo = cachedInfo
    }
    where
        rFuncs = predRandomFunctions prd

deterministicRefWithNode :: Bool -> cachedInfo -> RefWithNode cachedInfo
deterministicRefWithNode val cachedInfo = RefWithNode
    { entryRef        = RefDeterministic val
    , entryNode       = Deterministic val
    , entryLabel      = Nothing
    , entryRFuncs     = Set.empty
    , entryCachedInfo = cachedInfo
    }

entryChoices :: RefWithNode cachedInfo -> Conditions
entryChoices entry = case entryRef entry of
    RefBuildInPredicate _ choices -> Conditions Map.empty choices
    _ -> case entryLabel entry of
        Just (ComposedLabel _ conds _) -> conds
        _ -> Conditions Map.empty Map.empty

conditionBool :: (Hashable cachedInfo, Eq cachedInfo)
              => RefWithNode cachedInfo
              -> PropRFunc
              -> Bool
              -> FState cachedInfo (RefWithNode cachedInfo)
conditionBool origNodeEntry rf val
    | not $ Set.member rf $ entryRFuncs origNodeEntry = return origNodeEntry
    | otherwise = case entryRef origNodeEntry of
        RefComposed sign origId -> do
            Formula{labels2ids, nodes} <- get
            case Map.lookup newLabel labels2ids of
                Just nodeId -> augmentWithEntry $ RefComposed sign nodeId
                _ -> do
                    let (_, FormulaEntry op children _ _) = fromJust $ Map.lookup origId nodes
                    condChildren <- foldM
                        (\children' child -> do
                            condRef   <- augmentWithEntry child
                            condChild <- conditionBool condRef rf val
                            return $ Set.insert condChild children'
                        )
                        Set.empty
                        children
                    insert (Left newLabel) sign op $ Set.map entryRef condChildren
            where
            newLabel = condComposedLabelBool rf val $ fromJust $ entryLabel origNodeEntry
        RefBuildInPredicate prd prevChoicesReal -> do
            Formula{cacheComps, buildinCache} <- get
            case deterministicValue condPred of
                Just val' -> return $ deterministicRefWithNode val' $ cachedInfoDeterministic cacheComps val'
                Nothing -> do
                    let (cachedInfo, buildinCache') = cachedInfoBuildInPredCached prevChoicesReal prd (cachedInfoBuildInPred cacheComps) buildinCache
                    modify (\f -> f {buildinCache=buildinCache'})
                    return $ predRefWithNode condPred prevChoicesReal cachedInfo
            where
            condPred = conditionPred prd
        RefDeterministic _ -> error "should not happen as deterministic nodes contain no rfunctions"
    where
        conditionPred :: PropBuildInPredicate -> PropBuildInPredicate
        conditionPred (BuildInPredicateBool (Equality eq exprL exprR)) = BuildInPredicateBool $ Equality eq (conditionExpr exprL) (conditionExpr exprR)
            where
            conditionExpr :: PropExpr Bool -> PropExpr Bool
            conditionExpr expr@(RFunc exprRFunc)
                | exprRFunc == rf = ConstantExpr $ BoolConstant val
                | otherwise       = expr
            conditionExpr expr = expr
        conditionPred prd = prd

conditionReal :: (Hashable cachedInfo, Eq cachedInfo)
              => RefWithNode cachedInfo
              -> PropRFunc
              -> Interval
              -> FState cachedInfo (RefWithNode cachedInfo)
conditionReal origNodeEntry rf interv
    | not $ Set.member rf $ entryRFuncs origNodeEntry = return origNodeEntry
    | otherwise = case entryRef origNodeEntry of
        RefComposed sign origLabel -> do
            Formula{labels2ids, nodes} <- get
            case Map.lookup newLabel labels2ids of
                Just nodeId -> augmentWithEntry $ RefComposed sign nodeId
                _ -> do
                    let (_, FormulaEntry op children _ _) = fromJust $ Map.lookup origLabel nodes
                    condChildren <- foldM
                        (\children' child -> do
                            condRef   <- Formula.augmentWithEntry child
                            condChild <- conditionReal condRef rf interv
                            return $ Set.insert condChild children'
                        )
                        Set.empty
                        children
                    insert (Left newLabel) sign op $ Set.map entryRef condChildren
            where
            newLabel = condComposedLabelReal rf interv $ fromJust $ entryLabel origNodeEntry
        RefBuildInPredicate prd prevChoicesReal -> do
            Formula{cacheComps, buildinCache} <- get
            case deterministicValue condPred of
                Just val -> return $ deterministicRefWithNode val $ cachedInfoDeterministic cacheComps val
                Nothing  -> do
                    let choices = Map.insert rf interv prevChoicesReal
                    let (cachedInfo, buildinCache') = cachedInfoBuildInPredCached choices prd (cachedInfoBuildInPred cacheComps) buildinCache
                    modify (\f -> f {buildinCache=buildinCache'})
                    return $ predRefWithNode condPred choices cachedInfo
            where
            condPred = conditionPred prd prevChoicesReal
        RefDeterministic _ -> error "should not happen as deterministic nodes contain no rfunctions"
    where
        conditionPred :: PropBuildInPredicate -> HashMap PropRFunc Interval -> PropBuildInPredicate
        conditionPred prd@(BuildInPredicateReal (Ineq op left right)) otherRealChoices
            -- check if choice is made for all 'rFuncs' in 'prd'
            | length conditions == Set.size predRFuncs = conditionPred'
            | otherwise = prd
            where
            conditionPred'
                | all ((==) $ Just True)  checkedPreds = BuildInPredicateReal $ Constant True
                | all ((==) $ Just False) checkedPreds = BuildInPredicateReal $ Constant False
                | otherwise                            = prd

            checkedPreds = map (checkRealIneqPred op left right) crns
            conditions   = (rf, interv):[(rf',interv') | (rf',interv') <- Map.toList otherRealChoices, Set.member rf' predRFuncs && rf' /= rf]
            crns         = Interval.corners conditions
            predRFuncs   = predRandomFunctions prd
        conditionPred prd _ = prd

negate :: NodeRef -> NodeRef
negate (RefComposed sign label)                  = RefComposed         (not sign) label
negate (RefBuildInPredicate prd prevChoicesReal) = RefBuildInPredicate (negatePred prd) prevChoicesReal
negate (RefDeterministic val)                    = RefDeterministic    (not val)

exportAsDot :: FilePath -> Formula cachedInfo -> ExceptionalT String IO ()
exportAsDot path Formula{nodes} = do
    file <- doIO (openFile path WriteMode)
    doIO (hPutStrLn file "digraph Formula {")
    forM_ (Map.toList nodes) (printNode file)
    doIO (hPutStrLn file "}")
    doIO (hClose file)
    where
        printNode :: Handle -> (ComposedId, (ComposedLabel, FormulaEntry cachedInfo)) -> ExceptionalT String IO ()
        printNode file (ComposedId i, (label, FormulaEntry op children _ _)) = do
            doIO (hPutStrLn file (printf "%i[label=\"%i: %s\\n%s\"];" i i (show label) descr))
            void $ forM_ children writeEdge
            where
                descr = case op of And -> "AND"; Or -> "OR"
                writeEdge childRef = doIO (hPutStrLn file (printf "%i->%s;" i (childStr childRef)))

                childStr :: NodeRef -> String
                childStr (RefComposed sign (ComposedId childId)) = printf "%i[label=\"%s\"]" childId (show sign)
                childStr (RefBuildInPredicate prd _)             = printf "%i;\n%i[label=\"%s\"]" h h $ show prd
                    where
                    h = Hashable.hashWithSalt i prd
                childStr (RefDeterministic _)              = error "Formula export: should this happen?"

-- FORMULA STORAGE
data Formula cachedInfo = Formula
    { nodes        :: HashMap ComposedId (ComposedLabel, FormulaEntry cachedInfo)           -- graph representing formulas
    , freshCounter :: Int                                                                   -- counter for fresh nodes
    , labels2ids   :: HashMap ComposedLabel ComposedId                                      -- map from composed label to composed ids (ids are used for performance, as ints are most effecient as keys in the graph map)
    , buildinCache :: HashMap (PropBuildInPredicate, HashMap PropRFunc Interval) cachedInfo -- cache for buildin predicates
    , cacheComps   :: CacheComputations cachedInfo                                          -- how cached information attached to formulas is computed
    }

newtype ComposedId = ComposedId Int deriving (Eq, Generic)
instance Hashable ComposedId

data ComposedLabel = ComposedLabel
    PropPredicateLabel -- the name
    Conditions         -- conditions
    Int                -- stored hash to avoid recomputation
    deriving (Eq)

-- propositional version of data types, similarly present in AST (without argument, after grounding)
newtype PropPredicateLabel = PropPredicateLabel String deriving (Eq, Generic)
instance Hashable PropPredicateLabel

data PropRFunc = PropRFunc PropRFuncLabel AST.RFuncDef
instance Eq PropRFunc
    where
    PropRFunc x _ == PropRFunc y _ = x == y
instance Show PropRFunc
    where
    show (PropRFunc l _ ) = show l
instance Hashable PropRFunc
    where
    hash = Hashable.hashWithSalt 0
    hashWithSalt salt (PropRFunc l _) = Hashable.hashWithSalt salt l

newtype PropRFuncLabel = PropRFuncLabel String deriving (Eq, Generic)
instance Show PropRFuncLabel
    where
    show (PropRFuncLabel l) = l
instance Hashable PropRFuncLabel

data PropBuildInPredicate = BuildInPredicateBool (TypedPropBuildInPred Bool)
                          | BuildInPredicateReal (TypedPropBuildInPred RealN)
                          | BuildInPredicateStr  (TypedPropBuildInPred String)
                          | BuildInPredicateInt  (TypedPropBuildInPred Integer)
                          deriving (Eq, Generic)
instance Show PropBuildInPredicate
    where
    show (BuildInPredicateBool b) = show b
    show (BuildInPredicateReal r) = show r
    show (BuildInPredicateStr  s) = show s
    show (BuildInPredicateInt  i) = show i
instance Hashable PropBuildInPredicate

data TypedPropBuildInPred a
    where
    Equality :: Bool       -> PropExpr a -> PropExpr a -> TypedPropBuildInPred a
    Ineq     :: AST.IneqOp -> PropExpr a -> PropExpr a -> TypedPropBuildInPred a
    Constant :: Bool                                   -> TypedPropBuildInPred a

deriving instance Eq (TypedPropBuildInPred a)
instance Show (TypedPropBuildInPred a)
    where
    show (Equality eq exprX exprY) = printf "%s %s %s" (show exprX) (if eq then "=" else "/=") (show exprY)
    show (Ineq     op exprX exprY) = printf "%s %s %s" (show exprX) (show op) (show exprY)
    show (Constant cnst)           = show cnst
instance Hashable (TypedPropBuildInPred a)
    where
    hash = Hashable.hashWithSalt 0
    hashWithSalt salt (Equality eq exprX exprY) = Hashable.hashWithSalt (Hashable.hashWithSalt (Hashable.hashWithSalt salt eq) exprX) exprY
    hashWithSalt salt (Ineq     op exprX exprY) = Hashable.hashWithSalt (Hashable.hashWithSalt (Hashable.hashWithSalt salt op) exprX) exprY
    hashWithSalt salt (Constant b)              = Hashable.hashWithSalt salt b

data PropExpr a
    where
    ConstantExpr ::               PropConstantExpr a       -> PropExpr a
    RFunc        ::               PropRFunc                -> PropExpr a -- type depends on user input, has to be typechecked at runtime
    Sum          :: Addition a => PropExpr a -> PropExpr a -> PropExpr a

deriving instance Eq (PropExpr a)
instance Show (PropExpr a)
    where
    show (ConstantExpr cExpr) = show cExpr
    show (RFunc label)        = printf "~%s" $ show label
    show (Sum x y)            = printf "%s + %s" (show x) (show y)
instance Hashable (PropExpr a)
    where
    hash = Hashable.hashWithSalt 0
    hashWithSalt salt (ConstantExpr cExpr) = Hashable.hashWithSalt salt cExpr
    hashWithSalt salt (RFunc r)            = Hashable.hashWithSalt salt r
    hashWithSalt salt (Sum x y)            = Hashable.hashWithSalt (Hashable.hashWithSalt salt x) y

data PropConstantExpr a
    where
    BoolConstant :: Bool     -> PropConstantExpr Bool
    RealConstant :: Rational -> PropConstantExpr RealN
    StrConstant  :: String   -> PropConstantExpr String
    IntConstant  :: Integer  -> PropConstantExpr Integer

deriving instance Eq (PropConstantExpr a)
instance Show (PropConstantExpr a)
    where
    show (BoolConstant cnst) = printf "%s" (toLower <$> show cnst)
    show (RealConstant cnst) = printf "%f" (fromRat cnst::Float)
    show (StrConstant  cnst) = cnst
    show (IntConstant  cnst) = show cnst
instance Hashable (PropConstantExpr a)
    where
    hash = Hashable.hashWithSalt 0
    hashWithSalt salt (BoolConstant b) = Hashable.hashWithSalt salt b
    hashWithSalt salt (RealConstant r) = Hashable.hashWithSalt salt r
    hashWithSalt salt (StrConstant  s) = Hashable.hashWithSalt salt s
    hashWithSalt salt (IntConstant  i) = Hashable.hashWithSalt salt i
instance Ord (PropConstantExpr a)
    where
    BoolConstant x <= BoolConstant y = x <= y
    RealConstant x <= RealConstant y = x <= y
    StrConstant  x <= StrConstant  y = x <= y
    IntConstant  x <= IntConstant  y = x <= y
    _              <= _              = error "Formula.Ord.PropConstantExpr"

data RealN -- phantom for real numbered expression etc.

class Addition a
instance Addition Integer
instance Addition RealN

predRandomFunctions :: PropBuildInPredicate -> HashSet PropRFunc
predRandomFunctions (BuildInPredicateBool b) = predRandomFunctions' b
predRandomFunctions (BuildInPredicateReal r) = predRandomFunctions' r
predRandomFunctions (BuildInPredicateStr  s) = predRandomFunctions' s
predRandomFunctions (BuildInPredicateInt  i) = predRandomFunctions' i

predRandomFunctions' :: TypedPropBuildInPred a -> HashSet PropRFunc
predRandomFunctions' (Equality _ left right) = Set.union (exprRandomFunctions left) (exprRandomFunctions right)
predRandomFunctions' (Ineq     _ left right) = Set.union (exprRandomFunctions left) (exprRandomFunctions right)
predRandomFunctions' (Constant _)            = Set.empty

exprRandomFunctions :: PropExpr t -> HashSet PropRFunc
exprRandomFunctions (RFunc label)    = Set.singleton label
exprRandomFunctions (ConstantExpr _) = Set.empty
exprRandomFunctions (Sum x y)        = Set.union (exprRandomFunctions x) (exprRandomFunctions y)

negatePred :: PropBuildInPredicate -> PropBuildInPredicate
negatePred (BuildInPredicateBool b) = BuildInPredicateBool $ negatePred' b
negatePred (BuildInPredicateReal r) = BuildInPredicateReal $ negatePred' r
negatePred (BuildInPredicateStr  s) = BuildInPredicateStr  $ negatePred' s
negatePred (BuildInPredicateInt  i) = BuildInPredicateInt  $ negatePred' i

negatePred' :: TypedPropBuildInPred a -> TypedPropBuildInPred a
negatePred' (Equality eq exprX exprY) = Equality (not eq) exprX exprY
negatePred' (Ineq     op exprX exprY) = Ineq (AST.negateOp op) exprX exprY
negatePred' (Constant cnst)           = Constant $ not cnst

deterministicValue :: PropBuildInPredicate -> Maybe Bool
deterministicValue (BuildInPredicateBool b) = deterministicValue' b
deterministicValue (BuildInPredicateReal r) = deterministicValue' r
deterministicValue (BuildInPredicateStr  s) = deterministicValue' s
deterministicValue (BuildInPredicateInt  i) = deterministicValue' i

deterministicValue' :: TypedPropBuildInPred a -> Maybe Bool
deterministicValue' (Equality eq (ConstantExpr left) (ConstantExpr right))   = Just $ (if eq then (==) else (/=)) left right
deterministicValue' (Equality eq (RFunc left) (RFunc right)) | left == right = Just eq
deterministicValue' (Ineq     op (ConstantExpr left) (ConstantExpr right))   = Just evalPred
    where
    evalPred = case op of
        AST.Lt   -> left <  right
        AST.LtEq -> left <= right
        AST.Gt   -> left >  right
        AST.GtEq -> left >= right
deterministicValue' (Constant val)                                           = Just val
deterministicValue' _                                                        = Nothing

checkRealIneqPred :: AST.IneqOp
                  -> PropExpr RealN
                  -> PropExpr RealN
                  -> Map.HashMap PropRFunc Interval.IntervalLimitPoint
                  -> Maybe Bool -- result may be undetermined -> Nothing
checkRealIneqPred op left right point = case op of
    AST.Lt   -> evalLeft ~<  evalRight
    AST.LtEq -> evalLeft ~<= evalRight
    AST.Gt   -> evalLeft ~>  evalRight
    AST.GtEq -> evalLeft ~>= evalRight
    where
    evalLeft  = eval left  point
    evalRight = eval right point

eval :: PropExpr RealN -> HashMap PropRFunc Interval.IntervalLimitPoint -> Interval.IntervalLimitPoint
eval (RFunc rf) point                  = Map.lookupDefault (error $ printf "AST.checkRealIneqPred: no point for %s" $ show rf) rf point
eval (ConstantExpr (RealConstant r)) _ = Interval.rat2IntervLimPoint r
eval (Sum x y) point                   = eval x point + eval y point

-- conditioned formulas
data Conditions = Conditions (HashMap PropRFunc Bool) (HashMap PropRFunc Interval)
    deriving (Eq)

instance Show ComposedLabel
    where
    show (ComposedLabel (PropPredicateLabel label) (Conditions bConds rConds) _) = printf
        "%s|%s"
        label
        (List.intercalate "," ((showCondBool <$> Map.toList bConds) ++ (showCondReal <$> Map.toList rConds)))
        where
            showCondBool (PropRFunc rf _, val) = printf "%s=%s" (show rf) (show val)

instance Hashable ComposedLabel
    where
    hash              (ComposedLabel _ _ hash) = hash
    hashWithSalt salt (ComposedLabel _ _ hash) = Hashable.hashWithSalt salt hash

uncondComposedLabel :: PropPredicateLabel -> ComposedLabel
uncondComposedLabel label = ComposedLabel label (Conditions Map.empty Map.empty) $ Hashable.hash label

condComposedLabelBool :: PropRFunc -> Bool -> ComposedLabel -> ComposedLabel
condComposedLabelBool rf val (ComposedLabel name (Conditions bConds rConds) hash) = ComposedLabel name (Conditions bConds' rConds) hash'
    where
    bConds' = Map.insert rf val bConds
    hash'   = hash + Hashable.hashWithSalt (Hashable.hash rf) val

condComposedLabelReal :: PropRFunc -> Interval -> ComposedLabel -> ComposedLabel
condComposedLabelReal rf interv (ComposedLabel name (Conditions bConds rConds) hash) = ComposedLabel name (Conditions bConds rConds') hash'
    where
    rConds' = Map.insert rf interv rConds
    hash'   = hash + Hashable.hashWithSalt (Hashable.hash rf) interv

labelId :: ComposedLabel -> FState cachednInfo (Maybe ComposedId)
labelId label = get >>= \Formula{labels2ids} -> return $ Map.lookup label labels2ids

-- the FormulaEntry contains composed node, plus additional, redundant, cached information to avoid recomputations
data FormulaEntry cachedInfo = FormulaEntry NodeType (HashSet NodeRef) (HashSet PropRFunc) cachedInfo

data NodeType = And | Or deriving (Eq, Show, Generic)
instance Hashable NodeType

-- node refs are used for optimisation, to avoid looking up leaves (build in preds and deterministic nodes) in the graph
data NodeRef = RefComposed Bool ComposedId
             | RefBuildInPredicate PropBuildInPredicate (HashMap PropRFunc Interval) -- store only real choices, as bool choices eliminate rfs
             | RefDeterministic Bool
             deriving (Eq, Generic)
instance Hashable NodeRef
instance Show NodeRef
    where
    show (RefComposed sign (ComposedId cid)) = printf "composed %s %i" (show sign) cid
    show (RefBuildInPredicate prd rConds)    = printf
                                                   "%s|\n  %s"
                                                   (show prd)
                                                   (List.intercalate ",\n" (showCondReal <$> Map.toList rConds))
    show (RefDeterministic val)              = show val

showCondReal :: (PropRFunc, Interval) -> String
showCondReal (rf, Interval.Interval l r) = printf "%s in (%s,%s)" (show rf) (show l) (show r)

refBuildInPredicate :: PropBuildInPredicate -> NodeRef
refBuildInPredicate prd = case deterministicValue simplifiedPrd of
    Just val -> RefDeterministic val
    Nothing  -> RefBuildInPredicate simplifiedPrd Map.empty
    where
    simplifiedPrd = case prd of
        BuildInPredicateBool prd' -> BuildInPredicateBool $ simplifiedPrd' prd'
        BuildInPredicateReal prd' -> BuildInPredicateReal $ simplifiedPrd' prd'
        BuildInPredicateInt  prd' -> BuildInPredicateInt  $ simplifiedPrd' prd'
        BuildInPredicateStr  prd' -> BuildInPredicateStr  $ simplifiedPrd' prd'

    simplifiedPrd' (Equality eq exprX exprY) = Equality eq (simplifiedExpr exprX) (simplifiedExpr exprY)
    simplifiedPrd' (Ineq     op exprX exprY) = Ineq     op (simplifiedExpr exprX) (simplifiedExpr exprY)
    simplifiedPrd' prd'                      = prd'

    simplifiedExpr (Sum exprX exprY) = case (simplifiedExpr exprX, simplifiedExpr exprY) of
        (ConstantExpr x, ConstantExpr y) -> ConstantExpr (add x y)
        (exprX',         exprY')         -> Sum exprX' exprY'
    simplifiedExpr expr              = expr

    add :: Addition a => PropConstantExpr a -> PropConstantExpr a -> PropConstantExpr a
    add (RealConstant x) (RealConstant y) = RealConstant (x + y)
    add (IntConstant  x) (IntConstant  y) = IntConstant  (x + y)
    add _                _                = error "Formula.refBuildInPredicate"

data CacheComputations cachedInfo = CacheComputations
    { cachedInfoComposed      :: HashSet cachedInfo                                 -> cachedInfo
    , cachedInfoBuildInPred   :: HashMap PropRFunc Interval -> PropBuildInPredicate -> cachedInfo
    , cachedInfoDeterministic :: Bool                                               -> cachedInfo
    }

-- to avoid recomputation
cachedInfoBuildInPredCached :: HashMap PropRFunc Interval
                            -> PropBuildInPredicate
                            -> (HashMap PropRFunc Interval -> PropBuildInPredicate -> cachedInfo)
                            -> HashMap (PropBuildInPredicate, HashMap PropRFunc Interval) cachedInfo
                            -> (cachedInfo, HashMap (PropBuildInPredicate, HashMap PropRFunc Interval) cachedInfo)
cachedInfoBuildInPredCached conds prd infoComp cache = case Map.lookup (prd,conds) cache of
    Just cachedInfo -> (cachedInfo, cache)
    Nothing         -> let cachedInfo = infoComp conds prd
                       in  (cachedInfo, Map.insert (prd,conds) cachedInfo cache)
