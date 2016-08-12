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
    , RefWithNode(entryRef,entryNode,entryRFuncs,entryCachedInfo)
    , CacheComputations(..)
    , ComposedId(..)
    , Conditions(..)
    , PropPredicateLabel(..)
    , PropRFuncLabel(..)
    , PropBuildInPredicate(..)
    , PropExpr(..)
    , PropConstantExpr(..)
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
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import System.IO
import Exception
import Control.Monad (void)
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
import Data.Foldable (forM_)
import Control.Arrow (first)
import Data.Char (toLower)
import Numeric (fromRat)

-- INTERFACE
data Node = Composed NodeType (HashSet NodeRef)
          | BuildInPredicate PropBuildInPredicate (HashMap PropRFuncLabel Interval) -- store only real choices, as bool choices eliminate rfs
          | Deterministic Bool
          deriving (Show, Eq)

data RefWithNode cachedInfo = RefWithNode
    { entryRef        :: NodeRef
    , entryNode       :: Node
    , entryLabel      :: Maybe ComposedLabel
    , entryRFuncs     :: HashSet PropRFuncLabel
    , entryCachedInfo :: cachedInfo
    } deriving (Eq)
instance Hashable (RefWithNode cachedInfo)
    where
    hash                                    = Hashable.hashWithSalt 0
    hashWithSalt salt RefWithNode{entryRef} = Hashable.hashWithSalt salt entryRef

insert :: (Hashable cachedInfo, Eq cachedInfo)
       => Either ComposedLabel Conditions
       -> Bool
       -> NodeType
       -> HashSet NodeRef
       -> Formula cachedInfo
       -> (RefWithNode cachedInfo, Formula cachedInfo)
insert labelOrConds sign op children f@Formula{nodes,labels2ids,freshCounter,cacheComps} = case simplifiedNode of
    Composed nType nChildren -> ( RefWithNode { entryRef        = RefComposed (sign == simplifiedSign) $ ComposedId freshId
                                              , entryNode       = simplifiedNode
                                              , entryLabel      = Just label
                                              , entryRFuncs     = rFuncs
                                              , entryCachedInfo = cachedInfo
                                              }
                                , f''         { nodes        = Map.insert (ComposedId freshId) (label, FormulaEntry nType nChildren rFuncs cachedInfo) nodes
                                              , freshCounter = freshId+1
                                              , labels2ids   = Map.insert label (ComposedId freshId) labels2ids
                                              }
                                )
    BuildInPredicate prd rConds -> (predRefWithNode (if sign then prd else negatePred prd) rConds cachedInfo, f'')
    Deterministic val           -> (deterministicRefWithNode (val == sign) cachedInfo, f'')
    where
    freshId = freshCounter
    label = case labelOrConds of
        Left label' -> label'
        Right conds -> let label' = PropPredicateLabel $ show freshId
                       in  ComposedLabel label' conds $ Hashable.hash label' -- only use label as hash (ignore conds) as node is unique anyhow
    (simplifiedNode, simplifiedSign, f') = simplify (Composed op children) f
    (children', f'') = Set.foldr (\c (cs,f''') -> first (`Set.insert` cs) $ augmentWithEntry c f''') (Set.empty,f') (nodeChildren simplifiedNode)
    rFuncs = case simplifiedNode of
        Deterministic _        -> Set.empty
        BuildInPredicate prd _ -> predRandomFunctions prd
        Composed _ _           -> Set.foldr (\child rfuncs -> Set.union rfuncs $ entryRFuncs child) Set.empty children'
    cachedInfo = cachedInfoComposed cacheComps (Set.map entryCachedInfo children')

    simplify :: Node -> Formula cachedInfo -> (Node, Bool, Formula cachedInfo)
    simplify node@(Deterministic _) f''' = (node, undefined, f''')
    simplify node@(BuildInPredicate prd _) f''' = case deterministicValue prd of
        Just val -> (Deterministic val, undefined, f''')
        Nothing  -> (node, undefined, f''')
    simplify (Composed operator childRefs) f''' = (simplified, sign', f'''')
        where
        sign' = case (nChildren, getFirst newChildRefs) of
            (1, RefComposed s _) -> s
            _                    -> True
        (simplified, f'''')
            | nChildren == 0 = (Deterministic filterValue, f''')
            | nChildren == 1 = first entryNode . (`augmentWithEntry` f''') $ getFirst newChildRefs
            | Foldable.any (RefDeterministic singleDeterminismValue ==) childRefs =
                (Deterministic singleDeterminismValue, f''')
            | otherwise = (Composed operator newChildRefs, f''')

        newChildRefs = Set.filter (RefDeterministic filterValue /=) childRefs
        nChildren    = Set.size newChildRefs
        -- truth value that causes determinism if at least a single child has it
        singleDeterminismValue = operator == Or
        -- truth value that can be filtered out
        filterValue = operator == And

    nodeChildren :: Node -> HashSet NodeRef
    nodeChildren (Composed _ children'') = children''
    nodeChildren _                       = Set.empty

augmentWithEntry :: NodeRef -> Formula cachedInfo -> (RefWithNode cachedInfo, Formula cachedInfo)
augmentWithEntry label f = ( fromMaybe
                                 (error $ printf "non-existing Formula node '%s'" $ show label)
                                 mbRef
                           , f' )
    where
    (mbRef, f') = tryAugmentWithEntry label f

tryAugmentWithEntry :: NodeRef -> Formula cachedInfo -> (Maybe (RefWithNode cachedInfo), Formula cachedInfo)
tryAugmentWithEntry ref@(RefComposed _ i) f@Formula{nodes} = case Map.lookup i nodes of
    Just (label, FormulaEntry nType nChildren rFuncs cachedInfo) -> (Just RefWithNode
        { entryRef        = ref
        , entryNode       = Composed nType nChildren
        , entryLabel      = Just label
        , entryRFuncs     = rFuncs
        , entryCachedInfo = cachedInfo
        }, f)
    Nothing                                                      -> (Nothing, f)
tryAugmentWithEntry (RefBuildInPredicate prd prevChoicesReal) f@Formula{buildinCache, cacheComps} =
    let (cachedInfo, buildinCache') = cachedInfoBuildInPredCached prevChoicesReal prd (cachedInfoBuildInPred cacheComps) buildinCache
    in  (Just $ predRefWithNode prd prevChoicesReal cachedInfo, f {buildinCache=buildinCache'})
tryAugmentWithEntry (RefDeterministic val)                    f@Formula{cacheComps} =
    (Just $ deterministicRefWithNode val $ cachedInfoDeterministic cacheComps val, f)

{-entryRefWithNode :: Bool -> ComposedId -> FormulaEntry cachedInfo -> RefWithNode cachedInfo
entryRefWithNode sign i (FormulaEntry op children rFuncs cachedInfo) = RefWithNode
    { entryRef        = RefComposed sign i
    , entryNode       = Composed op children
    , entryLabel      = Nothing
    , entryRFuncs     = rFuncs
    , entryCachedInfo = cachedInfo
    }-}

predRefWithNode :: PropBuildInPredicate -> HashMap PropRFuncLabel Interval -> cachedInfo -> RefWithNode cachedInfo
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
              -> PropRFuncLabel
              -> Bool
              -> Formula cachedInfo
              -> (RefWithNode cachedInfo, Formula cachedInfo)
conditionBool origNodeEntry rf val f@Formula{nodes, labels2ids, buildinCache, cacheComps}
    | not $ Set.member rf $ entryRFuncs origNodeEntry = (origNodeEntry, f)
    | otherwise = case entryRef origNodeEntry of
        RefComposed sign origId -> case Map.lookup newLabel labels2ids of
                                    Just nodeId -> augmentWithEntry (RefComposed sign nodeId) f
                                    _ -> let (_, FormulaEntry op children _ _) = fromJust $ Map.lookup origId nodes
                                             (condChildren, f') = Set.foldr
                                                (\child (children', f'') ->
                                                    let (condRef,   f''')  = Formula.augmentWithEntry child f''
                                                        (condChild, f'''') = conditionBool condRef rf val f'''
                                                    in  (Set.insert condChild children', f'''')
                                                )
                                                (Set.empty, f)
                                                children
                                         in  insert (Left newLabel) sign op (Set.map entryRef condChildren) f'
            where
            newLabel = condComposedLabelBool rf val $ fromJust $ entryLabel origNodeEntry
        RefBuildInPredicate prd prevChoicesReal -> case deterministicValue condPred of
            Just val' -> (deterministicRefWithNode val' $ cachedInfoDeterministic cacheComps val', f)
            Nothing   -> let (cachedInfo, buildinCache') = cachedInfoBuildInPredCached prevChoicesReal prd (cachedInfoBuildInPred cacheComps) buildinCache
                        in  (predRefWithNode condPred prevChoicesReal cachedInfo, f {buildinCache=buildinCache'})
            where
            condPred = conditionPred prd
        RefDeterministic _ -> error "should not happen as deterministic nodes contain no rfunctions"
    where
        conditionPred :: PropBuildInPredicate -> PropBuildInPredicate
        conditionPred (BoolEq eq exprL exprR) = BoolEq eq (conditionExpr exprL) (conditionExpr exprR)
            where
            conditionExpr expr@(RFunc exprRFuncLabel)
                | exprRFuncLabel == rf = ConstantExpr $ BoolConstant val
                | otherwise            = expr
            conditionExpr expr = expr
        conditionPred prd = prd

conditionReal :: (Hashable cachedInfo, Eq cachedInfo)
              => RefWithNode cachedInfo
              -> PropRFuncLabel
              -> Interval
              -> Formula cachedInfo
              -> (RefWithNode cachedInfo, Formula cachedInfo)
conditionReal origNodeEntry rf interv f@Formula{nodes, labels2ids, buildinCache, cacheComps}
    | not $ Set.member rf $ entryRFuncs origNodeEntry = (origNodeEntry, f)
    | otherwise = case entryRef origNodeEntry of
        RefComposed sign origLabel -> case Map.lookup newLabel labels2ids of
                                        Just nodeId -> augmentWithEntry (RefComposed sign nodeId) f
                                        _ -> let (_, FormulaEntry op children _ _) = fromJust $ Map.lookup origLabel nodes
                                                 (condChildren, f') = Set.foldr
                                                    (\child (children', f'') ->
                                                        let (condRef,   f''')  = Formula.augmentWithEntry child f''
                                                            (condChild, f'''') = conditionReal condRef rf interv f'''
                                                        in  (Set.insert condChild children', f'''')
                                                    )
                                                    (Set.empty, f)
                                                    children
                                             in insert (Left newLabel) sign op (Set.map entryRef condChildren) f'
            where
            newLabel = condComposedLabelReal rf interv $ fromJust $ entryLabel origNodeEntry
        RefBuildInPredicate prd prevChoicesReal -> case deterministicValue condPred of
            Just val -> (deterministicRefWithNode val $ cachedInfoDeterministic cacheComps val, f)
            Nothing  -> let choices = Map.insert rf interv prevChoicesReal
                            (cachedInfo, buildinCache') = cachedInfoBuildInPredCached choices prd (cachedInfoBuildInPred cacheComps) buildinCache
                        in  (predRefWithNode condPred choices cachedInfo, f {buildinCache=buildinCache'})
            where
            condPred = conditionPred prd prevChoicesReal
        RefDeterministic _ -> error "should not happen as deterministic nodes contain no rfunctions"
    where
        conditionPred :: PropBuildInPredicate -> HashMap PropRFuncLabel Interval -> PropBuildInPredicate
        conditionPred prd@(RealIneq op left right) otherRealChoices
            -- check if choice is made for all 'rFuncs' in 'prd'
            | length conditions == Set.size predRFuncs = conditionPred'
            | otherwise = prd
            where
            conditionPred'
                | all ((==) $ Just True)  checkedPreds = Constant True
                | all ((==) $ Just False) checkedPreds = Constant False
                | otherwise                            = prd

            checkedPreds = map (checkRealIneqPred op left right) crns
            conditions   = (rf, interv):[(rf',interv') | (rf',interv') <- Map.toList otherRealChoices, Set.member rf' predRFuncs && rf' /= rf]
            crns         = Interval.corners conditions
            predRFuncs   = predRandomFunctions prd
        conditionPred prd _ = prd

negate :: NodeRef -> NodeRef
negate (Formula.RefComposed sign label)                  = Formula.RefComposed         (not sign) label
negate (Formula.RefBuildInPredicate prd prevChoicesReal) = Formula.RefBuildInPredicate (negatePred prd) prevChoicesReal
negate (Formula.RefDeterministic val)                    = Formula.RefDeterministic    (not val)

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
    { nodes        :: HashMap ComposedId (ComposedLabel, FormulaEntry cachedInfo)            -- graph representing formulas
    , freshCounter :: Int                                                                    -- counter for fresh nodes
    , labels2ids   :: HashMap ComposedLabel ComposedId                                       -- map from composed label to composed ids (ids are used for performance, as ints are most effecient as keys in the graph map)
    , buildinCache :: HashMap (PropBuildInPredicate, HashMap PropRFuncLabel Interval) cachedInfo -- cache for buildin predicates
    , cacheComps   :: CacheComputations cachedInfo                                           -- how cached information attached to formulas is computed
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
newtype PropRFuncLabel = PropRFuncLabel String deriving (Eq, Show, Generic)
instance Hashable PropRFuncLabel

data PropBuildInPredicate = BoolEq Bool (PropExpr Bool)  (PropExpr Bool)
                          | RealIneq AST.IneqOp (PropExpr RealN) (PropExpr RealN)
                          | Constant Bool
                          deriving (Eq, Generic)

instance Show PropBuildInPredicate
    where
    show (BoolEq eq exprX exprY)   = printf "%s %s %s"  (show exprX) (if eq then "=" else "/=") (show exprY)
    show (RealIneq op exprX exprY) = printf "%s %s %s" (show exprX) (show op) (show exprY)
    show (Constant cnst)           = show cnst
instance Hashable PropBuildInPredicate

data PropExpr a
    where
    ConstantExpr :: PropConstantExpr a               -> PropExpr a
    RFunc        :: PropRFuncLabel                   -> PropExpr a -- type depends on user input, has to be typechecked at runtime
    RealSum      :: PropExpr RealN -> PropExpr RealN -> PropExpr RealN

deriving instance Eq (PropExpr a)
instance Show (PropExpr a)
    where
    show (ConstantExpr cExpr)           = show cExpr
    show (RFunc (PropRFuncLabel label)) = printf "~%s" label
    show (RealSum x y)                  = printf "%s + %s" (show x) (show y)
instance Hashable (PropExpr a)
    where
    hash = Hashable.hashWithSalt 0
    hashWithSalt salt (ConstantExpr cExpr) = Hashable.hashWithSalt salt cExpr
    hashWithSalt salt (RFunc r)            = Hashable.hashWithSalt salt r
    hashWithSalt salt (RealSum x y)        = Hashable.hashWithSalt (Hashable.hashWithSalt salt x) y

data PropConstantExpr a
    where
    BoolConstant :: Bool     -> PropConstantExpr Bool
    RealConstant :: Rational -> PropConstantExpr RealN

deriving instance Eq (PropConstantExpr a)
instance Show (PropConstantExpr a)
    where
    show (BoolConstant cnst) = printf "%s" (toLower <$> show cnst)
    show (RealConstant cnst) = printf "%f" (fromRat cnst::Float)
instance Hashable (PropConstantExpr a)
    where
    hash = Hashable.hashWithSalt 0
    hashWithSalt salt (BoolConstant b) = Hashable.hashWithSalt salt b
    hashWithSalt salt (RealConstant r) = Hashable.hashWithSalt salt r

predRandomFunctions :: PropBuildInPredicate -> HashSet PropRFuncLabel
predRandomFunctions (BoolEq _ left right)   = Set.union (exprRandomFunctions left) (exprRandomFunctions right)
predRandomFunctions (RealIneq _ left right) = Set.union (exprRandomFunctions left) (exprRandomFunctions right)
predRandomFunctions (Constant _)            = Set.empty

exprRandomFunctions :: PropExpr t -> HashSet PropRFuncLabel
exprRandomFunctions (RFunc label)    = Set.singleton label
exprRandomFunctions (ConstantExpr _) = Set.empty
exprRandomFunctions (RealSum x y)    = Set.union (exprRandomFunctions x) (exprRandomFunctions y)

negatePred :: PropBuildInPredicate -> PropBuildInPredicate
negatePred (BoolEq eq exprX exprY)   = BoolEq (not eq) exprX exprY
negatePred (RealIneq op exprX exprY) = RealIneq (AST.negateOp op) exprX exprY
negatePred (Constant cnst)           = Constant $ not cnst

deterministicValue :: PropBuildInPredicate -> Maybe Bool
deterministicValue (BoolEq eq (ConstantExpr left) (ConstantExpr right))   = Just $ (if eq then (==) else (/=)) left right
deterministicValue (BoolEq eq (RFunc left) (RFunc right)) | left == right = Just eq
deterministicValue (Constant val)                                         = Just val
deterministicValue _                                                      = Nothing

checkRealIneqPred :: AST.IneqOp
                  -> PropExpr RealN
                  -> PropExpr RealN
                  -> Map.HashMap PropRFuncLabel Interval.IntervalLimitPoint
                  -> Maybe Bool -- result may be undetermined -> Nothing
checkRealIneqPred op left right point = case op of
    AST.Lt   -> evalLeft ~<  evalRight
    AST.LtEq -> evalLeft ~<= evalRight
    AST.Gt   -> evalLeft ~>  evalRight
    AST.GtEq -> evalLeft ~>= evalRight
    where
    evalLeft  = eval left  point
    evalRight = eval right point

eval :: PropExpr RealN -> HashMap PropRFuncLabel Interval.IntervalLimitPoint -> Interval.IntervalLimitPoint
eval (RFunc rf@(PropRFuncLabel rfStr)) point = Map.lookupDefault (error $ printf "AST.checkRealIneqPred: no point for %s" rfStr) rf point
eval (ConstantExpr (RealConstant r)) _       = Interval.rat2IntervLimPoint r
eval (RealSum x y)    point                  = eval x point + eval y point

-- conditioned formulas
data Conditions = Conditions (HashMap PropRFuncLabel Bool) (HashMap PropRFuncLabel Interval)
    deriving (Eq)

instance Show ComposedLabel
    where
    show (ComposedLabel (PropPredicateLabel label) (Conditions bConds rConds) _) = printf
        "%s|%s"
        label
        (List.intercalate "," ((showCondBool <$> Map.toList bConds) ++ (showCondReal <$> Map.toList rConds)))
        where
            showCondBool (PropRFuncLabel rf, val)    = printf "%s=%s"    rf $ show val

instance Hashable ComposedLabel
    where
    hash              (ComposedLabel _ _ hash) = hash
    hashWithSalt salt (ComposedLabel _ _ hash) = Hashable.hashWithSalt salt hash

uncondComposedLabel :: PropPredicateLabel -> ComposedLabel
uncondComposedLabel label = ComposedLabel label (Conditions Map.empty Map.empty) $ Hashable.hash label

condComposedLabelBool :: PropRFuncLabel -> Bool -> ComposedLabel -> ComposedLabel
condComposedLabelBool rf val (ComposedLabel name (Conditions bConds rConds) hash) = ComposedLabel name (Conditions bConds' rConds) hash'
    where
    bConds' = Map.insert rf val bConds
    hash'   = hash + Hashable.hashWithSalt (Hashable.hash rf) val

condComposedLabelReal :: PropRFuncLabel -> Interval -> ComposedLabel -> ComposedLabel
condComposedLabelReal rf interv (ComposedLabel name (Conditions bConds rConds) hash) = ComposedLabel name (Conditions bConds rConds') hash'
    where
    rConds' = Map.insert rf interv rConds
    hash'   = hash + Hashable.hashWithSalt (Hashable.hash rf) interv

labelId :: ComposedLabel -> Formula cachedInfo -> Maybe ComposedId
labelId label Formula{labels2ids} = Map.lookup label labels2ids

-- the FormulaEntry contains composed node, plus additional, redundant, cached information to avoid recomputations
data FormulaEntry cachedInfo = FormulaEntry NodeType (HashSet NodeRef) (HashSet PropRFuncLabel) cachedInfo

data NodeType = And | Or deriving (Eq, Show, Generic)
instance Hashable NodeType

-- node refs are used for optimisation, to avoid looking up leaves (build in preds and deterministic nodes) in the graph
data NodeRef = RefComposed Bool ComposedId
             | RefBuildInPredicate PropBuildInPredicate (HashMap PropRFuncLabel Interval) -- store only real choices, as bool choices eliminate rfs
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

showCondReal :: (PropRFuncLabel, Interval) -> String
showCondReal (PropRFuncLabel rf, Interval.Interval l r) = printf "%s in (%s,%s)" rf (show l) (show r)

data CacheComputations cachedInfo = CacheComputations
    { cachedInfoComposed      :: HashSet cachedInfo                                      -> cachedInfo
    , cachedInfoBuildInPred   :: HashMap PropRFuncLabel Interval -> PropBuildInPredicate -> cachedInfo
    , cachedInfoDeterministic :: Bool                                                    -> cachedInfo
    }

-- to avoid recomputation
cachedInfoBuildInPredCached :: HashMap PropRFuncLabel Interval
                            -> PropBuildInPredicate
                            -> (HashMap PropRFuncLabel Interval -> PropBuildInPredicate -> cachedInfo)
                            -> HashMap (PropBuildInPredicate, HashMap PropRFuncLabel Interval) cachedInfo
                            -> (cachedInfo, HashMap (PropBuildInPredicate, HashMap PropRFuncLabel Interval) cachedInfo)
cachedInfoBuildInPredCached conds prd infoComp cache = case Map.lookup (prd,conds) cache of
    Just cachedInfo -> (cachedInfo, cache)
    Nothing         -> let cachedInfo = infoComp conds prd
                       in  (cachedInfo, Map.insert (prd,conds) cachedInfo cache)

empty :: CacheComputations cachedInfo -> Formula cachedInfo
empty cacheComps = Formula { nodes        = Map.empty
                           , freshCounter = 0
                           , labels2ids   = Map.empty
                           , buildinCache = Map.empty
                           , cacheComps   = cacheComps
                           }
