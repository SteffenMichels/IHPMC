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
    , FState
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
import qualified GroundedAST
import GHC.Generics (Generic)
import Data.Hashable (Hashable)
import qualified Data.Hashable as Hashable
import qualified Data.List as List
import Interval (Interval)
import qualified Interval
import Control.Monad.State.Strict

-- INTERFACE
data Node = Composed NodeType (HashSet NodeRef)
          | BuildInPredicate GroundedAST.BuildInPredicate (HashMap GroundedAST.RFunc Interval) -- store only real choices, as bool choices eliminate rfs
          | Deterministic Bool
          deriving (Show, Eq)

data RefWithNode cachedInfo = RefWithNode
    { entryRef        :: NodeRef
    , entryNode       :: Node
    , entryLabel      :: Maybe ComposedLabel
    , entryRFuncs     :: HashSet GroundedAST.RFunc
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
                    Right conds -> let label' = GroundedAST.PredicateLabel $ show freshCounter
                                   in  ComposedLabel label' conds $ Hashable.hash label' -- only use label as hash (ignore conds) as node is unique anyhow
            let rFuncs = Set.foldr (\child rfuncs -> Set.union rfuncs $ entryRFuncs child) Set.empty children'
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
        BuildInPredicate prd rConds -> return $ predRefWithNode (if sign then prd else GroundedAST.negatePred prd) rConds cachedInfo
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
        _ | RefDeterministic singleDeterminismValue `elem`childRefs  ->
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

predRefWithNode :: GroundedAST.BuildInPredicate -> HashMap GroundedAST.RFunc Interval -> cachedInfo -> RefWithNode cachedInfo
predRefWithNode prd prevChoicesReal cachedInfo = RefWithNode
    { entryRef        = RefBuildInPredicate prd prevChoicesReal
    , entryNode       = BuildInPredicate prd prevChoicesReal
    , entryLabel      = Nothing
    , entryRFuncs     = rFuncs
    , entryCachedInfo = cachedInfo
    }
    where
        rFuncs = GroundedAST.predRandomFunctions prd

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
              -> GroundedAST.RFunc
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
            case GroundedAST.deterministicValue condPred of
                Just val' -> return $ deterministicRefWithNode val' $ cachedInfoDeterministic cacheComps val'
                Nothing -> do
                    let (cachedInfo, buildinCache') = cachedInfoBuildInPredCached prevChoicesReal prd (cachedInfoBuildInPred cacheComps) buildinCache
                    modify (\f -> f {buildinCache=buildinCache'})
                    return $ predRefWithNode condPred prevChoicesReal cachedInfo
            where
            condPred = conditionPred prd
        RefDeterministic _ -> error "should not happen as deterministic nodes contain no rfunctions"
    where
        conditionPred :: GroundedAST.BuildInPredicate -> GroundedAST.BuildInPredicate
        conditionPred (GroundedAST.BuildInPredicateBool (GroundedAST.Equality eq exprL exprR)) = GroundedAST.BuildInPredicateBool $ GroundedAST.Equality eq (conditionExpr exprL) (conditionExpr exprR)
            where
            conditionExpr :: GroundedAST.Expr Bool -> GroundedAST.Expr Bool
            conditionExpr expr@(GroundedAST.RFuncExpr exprRFunc)
                | exprRFunc == rf = GroundedAST.ConstantExpr $ GroundedAST.BoolConstant val
                | otherwise       = expr
            conditionExpr expr = expr
        conditionPred prd = prd

conditionReal :: (Hashable cachedInfo, Eq cachedInfo)
              => RefWithNode cachedInfo
              -> GroundedAST.RFunc
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
            case GroundedAST.deterministicValue condPred of
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
        conditionPred :: GroundedAST.BuildInPredicate -> HashMap GroundedAST.RFunc Interval -> GroundedAST.BuildInPredicate
        conditionPred prd@(GroundedAST.BuildInPredicateReal (GroundedAST.Ineq op left right)) otherRealChoices
            -- check if choice is made for all 'rFuncs' in 'prd'
            | length conditions == Set.size predRFuncs = conditionPred'
            | otherwise = prd
            where
            conditionPred'
                | all ((==) $ Just True)  checkedPreds = GroundedAST.BuildInPredicateReal $ GroundedAST.Constant True
                | all ((==) $ Just False) checkedPreds = GroundedAST.BuildInPredicateReal $ GroundedAST.Constant False
                | otherwise                            = prd

            checkedPreds = map (GroundedAST.checkRealIneqPred op left right) crns
            conditions   = (rf, interv):[(rf',interv') | (rf',interv') <- Map.toList otherRealChoices, Set.member rf' predRFuncs && rf' /= rf]
            crns         = Interval.corners conditions
            predRFuncs   = GroundedAST.predRandomFunctions prd
        conditionPred prd _ = prd

negate :: NodeRef -> NodeRef
negate (RefComposed sign label)                  = RefComposed         (not sign) label
negate (RefBuildInPredicate prd prevChoicesReal) = RefBuildInPredicate (GroundedAST.negatePred prd) prevChoicesReal
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
    , buildinCache :: HashMap (GroundedAST.BuildInPredicate, HashMap GroundedAST.RFunc Interval) cachedInfo -- cache for buildin predicates
    , cacheComps   :: CacheComputations cachedInfo                                          -- how cached information attached to formulas is computed
    }

newtype ComposedId = ComposedId Int deriving (Eq, Generic)
instance Hashable ComposedId

data ComposedLabel = ComposedLabel
    GroundedAST.PredicateLabel -- the name
    Conditions                 -- conditions
    Int                        -- stored hash to avoid recomputation
    deriving (Eq)

-- conditioned formulas
data Conditions = Conditions (HashMap GroundedAST.RFunc Bool) (HashMap GroundedAST.RFunc Interval)
    deriving (Eq)

instance Show ComposedLabel
    where
    show (ComposedLabel label (Conditions bConds rConds) _) = printf
        "%s|%s"
        (show label)
        (List.intercalate "," ((showCondBool <$> Map.toList bConds) ++ (showCondReal <$> Map.toList rConds)))
        where
            showCondBool (rf, val) = printf "%s=%s" (show rf) (show val)

instance Hashable ComposedLabel
    where
    hash              (ComposedLabel _ _ hash) = hash
    hashWithSalt salt (ComposedLabel _ _ hash) = Hashable.hashWithSalt salt hash

uncondComposedLabel :: GroundedAST.PredicateLabel -> ComposedLabel
uncondComposedLabel label = ComposedLabel label (Conditions Map.empty Map.empty) $ Hashable.hash label

condComposedLabelBool :: GroundedAST.RFunc -> Bool -> ComposedLabel -> ComposedLabel
condComposedLabelBool rf val (ComposedLabel name (Conditions bConds rConds) hash) = ComposedLabel name (Conditions bConds' rConds) hash'
    where
    bConds' = Map.insert rf val bConds
    hash'   = hash + Hashable.hashWithSalt (Hashable.hash rf) val

condComposedLabelReal :: GroundedAST.RFunc -> Interval -> ComposedLabel -> ComposedLabel
condComposedLabelReal rf interv (ComposedLabel name (Conditions bConds rConds) hash) = ComposedLabel name (Conditions bConds rConds') hash'
    where
    rConds' = Map.insert rf interv rConds
    hash'   = hash + Hashable.hashWithSalt (Hashable.hash rf) interv

labelId :: ComposedLabel -> FState cachednInfo (Maybe ComposedId)
labelId label = get >>= \Formula{labels2ids} -> return $ Map.lookup label labels2ids

-- the FormulaEntry contains composed node, plus additional, redundant, cached information to avoid recomputations
data FormulaEntry cachedInfo = FormulaEntry NodeType (HashSet NodeRef) (HashSet GroundedAST.RFunc) cachedInfo

data NodeType = And | Or deriving (Eq, Show, Generic)
instance Hashable NodeType

-- node refs are used for optimisation, to avoid looking up leaves (build in preds and deterministic nodes) in the graph
data NodeRef = RefComposed Bool ComposedId
             | RefBuildInPredicate GroundedAST.BuildInPredicate (HashMap GroundedAST.RFunc Interval) -- store only real choices, as bool choices eliminate rfs
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

showCondReal :: (GroundedAST.RFunc, Interval) -> String
showCondReal (rf, Interval.Interval l r) = printf "%s in (%s,%s)" (show rf) (show l) (show r)

refBuildInPredicate :: GroundedAST.BuildInPredicate -> NodeRef
refBuildInPredicate prd = case GroundedAST.deterministicValue prd of
    Just val -> RefDeterministic val
    Nothing  -> RefBuildInPredicate prd Map.empty

data CacheComputations cachedInfo = CacheComputations
    { cachedInfoComposed      :: HashSet cachedInfo                                                         -> cachedInfo
    , cachedInfoBuildInPred   :: HashMap GroundedAST.RFunc Interval -> GroundedAST.BuildInPredicate -> cachedInfo
    , cachedInfoDeterministic :: Bool                                                                       -> cachedInfo
    }

-- to avoid recomputation
cachedInfoBuildInPredCached :: HashMap GroundedAST.RFunc Interval
                            -> GroundedAST.BuildInPredicate
                            -> (HashMap GroundedAST.RFunc Interval -> GroundedAST.BuildInPredicate -> cachedInfo)
                            -> HashMap (GroundedAST.BuildInPredicate, HashMap GroundedAST.RFunc Interval) cachedInfo
                            -> (cachedInfo, HashMap (GroundedAST.BuildInPredicate, HashMap GroundedAST.RFunc Interval) cachedInfo)
cachedInfoBuildInPredCached conds prd infoComp cache = case Map.lookup (prd,conds) cache of
    Just cachedInfo -> (cachedInfo, cache)
    Nothing         -> let cachedInfo = infoComp conds prd
                       in  (cachedInfo, Map.insert (prd,conds) cachedInfo cache)
