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
    , NodeRef
    , refDeterministic
    , refBuildInPredicate
    , refComposed
    , negateNodeRef
    , deterministicNodeRef
    , RefWithNode(entryRef,entryNode,entryPFuncs,entryCachedInfo)
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
import Data.Foldable (foldl')
import Util

-- INTERFACE
data Node = Composed NodeType [NodeRef]
          | BuildInPredicate GroundedAST.BuildInPredicate (HashMap GroundedAST.PFunc Interval) -- store only real choices, as bool choices eliminate pfs
          | Deterministic Bool
          deriving (Show, Eq)

data RefWithNode cachedInfo = RefWithNode
    { entryRef        :: NodeRef
    , entryNode       :: Node
    , entryLabel      :: Maybe ComposedLabel
    , entryPFuncs     :: HashSet GroundedAST.PFunc
    , entryCachedInfo :: cachedInfo
    }

type FState cachedInfo = State (Formula cachedInfo)

empty :: CacheComputations cachedInfo -> Formula cachedInfo
empty cacheComps = Formula { nodes        = Map.empty
                           , freshCounter = 0
                           , labels2ids   = Map.empty
                           , buildinCache = Map.empty
                           , cacheComps   = cacheComps
                           }

insert :: Either ComposedLabel Conditions
       -> Bool
       -> NodeType
       -> [NodeRef]
       -> FState cachedInfo (RefWithNode cachedInfo)
insert labelOrConds sign op children = do
    (simplifiedNode, simplifiedSign) <- simplify op children
    children' <- forM (nodeChildren simplifiedNode) augmentWithEntry
    Formula{cacheComps, freshCounter, labels2ids, nodes} <- get
    let cachedInfo = cachedInfoComposed cacheComps (entryCachedInfo <$> children')
    case simplifiedNode of
        Composed nType nChildren -> do
            let label = case labelOrConds of
                    Left label' -> label'
                    Right conds -> let label' = GroundedAST.PredicateLabel $ show freshCounter
                                   in  ComposedLabel label' conds $ Hashable.hash label' -- only use label as hash (ignore conds) as node is unique anyhow
            let pFuncs = foldl' (\pfuncs child -> Set.union pfuncs $ entryPFuncs child) Set.empty children'
            modify' (\f -> f{ nodes       = Map.insert (ComposedId freshCounter) (label, FormulaEntry nType nChildren pFuncs cachedInfo) nodes
                           , freshCounter = succ freshCounter
                           , labels2ids   = Map.insert label (ComposedId freshCounter) labels2ids
                           }
                   )
            return RefWithNode { entryRef        = RefComposed (sign == simplifiedSign) $ ComposedId freshCounter
                               , entryNode       = simplifiedNode
                               , entryLabel      = Just label
                               , entryPFuncs     = pFuncs
                               , entryCachedInfo = cachedInfo
                               }
        BuildInPredicate prd rConds -> return $ predRefWithNode (if sign then prd else GroundedAST.negatePred prd) rConds cachedInfo
        Deterministic val           -> return $ deterministicRefWithNode (val == sign) cachedInfo
    where
    simplify :: NodeType -> [NodeRef] -> FState cachedInfo (Node, Bool)
    simplify operator childRefs = case newChildRefs of
        []          -> return (Deterministic filterValue, True)
        [onlyChild] -> do
            let sign' = case onlyChild of
                    RefComposed sign'' _ -> sign''
                    _                    -> True
            e <- augmentWithEntry onlyChild
            return (entryNode e, sign')
        _ | RefDeterministic singleDeterminismValue `elem`childRefs  ->
            return (Deterministic singleDeterminismValue, True)
        _ ->
            return (Composed operator newChildRefs, True)
        where
        newChildRefs = filter (RefDeterministic filterValue /=) childRefs
        -- truth value that causes determinism if at least a single child has it
        singleDeterminismValue = operator == Or
        -- truth value that can be filtered out
        filterValue = operator == And

    nodeChildren :: Node -> [NodeRef]
    nodeChildren (Composed _ children'') = children''
    nodeChildren _                       = []

augmentWithEntry :: NodeRef -> FState cachedInfo (RefWithNode cachedInfo)
augmentWithEntry label = fromMaybe (error $ printf "Formula: non-existing Formula node '%s'" $ show label)
                         <$>
                         tryAugmentWithEntry label

tryAugmentWithEntry :: NodeRef -> FState cachedInfo (Maybe (RefWithNode cachedInfo))
tryAugmentWithEntry ref@(RefComposed _ i) = do
    Formula{nodes} <- get
    case Map.lookup i nodes of
        Just (label, FormulaEntry nType nChildren pFuncs cachedInfo) -> return $ Just RefWithNode
            { entryRef        = ref
            , entryNode       = Composed nType nChildren
            , entryLabel      = Just label
            , entryPFuncs     = pFuncs
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

predRefWithNode :: GroundedAST.BuildInPredicate -> HashMap GroundedAST.PFunc Interval -> cachedInfo -> RefWithNode cachedInfo
predRefWithNode prd prevChoicesReal cachedInfo = RefWithNode
    { entryRef        = RefBuildInPredicate prd prevChoicesReal
    , entryNode       = BuildInPredicate prd prevChoicesReal
    , entryLabel      = Nothing
    , entryPFuncs     = pFuncs
    , entryCachedInfo = cachedInfo
    }
    where
        pFuncs = GroundedAST.predProbabilisticFunctions prd

deterministicRefWithNode :: Bool -> cachedInfo -> RefWithNode cachedInfo
deterministicRefWithNode val cachedInfo = RefWithNode
    { entryRef        = RefDeterministic val
    , entryNode       = Deterministic val
    , entryLabel      = Nothing
    , entryPFuncs     = Set.empty
    , entryCachedInfo = cachedInfo
    }

entryChoices :: RefWithNode cachedInfo -> Conditions
entryChoices entry = case entryRef entry of
    RefBuildInPredicate _ choices -> Conditions Map.empty choices
    _ -> case entryLabel entry of
        Just (ComposedLabel _ conds _) -> conds
        _ -> Conditions Map.empty Map.empty

conditionBool :: RefWithNode cachedInfo
              -> GroundedAST.PFunc
              -> Bool
              -> FState cachedInfo (RefWithNode cachedInfo)
conditionBool origNodeEntry pf val
    | not $ Set.member pf $ entryPFuncs origNodeEntry = return origNodeEntry
    | otherwise = case entryRef origNodeEntry of
        RefComposed sign origId -> do
            Formula{labels2ids, nodes} <- get
            case Map.lookup newLabel labels2ids of
                Just nodeId -> augmentWithEntry $ RefComposed sign nodeId
                _ -> do
                    let (_, FormulaEntry op children _ _) = fromJust $ Map.lookup origId nodes
                    condChildren <- forM
                        children
                        (\child -> do
                            condRef <- augmentWithEntry child
                            conditionBool condRef pf val
                        )
                    insert (Left newLabel) sign op $ map entryRef condChildren
            where
            newLabel = condComposedLabelBool pf val $ fromJust $ entryLabel origNodeEntry
        RefBuildInPredicate prd prevChoicesReal -> do
            Formula{cacheComps, buildinCache} <- get
            case GroundedAST.deterministicValue condPred of
                Just val' -> return $ deterministicRefWithNode val' $ cachedInfoDeterministic cacheComps val'
                Nothing -> do
                    let (cachedInfo, buildinCache') = cachedInfoBuildInPredCached prevChoicesReal prd (cachedInfoBuildInPred cacheComps) buildinCache
                    modify' (\f -> f {buildinCache=buildinCache'})
                    return $ predRefWithNode condPred prevChoicesReal cachedInfo
            where
            condPred = conditionPred prd
        RefDeterministic _ -> error "should not happen as deterministic nodes contain no pfunctions"
    where
        conditionPred :: GroundedAST.BuildInPredicate -> GroundedAST.BuildInPredicate
        conditionPred (GroundedAST.BuildInPredicateBool (GroundedAST.Equality eq exprL exprR)) = GroundedAST.BuildInPredicateBool $ GroundedAST.Equality eq (conditionExpr exprL) (conditionExpr exprR)
            where
            conditionExpr :: GroundedAST.Expr Bool -> GroundedAST.Expr Bool
            conditionExpr expr@(GroundedAST.PFuncExpr exprPFunc)
                | exprPFunc == pf = GroundedAST.ConstantExpr $ GroundedAST.BoolConstant val
                | otherwise       = expr
            conditionExpr expr = expr
        conditionPred prd = prd

conditionReal :: RefWithNode cachedInfo
              -> GroundedAST.PFunc
              -> Interval
              -> FState cachedInfo (RefWithNode cachedInfo)
conditionReal origNodeEntry pf interv
    | not $ Set.member pf $ entryPFuncs origNodeEntry = return origNodeEntry
    | otherwise = case entryRef origNodeEntry of
        RefComposed sign origLabel -> do
            Formula{labels2ids, nodes} <- get
            case Map.lookup newLabel labels2ids of
                Just nodeId -> augmentWithEntry $ RefComposed sign nodeId
                _ -> do
                    let (_, FormulaEntry op children _ _) = fromJust $ Map.lookup origLabel nodes
                    condChildren <- forM
                        children
                        (\child -> do
                            condRef   <- Formula.augmentWithEntry child
                            conditionReal condRef pf interv
                        )
                    insert (Left newLabel) sign op $ map entryRef condChildren
            where
            newLabel = condComposedLabelReal pf interv $ fromJust $ entryLabel origNodeEntry
        RefBuildInPredicate prd prevChoicesReal -> do
            Formula{cacheComps, buildinCache} <- get
            case GroundedAST.deterministicValue condPred of
                Just val -> return $ deterministicRefWithNode val $ cachedInfoDeterministic cacheComps val
                Nothing  -> do
                    let choices = Map.insert pf interv prevChoicesReal
                    let (cachedInfo, buildinCache') = cachedInfoBuildInPredCached choices prd (cachedInfoBuildInPred cacheComps) buildinCache
                    modify' (\f -> f {buildinCache=buildinCache'})
                    return $ predRefWithNode condPred choices cachedInfo
            where
            condPred = conditionPred prd prevChoicesReal
        RefDeterministic _ -> error "should not happen as deterministic nodes contain no pfunctions"
    where
        conditionPred :: GroundedAST.BuildInPredicate -> HashMap GroundedAST.PFunc Interval -> GroundedAST.BuildInPredicate
        conditionPred prd@(GroundedAST.BuildInPredicateReal (GroundedAST.Ineq op left right)) otherRealChoices
            -- check if choice is made for all 'pFuncs' in 'prd'
            | length conditions == Set.size predPFuncs = conditionPred'
            | otherwise = prd
            where
            conditionPred'
                | all ((==) $ Just True)  checkedPreds = GroundedAST.BuildInPredicateReal $ GroundedAST.Constant True
                | all ((==) $ Just False) checkedPreds = GroundedAST.BuildInPredicateReal $ GroundedAST.Constant False
                | otherwise                            = prd

            checkedPreds = map (GroundedAST.checkRealIneqPred op left right) crns
            conditions   = (pf, interv):[(pf',interv') | (pf',interv') <- Map.toList otherRealChoices, Set.member pf' predPFuncs && pf' /= pf]
            crns         = Interval.corners conditions
            predPFuncs   = GroundedAST.predProbabilisticFunctions prd
        conditionPred prd _ = prd

negate :: NodeRef -> NodeRef
negate (RefComposed sign label)                  = RefComposed         (not sign) label
negate (RefBuildInPredicate prd prevChoicesReal) = RefBuildInPredicate (GroundedAST.negatePred prd) prevChoicesReal
negate (RefDeterministic val)                    = RefDeterministic    (not val)

exportAsDot :: FilePath -> Formula cachedInfo -> ExceptionalT IOException IO ()
exportAsDot path Formula{nodes} = do
    file <- doIO (openFile path WriteMode)
    doIO (hPutStrLn file "digraph Formula {")
    forM_ (Map.toList nodes) (printNode file)
    doIO (hPutStrLn file "}")
    doIO (hClose file)
    where
        printNode :: Handle -> (ComposedId, (ComposedLabel, FormulaEntry cachedInfo)) -> ExceptionalT IOException IO ()
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
                    h = Hashable.hashWithSalt (Hashable.hash i) prd
                childStr (RefDeterministic _)                    = error "Formula export: should this happen?"

-- FORMULA STORAGE
data Formula cachedInfo = Formula
    { nodes        :: HashMap ComposedId (ComposedLabel, FormulaEntry cachedInfo)           -- graph representing formulas
    , freshCounter :: Integer                                                               -- counter for fresh nodes
    , labels2ids   :: HashMap ComposedLabel ComposedId                                      -- map from composed label to composed ids (ids are used for performance, as ints are most effecient as keys in the graph map)
    , buildinCache :: HashMap (GroundedAST.BuildInPredicate, HashMap GroundedAST.PFunc Interval) cachedInfo -- cache for buildin predicates
    , cacheComps   :: CacheComputations cachedInfo                                          -- how cached information attached to formulas is computed
    }

newtype ComposedId = ComposedId Integer deriving (Eq, Generic)
instance Hashable ComposedId

data ComposedLabel = ComposedLabel
    GroundedAST.PredicateLabel -- the name
    Conditions                 -- conditions
    Int                        -- stored hash to avoid recomputation
    deriving (Eq)

-- conditioned formulas
data Conditions = Conditions (HashMap GroundedAST.PFunc Bool) (HashMap GroundedAST.PFunc Interval)
    deriving (Eq)

instance Show ComposedLabel
    where
    show (ComposedLabel label (Conditions bConds rConds) _) = printf
        "%s|%s"
        (show label)
        (showLst ((showCondBool <$> Map.toList bConds) ++ (showCondReal <$> Map.toList rConds)))
        where
            showCondBool (pf, val) = printf "%s=%s" (show pf) (show val)

instance Hashable ComposedLabel
    where
    hash              (ComposedLabel _ _ hash) = hash
    hashWithSalt salt (ComposedLabel _ _ hash) = Hashable.hashWithSalt salt hash

uncondComposedLabel :: GroundedAST.PredicateLabel -> ComposedLabel
uncondComposedLabel label = ComposedLabel label (Conditions Map.empty Map.empty) $ Hashable.hash label

condComposedLabelBool :: GroundedAST.PFunc -> Bool -> ComposedLabel -> ComposedLabel
condComposedLabelBool pf val (ComposedLabel name (Conditions bConds rConds) hash) = ComposedLabel name (Conditions bConds' rConds) hash'
    where
    bConds' = Map.insert pf val bConds
    hash'   = hash + Hashable.hashWithSalt (Hashable.hash pf) val

condComposedLabelReal :: GroundedAST.PFunc -> Interval -> ComposedLabel -> ComposedLabel
condComposedLabelReal pf interv (ComposedLabel name (Conditions bConds rConds) hash) = ComposedLabel name (Conditions bConds rConds') hash'
    where
    rConds' = Map.insert pf interv rConds
    hash'   = hash + Hashable.hashWithSalt (Hashable.hash pf) interv

labelId :: ComposedLabel -> FState cachednInfo (Maybe ComposedId)
labelId label = get >>= \Formula{labels2ids} -> return $ Map.lookup label labels2ids

-- the FormulaEntry contains composed node, plus additional, redundant, cached information to avoid recomputations
data FormulaEntry cachedInfo = FormulaEntry NodeType [NodeRef] (HashSet GroundedAST.PFunc) cachedInfo

data NodeType = And | Or deriving (Eq, Show, Generic)
instance Hashable NodeType

-- node refs are used for optimisation, to avoid looking up leaves (build in preds and deterministic nodes) in the graph
data NodeRef = RefComposed Bool ComposedId
             -- store only real choices, as bool choices eliminate pfs
             | RefBuildInPredicate GroundedAST.BuildInPredicate (HashMap GroundedAST.PFunc Interval)
             | RefDeterministic Bool
             deriving Eq

instance Show NodeRef
    where
    show (RefComposed sign (ComposedId cid)) = printf
        "%s%s\n"
        (if sign then "" else "-")
        (show cid)
    show (RefBuildInPredicate prd rConds)    = printf
       "%s|\n  %s"
       (show prd)
       (List.intercalate ",\n" (showCondReal <$> Map.toList rConds))
    show (RefDeterministic val)              = show val

showCondReal :: (GroundedAST.PFunc, Interval) -> String
showCondReal (pf, Interval.Interval l r) = printf "%s in (%s,%s)" (show pf) (show l) (show r)

refDeterministic :: Bool -> NodeRef
refDeterministic = RefDeterministic

refBuildInPredicate :: GroundedAST.BuildInPredicate -> NodeRef
refBuildInPredicate prd = case GroundedAST.deterministicValue prd of
    Just val -> RefDeterministic val
    Nothing  -> RefBuildInPredicate prd Map.empty

refComposed :: ComposedId -> NodeRef
refComposed = RefComposed True

negateNodeRef :: NodeRef -> NodeRef
negateNodeRef (RefComposed sign label)                  = RefComposed (not sign) label
negateNodeRef (RefBuildInPredicate prd prevChoicesReal) = RefBuildInPredicate (GroundedAST.negatePred prd) prevChoicesReal
negateNodeRef (RefDeterministic val)                    = RefDeterministic $ not val

deterministicNodeRef :: NodeRef -> Maybe Bool
deterministicNodeRef (RefDeterministic val) = Just val
deterministicNodeRef _                      = Nothing

data CacheComputations cachedInfo = CacheComputations
    { cachedInfoComposed      :: [cachedInfo]                                                       -> cachedInfo
    , cachedInfoBuildInPred   :: HashMap GroundedAST.PFunc Interval -> GroundedAST.BuildInPredicate -> cachedInfo
    , cachedInfoDeterministic :: Bool                                                               -> cachedInfo
    }

-- to avoid recomputation
cachedInfoBuildInPredCached :: HashMap GroundedAST.PFunc Interval
                            -> GroundedAST.BuildInPredicate
                            -> (HashMap GroundedAST.PFunc Interval -> GroundedAST.BuildInPredicate -> cachedInfo)
                            -> HashMap (GroundedAST.BuildInPredicate, HashMap GroundedAST.PFunc Interval) cachedInfo
                            -> (cachedInfo, HashMap (GroundedAST.BuildInPredicate, HashMap GroundedAST.PFunc Interval) cachedInfo)
cachedInfoBuildInPredCached conds prd infoComp cache = case Map.lookup (prd,conds) cache of
    Just cachedInfo -> (cachedInfo, cache)
    Nothing         -> let cachedInfo = infoComp conds prd
                       in  (cachedInfo, Map.insert (prd,conds) cachedInfo cache)
