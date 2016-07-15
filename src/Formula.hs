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
import Interval (Interval)
import qualified Interval
import Data.Foldable (forM_)
import Control.Arrow (first)

-- INTERFACE
data Node = Composed NodeType (HashSet NodeRef)
          | BuildInPredicate AST.BuildInPredicate (HashMap RFuncLabel Interval) -- store only real choices, as bool choices eliminate rfs
          | Deterministic Bool
          deriving (Show, Eq)

data RefWithNode cachedInfo = RefWithNode
    { entryRef        :: NodeRef
    , entryNode       :: Node
    , entryLabel      :: Maybe ComposedLabel
    , entryRFuncs     :: HashSet RFuncLabel
    , entryCachedInfo :: cachedInfo
    } deriving (Eq)
instance Hashable (RefWithNode cachedInfo) where
    hash                                    = Hashable.hashWithSalt 0
    hashWithSalt salt RefWithNode{entryRef} = Hashable.hashWithSalt salt entryRef

insert :: (Hashable cachedInfo, Eq cachedInfo) => Either ComposedLabel Conditions -> Bool -> NodeType -> HashSet NodeRef -> Formula cachedInfo -> (RefWithNode cachedInfo, Formula cachedInfo)
insert labelOrConds sign op children f@Formula{nodes,labels2ids,freshCounter,cacheComps} = case simplifiedNode of
    Composed nType nChildren -> ( RefWithNode { entryRef        = RefComposed (sign == simplifiedSign) freshId
                                              , entryNode       = simplifiedNode
                                              , entryLabel      = Just label
                                              , entryRFuncs     = rFuncs
                                              , entryCachedInfo = cachedInfo
                                              }
                                , f''         { nodes        = Map.insert freshId (label, FormulaEntry nType nChildren rFuncs cachedInfo) nodes
                                              , freshCounter = freshId+1
                                              , labels2ids   = Map.insert label freshId labels2ids
                                              }
                                )
    BuildInPredicate pred rConds -> (predRefWithNode (if sign then pred else AST.negatePred pred) rConds cachedInfo, f'')
    Deterministic val            -> (deterministicRefWithNode (val == sign) cachedInfo, f'')
    where
        freshId = freshCounter
        label = case labelOrConds of
            Left label  -> label
            Right conds -> let name = show freshId
                           in  ComposedLabel name conds $ Hashable.hash name -- only use name as hash (ignore conds) as node is unique anyhow
        (simplifiedNode, simplifiedSign, f') = simplify (Composed op children) f
        (children', f'') = Set.foldr (\c (cs,f) -> first (`Set.insert` cs) $ augmentWithEntry c f) (Set.empty,f') (nodeChildren simplifiedNode)
        rFuncs = case simplifiedNode of
            Deterministic _         -> Set.empty
            BuildInPredicate pred _ -> AST.predRandomFunctions pred
            Composed _ _            -> Set.foldr (\child rfuncs -> Set.union rfuncs $ entryRFuncs child) Set.empty children'
        cachedInfo = cachedInfoComposed cacheComps (Set.map entryCachedInfo children')

        simplify :: Node -> Formula cachedInfo -> (Node, Bool, Formula cachedInfo)
        simplify node@(Deterministic val) f = (node, undefined, f)
        simplify node@(BuildInPredicate pred _) f = case AST.deterministicValue pred of
            Just val -> (Deterministic val, undefined, f)
            Nothing  -> (node, undefined, f)
        simplify (Composed operator childRefs) f = (simplified, sign, f')
            where
                sign = case (nChildren, getFirst newChildRefs) of
                    (1, RefComposed s _) -> s
                    _                    -> True
                (simplified, f')
                    | nChildren == 0 = (Deterministic filterValue, f)
                    | nChildren == 1 = first entryNode . (`augmentWithEntry` f) $ getFirst newChildRefs
                    | Foldable.any (RefDeterministic singleDeterminismValue ==) childRefs =
                        (Deterministic singleDeterminismValue, f)
                    | otherwise = (Composed operator newChildRefs, f)

                newChildRefs = Set.filter (RefDeterministic filterValue /=) childRefs
                nChildren    = Set.size newChildRefs
                -- truth value that causes determinism if at least a single child has it
                singleDeterminismValue = operator == Or
                -- truth value that can be filtered out
                filterValue = operator == And

        nodeChildren :: Node -> HashSet NodeRef
        nodeChildren (Composed _ children) = children
        nodeChildren _                     = Set.empty

augmentWithEntry :: NodeRef -> Formula cachedInfo -> (RefWithNode cachedInfo, Formula cachedInfo)
augmentWithEntry label f = let (mbRef, f') = tryAugmentWithEntry label f
                           in  ( fromMaybe
                                   (error $ printf "non-existing Formula node '%s'" $ show label)
                                   mbRef
                               , f' )

tryAugmentWithEntry :: NodeRef -> Formula cachedInfo -> (Maybe (RefWithNode cachedInfo), Formula cachedInfo)
tryAugmentWithEntry ref@(RefComposed _ id) f@Formula{nodes} = case Map.lookup id nodes of
    Just (label, FormulaEntry nType nChildren rFuncs cachedInfo) -> (Just RefWithNode
        { entryRef        = ref
        , entryNode       = Composed nType nChildren
        , entryLabel      = Just label
        , entryRFuncs     = rFuncs
        , entryCachedInfo = cachedInfo
        }, f)
    Nothing                                                      -> (Nothing, f)
tryAugmentWithEntry ref@(RefBuildInPredicate pred prevChoicesReal) f@Formula{buildinCache, cacheComps} = let (cachedInfo, buildinCache') = cachedInfoBuildInPredCached prevChoicesReal pred (cachedInfoBuildInPred cacheComps) buildinCache
                                                                                                         in  (Just $ predRefWithNode pred prevChoicesReal cachedInfo, f {buildinCache=buildinCache'})
tryAugmentWithEntry ref@(RefDeterministic val)                     f@Formula{cacheComps}               = (Just $ deterministicRefWithNode val $ cachedInfoDeterministic cacheComps val, f)

entryRefWithNode :: Bool -> ComposedId -> FormulaEntry cachedInfo -> RefWithNode cachedInfo
entryRefWithNode sign id (FormulaEntry op children rFuncs cachedInfo) = RefWithNode
    { entryRef        = RefComposed sign id
    , entryNode       = Composed op children
    , entryLabel      = Nothing
    , entryRFuncs     = rFuncs
    , entryCachedInfo = cachedInfo
    }

predRefWithNode :: AST.BuildInPredicate -> HashMap RFuncLabel Interval -> cachedInfo -> RefWithNode cachedInfo
predRefWithNode pred prevChoicesReal cachedInfo = RefWithNode
    { entryRef        = RefBuildInPredicate pred prevChoicesReal
    , entryNode       = BuildInPredicate pred prevChoicesReal
    , entryLabel      = Nothing
    , entryRFuncs     = rFuncs
    , entryCachedInfo = cachedInfo
    }
    where
        rFuncs = AST.predRandomFunctions pred

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
    RefBuildInPredicate _ choices -> (Map.empty, choices)
    _ -> case entryLabel entry of
        Just (ComposedLabel _ conds _) -> conds
        _ -> (Map.empty, Map.empty)

conditionBool :: (Hashable cachedInfo, Eq cachedInfo) => RefWithNode cachedInfo -> RFuncLabel -> Bool -> Formula cachedInfo -> (RefWithNode cachedInfo, Formula cachedInfo)
conditionBool origNodeEntry rf val f@Formula{nodes, labels2ids, buildinCache, cacheComps}
    | not $ Set.member rf $ entryRFuncs origNodeEntry = (origNodeEntry, f)
    | otherwise = case entryRef origNodeEntry of
        RefComposed sign origId -> case Map.lookup newLabel labels2ids of
                                    Just nodeId -> augmentWithEntry (RefComposed sign nodeId) f
                                    _ -> let (mbLabel, FormulaEntry op children _ _) = fromJust $ Map.lookup origId nodes
                                             (condChildren, f') = Set.foldr
                                                (\child (children, f) ->
                                                    let (condRef,   f')  = Formula.augmentWithEntry child f
                                                        (condChild, f'') = conditionBool condRef rf val f'
                                                    in  (Set.insert condChild children, f'')
                                                )
                                                (Set.empty, f)
                                                children
                                         in  insert (Left newLabel) sign op (Set.map entryRef condChildren) f'
            where
                newLabel = condComposedLabelBool rf val $ fromJust $ entryLabel origNodeEntry
        RefBuildInPredicate pred prevChoicesReal -> let condPred = conditionPred pred
                                    in case AST.deterministicValue condPred of
                                        Just val -> (deterministicRefWithNode val $ cachedInfoDeterministic cacheComps val, f)
                                        Nothing  -> let (cachedInfo, buildinCache') = cachedInfoBuildInPredCached prevChoicesReal pred (cachedInfoBuildInPred cacheComps) buildinCache
                                                    in  (predRefWithNode condPred prevChoicesReal cachedInfo, f {buildinCache=buildinCache'})
        RefDeterministic _ -> error "should not happen as deterministic nodes contain no rfunctions"
    where
        conditionPred :: AST.BuildInPredicate -> AST.BuildInPredicate
        conditionPred (AST.BoolEq eq exprL exprR) = AST.BoolEq eq (conditionExpr exprL) (conditionExpr exprR)
            where
                conditionExpr expr@(AST.UserRFunc exprRFuncLabel)
                    | exprRFuncLabel == rf = AST.BoolConstant val
                    | otherwise            = expr
                conditionExpr expr = expr
        conditionPred pred = pred

conditionReal :: (Hashable cachedInfo, Eq cachedInfo) => RefWithNode cachedInfo -> RFuncLabel -> Interval -> Formula cachedInfo -> (RefWithNode cachedInfo, Formula cachedInfo)
conditionReal origNodeEntry rf interv f@Formula{nodes, labels2ids, buildinCache, cacheComps}
    | not $ Set.member rf $ entryRFuncs origNodeEntry = (origNodeEntry, f)
    | otherwise = case entryRef origNodeEntry of
        RefComposed sign origLabel -> case Map.lookup newLabel labels2ids of
                                        Just nodeId -> augmentWithEntry (RefComposed sign nodeId) f
                                        _ -> let (mbLabel, FormulaEntry op children _ _) = fromJust $ Map.lookup origLabel nodes
                                                 (condChildren, f') = Set.foldr
                                                    (\child (children, f) ->
                                                        let (condRef,   f')  = Formula.augmentWithEntry child f
                                                            (condChild, f'') = conditionReal condRef rf interv f'
                                                        in  (Set.insert condChild children, f'')
                                                    )
                                                    (Set.empty, f)
                                                    children
                                             in insert (Left newLabel) sign op (Set.map entryRef condChildren) f'
            where
                newLabel = condComposedLabelReal rf interv $ fromJust $ entryLabel origNodeEntry
        RefBuildInPredicate pred prevChoicesReal -> let condPred = conditionPred pred prevChoicesReal
                                    in case AST.deterministicValue condPred of
                                        Just val -> (deterministicRefWithNode val $ cachedInfoDeterministic cacheComps val, f)
                                        Nothing  -> let choices = Map.insert rf interv prevChoicesReal
                                                        (cachedInfo, buildinCache') = cachedInfoBuildInPredCached choices pred (cachedInfoBuildInPred cacheComps) buildinCache
                                                    in  (predRefWithNode condPred choices cachedInfo, f {buildinCache=buildinCache'})
        RefDeterministic _ -> error "should not happen as deterministic nodes contain no rfunctions"
    where
        conditionPred :: AST.BuildInPredicate -> HashMap RFuncLabel Interval -> AST.BuildInPredicate
        conditionPred pred@(AST.RealIneq op left right) otherRealChoices
            -- check if choice is made for all rFuncs in pred
            | length conditions == Set.size predRFuncs = conditionPred'
            | otherwise = pred
            where
                conditionPred'
                    | all ((==) $ Just True)  checkedPreds = AST.Constant True
                    | all ((==) $ Just False) checkedPreds = AST.Constant False
                    | otherwise                            = pred

                checkedPreds = map (AST.checkRealIneqPred op left right) crns
                conditions   = (rf, interv):[(rf',interv) | (rf',interv) <- Map.toList otherRealChoices, Set.member rf' predRFuncs && rf' /= rf]
                crns         = Interval.corners conditions
                predRFuncs   = AST.predRandomFunctions pred
        conditionPred pred _ = pred

negate :: NodeRef -> NodeRef
negate (Formula.RefComposed sign label)                   = Formula.RefComposed (not sign) label
negate (Formula.RefBuildInPredicate pred prevChoicesReal) = Formula.RefBuildInPredicate (AST.negatePred pred) prevChoicesReal
negate (Formula.RefDeterministic val)                     = Formula.RefDeterministic (not val)

exportAsDot :: FilePath -> Formula cachedInfo -> ExceptionalT String IO ()
exportAsDot path Formula{nodes} = do
    file <- doIO (openFile path WriteMode)
    doIO (hPutStrLn file "digraph Formula {")
    forM_ (Map.toList nodes) (printNode file)
    doIO (hPutStrLn file "}")
    doIO (hClose file)
    where
        printNode :: Handle -> (ComposedId, (ComposedLabel, FormulaEntry cachedInfo)) -> ExceptionalT String IO ()
        printNode file (id, (label, FormulaEntry op children _ _)) = do
            doIO (hPutStrLn file (printf "%i[label=\"%i: %s\\n%s\"];" id id (show label) descr))
            void $ forM_ children writeEdge
            where
                descr = case op of And -> "AND"; Or -> "OR"
                writeEdge childRef = doIO (hPutStrLn file (printf "%i->%s;" id (childStr childRef)))

                childStr :: NodeRef -> String
                childStr (RefComposed sign childId)   = printf "%i[label=\"%s\"]" childId (show sign)
                childStr (RefBuildInPredicate pred rconds) = let h = Hashable.hashWithSalt id pred in printf "%i;\n%i[label=\"%s\"]" h h $ show pred
                childStr (RefDeterministic _)         = error "Formula export: should this happen?"

-- FORMULA STORAGE
data Formula cachedInfo = Formula
    { nodes        :: HashMap ComposedId (ComposedLabel, FormulaEntry cachedInfo)            -- graph representing formulas
    , freshCounter :: Int                                                                    -- counter for fresh nodes
    , labels2ids   :: HashMap ComposedLabel ComposedId                                       -- map from composed label to composed ids (ids are used for performance, as ints are most effecient as keys in the graph map)
    , buildinCache :: HashMap (AST.BuildInPredicate, HashMap RFuncLabel Interval) cachedInfo -- cache for buildin predicates
    , cacheComps   :: CacheComputations cachedInfo                                           -- how cached information attached to formulas is computed
    }

type ComposedId = Int

data ComposedLabel = ComposedLabel
    String            -- the name
    Conditions        -- conditions
    Int               -- stored hash to avoid recomputation
    deriving (Eq)

type Conditions = (HashMap RFuncLabel Bool, HashMap RFuncLabel Interval)

instance Show ComposedLabel where
    show (ComposedLabel name (bConds, rConds) _) = printf
        "%s|%s"
        name
        (List.intercalate "," (fmap showCondBool (Map.toList bConds) ++ fmap showCondReal (Map.toList rConds)))
        where
            showCondBool (rf, val)    = printf "%s=%s"    rf $ show val

instance Hashable ComposedLabel where
    hash              (ComposedLabel _ _ hash) = hash
    hashWithSalt salt (ComposedLabel _ _ hash) = Hashable.hashWithSalt salt hash

uncondComposedLabel :: PredicateLabel -> ComposedLabel
uncondComposedLabel name = ComposedLabel name (Map.empty, Map.empty) $ Hashable.hash name

condComposedLabelBool :: RFuncLabel -> Bool -> ComposedLabel -> ComposedLabel
condComposedLabelBool rf val (ComposedLabel name (bConds, rConds) hash) = ComposedLabel name (bConds', rConds) hash' where
    bConds' = Map.insert rf val bConds
    hash'   = hash + Hashable.hashWithSalt (Hashable.hash rf) val

condComposedLabelReal :: RFuncLabel -> Interval -> ComposedLabel -> ComposedLabel
condComposedLabelReal rf interv (ComposedLabel name (bConds, rConds) hash) = ComposedLabel name (bConds, rConds') hash' where
    rConds' = Map.insert rf interv rConds
    hash'   = hash + Hashable.hashWithSalt (Hashable.hash rf) interv

labelId :: ComposedLabel -> Formula cachedInfo -> Maybe ComposedId
labelId label Formula{labels2ids} = Map.lookup label labels2ids

-- the FormulaEntry contains composed node, plus additional, redundant, cached information to avoid recomputations
data FormulaEntry cachedInfo = FormulaEntry NodeType (HashSet NodeRef) (HashSet RFuncLabel) cachedInfo

data NodeType = And | Or deriving (Eq, Show, Generic)
instance Hashable NodeType

-- node refs are used for optimisation, to avoid looking up leaves (build in preds and deterministic nodes) in the graph
data NodeRef = RefComposed Bool ComposedId
             | RefBuildInPredicate AST.BuildInPredicate (HashMap RFuncLabel Interval) -- store only real choices, as bool choices eliminate rfs
             | RefDeterministic Bool
             deriving (Eq, Generic)
instance Hashable NodeRef
instance Show NodeRef where
    show (RefComposed sign cid)            = printf "composed %s %i" (show sign) cid
    show (RefBuildInPredicate pred rConds) = printf
                                                "%s|\n  %s"
                                                (show pred)
                                                (List.intercalate ",\n" (fmap showCondReal (Map.toList rConds)))
    show (RefDeterministic val)            = show val

showCondReal (rf, (l,r)) = printf "%s in (%s,%s)" rf (show l) (show r)

data CacheComputations cachedInfo = CacheComputations
    { cachedInfoComposed      :: HashSet cachedInfo                                  -> cachedInfo
    , cachedInfoBuildInPred   :: HashMap RFuncLabel Interval -> AST.BuildInPredicate -> cachedInfo
    , cachedInfoDeterministic :: Bool                                                -> cachedInfo
    }

-- to avoid recomputation
cachedInfoBuildInPredCached :: HashMap RFuncLabel Interval -> AST.BuildInPredicate -> (HashMap RFuncLabel Interval -> AST.BuildInPredicate -> cachedInfo) -> HashMap (AST.BuildInPredicate, HashMap RFuncLabel Interval) cachedInfo -> (cachedInfo, HashMap (AST.BuildInPredicate, HashMap RFuncLabel Interval) cachedInfo)
cachedInfoBuildInPredCached conds pred infoComp cache = case Map.lookup (pred,conds) cache of
    Just cachedInfo -> (cachedInfo, cache)
    Nothing         -> let cachedInfo = infoComp conds pred
                       in  (cachedInfo, Map.insert (pred,conds) cachedInfo cache)

empty :: CacheComputations cachedInfo -> Formula cachedInfo
empty cacheComps = Formula { nodes        = Map.empty
                           , freshCounter = 0
                           , labels2ids   = Map.empty
                           , buildinCache = Map.empty
                           , cacheComps   = cacheComps
                           }
