-----------------------------------------------------------------------------
--
-- Module      :  Formula
-- Copyright   :
-- License     :  AllRightsReserved
--
-- Maintainer  :
-- Stability   :
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

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
    , entryPrevChoicesReal
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
    hash                  = Hashable.hashWithSalt 0
    hashWithSalt salt rwn = case entryRef rwn of
        RefComposed sign id -> Hashable.hashWithSalt (Hashable.hashWithSalt salt sign) id
        ref                 -> Hashable.hashWithSalt salt ref

insert :: (Hashable cachedInfo, Eq cachedInfo) => Maybe ComposedLabel -> Bool -> NodeType -> HashSet NodeRef -> Formula cachedInfo -> (RefWithNode cachedInfo, Formula cachedInfo)
insert mbLabel sign op children f@(Formula nodes freshCounter labels2ids cInfoComps) = case simplifiedNode of
    Composed nType nChildren -> ( RefWithNode { entryRef        = RefComposed (sign == simplifiedSign) freshCounter
                                              , entryNode       = simplifiedNode
                                              , entryLabel      = mbLabel
                                              , entryRFuncs     = rFuncs
                                              , entryCachedInfo = cachedInfo
                                              }
                                , Formula (Map.insert freshCounter (mbLabel, FormulaEntry nType nChildren rFuncs cachedInfo) nodes)
                                          (freshCounter+1)
                                          (maybe labels2ids (\l -> Map.insert l freshCounter labels2ids) mbLabel)
                                          cInfoComps
                                )
    BuildInPredicate pred rConds -> (predRefWithNode (if sign then pred else AST.negatePred pred) rConds cachedInfo, f)
    Deterministic val            -> (deterministicRefWithNode (val == sign) cachedInfo, f)
    where
        (simplifiedNode, simplifiedSign) = simplify (Composed op children) f
        children' = Set.map (`augmentWithEntry` f) $ nodeChildren simplifiedNode
        rFuncs = case simplifiedNode of
            Deterministic _         -> Set.empty
            BuildInPredicate pred _ -> AST.predRandomFunctions pred
            Composed _ _            -> Set.foldr (\child rfuncs -> Set.union rfuncs $ entryRFuncs child) Set.empty children'
        cachedInfo = cachedInfoComposed cInfoComps (Set.map entryCachedInfo children')

        simplify :: Node -> Formula cachedInfo -> (Node, Bool)
        simplify node@(Deterministic val) _ = (node, undefined)
        simplify node@(BuildInPredicate pred _) _ = case AST.deterministicValue pred of
            Just val -> (Deterministic val, undefined)
            Nothing  -> (node, undefined)
        simplify (Composed operator childRefs) f = (simplified, sign)
            where
                sign = case (nChildren, getFirst newChildRefs) of
                    (1, RefComposed s _) -> s
                    _                    -> True
                simplified
                    | nChildren == 0 = Deterministic filterValue
                    | nChildren == 1 = entryNode . (`augmentWithEntry` f) $ getFirst newChildRefs
                    | Foldable.any (RefDeterministic singleDeterminismValue ==) childRefs =
                        Deterministic singleDeterminismValue
                    | otherwise = Composed operator newChildRefs

                newChildRefs = Set.filter (RefDeterministic filterValue /=) childRefs
                nChildren    = Set.size newChildRefs
                -- truth value that causes determinism if at least a single child has it
                singleDeterminismValue = operator == Or
                -- truth value that can be filtered out
                filterValue = operator == And

        nodeChildren :: Node -> HashSet NodeRef
        nodeChildren (Composed _ children) = children
        nodeChildren _                     = Set.empty

augmentWithEntry :: NodeRef -> Formula cachedInfo -> RefWithNode cachedInfo
augmentWithEntry label f = fromMaybe
                               (error $ printf "non-existing Formula node '%s'" $ show label)
                               (tryAugmentWithEntry label f)

tryAugmentWithEntry :: NodeRef -> Formula cachedInfo -> Maybe (RefWithNode cachedInfo)
tryAugmentWithEntry ref@(RefComposed _ id) (Formula nodes _ _ cInfoComps) = case Map.lookup id nodes of
    Just (mbLabel, FormulaEntry nType nChildren rFuncs cachedInfo) -> Just RefWithNode
        { entryRef        = ref
        , entryNode       = Composed nType nChildren
        , entryLabel      = mbLabel
        , entryRFuncs     = rFuncs
        , entryCachedInfo = cachedInfo
        }
    Nothing                                                        -> Nothing
tryAugmentWithEntry ref@(RefBuildInPredicate pred prevChoicesReal) (Formula _ _ _ cInfoComps) = Just $ predRefWithNode pred prevChoicesReal $ cachedInfoBuildInPred cInfoComps prevChoicesReal pred
tryAugmentWithEntry ref@(RefDeterministic val)                     (Formula _ _ _ cInfoComps) = Just $ deterministicRefWithNode val $ cachedInfoDeterministic cInfoComps val

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

entryPrevChoicesReal :: RefWithNode cachedInfo -> HashMap RFuncLabel Interval
entryPrevChoicesReal entry = case entryRef entry of
    RefBuildInPredicate _ choices -> choices
    _ -> case entryLabel entry of
        Just (ComposedLabel _ _ choices _) -> choices
        _ -> Map.empty

conditionBool :: (Hashable cachedInfo, Eq cachedInfo) => RefWithNode cachedInfo -> RFuncLabel -> Bool -> Formula cachedInfo -> (RefWithNode cachedInfo, Formula cachedInfo)
conditionBool origNodeEntry rf val f@(Formula nodes _ labels2ids cInfoComps)
    | not $ Set.member rf $ entryRFuncs origNodeEntry = (origNodeEntry, f)
    | otherwise = case entryRef origNodeEntry of
        RefComposed sign origId -> case maybe Nothing (`Map.lookup` labels2ids) newLabel of
                                    Just nodeId -> (augmentWithEntry (RefComposed sign nodeId) f, f)
                                    _ -> let (mbLabel, FormulaEntry op children _ _) = fromJust $ Map.lookup origId nodes
                                             (condChildren, f') = Set.foldr
                                                (\child (children, f) ->
                                                    let (condChild, f') = conditionBool (Formula.augmentWithEntry child f) rf val f
                                                    in (Set.insert condChild children, f')
                                                )
                                                (Set.empty, f)
                                                children
                                         in insert newLabel sign op (Set.map entryRef condChildren) f'
            where
                newLabel = condComposedLabelBool rf val <$> entryLabel origNodeEntry
        RefBuildInPredicate pred prevChoicesReal -> let condPred = conditionPred pred
                                    in case AST.deterministicValue condPred of
                                        Just val -> (deterministicRefWithNode val $ cachedInfoDeterministic cInfoComps val, f)
                                        Nothing  -> (predRefWithNode condPred prevChoicesReal $ cachedInfoBuildInPred cInfoComps prevChoicesReal condPred,  f)
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
conditionReal origNodeEntry rf interv f@(Formula nodes _ labels2ids cInfoComps)
    | not $ Set.member rf $ entryRFuncs origNodeEntry = (origNodeEntry, f)
    | otherwise = case entryRef origNodeEntry of
        RefComposed sign origLabel -> case maybe Nothing (`Map.lookup` labels2ids) newLabel of
                                        Just nodeId -> (augmentWithEntry (RefComposed sign nodeId) f, f)
                                        _ -> let (mbLabel, FormulaEntry op children _ _) = fromJust $ Map.lookup origLabel nodes
                                                 (condChildren, f') = Set.foldr
                                                    (\child (children, f) ->
                                                        let (condChild, f') = conditionReal (Formula.augmentWithEntry child f) rf interv f
                                                        in  (Set.insert condChild children, f')
                                                    )
                                                    (Set.empty, f)
                                                    children
                                             in insert newLabel sign op (Set.map entryRef condChildren) f'
            where
                newLabel = condComposedLabelReal rf interv <$> entryLabel origNodeEntry
        RefBuildInPredicate pred prevChoicesReal -> let condPred = conditionPred pred prevChoicesReal
                                    in case AST.deterministicValue condPred of
                                        Just val -> (deterministicRefWithNode val $ cachedInfoDeterministic cInfoComps val, f)
                                        Nothing  -> let choices = Map.insert rf interv prevChoicesReal
                                                    in  (predRefWithNode condPred choices $ cachedInfoBuildInPred cInfoComps choices condPred,  f)
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
exportAsDot path (Formula nodes _ _ _) = do
    file <- doIO (openFile path WriteMode)
    doIO (hPutStrLn file "digraph Formula {")
    doIO (hPutStrLn file $ printf "%i" $ Map.size nodes)
    forM_ (Map.toList nodes) (printNode file)
    doIO (hPutStrLn file "}")
    doIO (hClose file)
    where
        printNode :: Handle -> (ComposedId, (Maybe ComposedLabel, FormulaEntry cachedInfo)) -> ExceptionalT String IO ()
        printNode file (id, (mbLabel, FormulaEntry op children _ _)) = do
            doIO (hPutStrLn file (printf "%i[label=\"%i: %s%s\"];" id id (maybe "" (\l -> show l ++ "\\n") mbLabel) descr))
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
    (HashMap ComposedId (Maybe ComposedLabel, FormulaEntry cachedInfo)) -- graph representing formulas
    Int                                                                 -- "counter for fresh nodes"
    (HashMap ComposedLabel ComposedId)                                  -- map from composed label to composed ids (ids are used for performance, as ints are most effecient as keys in the graph map)
    (CacheComputations cachedInfo)                                      -- how cached information attached to formulas is computed

type ComposedId = Int

data ComposedLabel = ComposedLabel
    String                        -- the name
    (HashMap RFuncLabel Bool)     -- conditions for boolean variables
    (HashMap RFuncLabel Interval) -- conditions for continuous variables
    Int                           -- stored hash to avoid recomputation
    deriving (Eq)

instance Show ComposedLabel where
    show (ComposedLabel name bConds rConds _) = printf
        "%s|%s"
        name
        (List.intercalate "," (fmap showCondBool (Map.toList bConds) ++ fmap showCondReal (Map.toList rConds)))
        where
            showCondBool (rf, val)    = printf "%s=%s"    rf $ show val

instance Hashable ComposedLabel where
    hash              (ComposedLabel _ _ _ hash) = hash
    hashWithSalt salt (ComposedLabel _ _ _ hash) = Hashable.hashWithSalt salt hash

uncondComposedLabel :: PredicateLabel -> ComposedLabel
uncondComposedLabel name = ComposedLabel name Map.empty Map.empty $ Hashable.hash name

condComposedLabelBool :: RFuncLabel -> Bool -> ComposedLabel -> ComposedLabel
condComposedLabelBool rf val (ComposedLabel name bConds rConds hash) = ComposedLabel name bConds' rConds hash' where
    bConds' = Map.insert rf val bConds
    hash'   = Hashable.hashWithSalt (Hashable.hashWithSalt hash val) rf

condComposedLabelReal :: RFuncLabel -> Interval -> ComposedLabel -> ComposedLabel
condComposedLabelReal rf interv (ComposedLabel name bConds rConds hash) = ComposedLabel name bConds rConds' hash' where
    rConds' = Map.insert rf interv rConds
    hash'   = Hashable.hashWithSalt (Hashable.hashWithSalt hash interv) rf

labelId :: ComposedLabel -> Formula cachedInfo -> Maybe ComposedId
labelId label f@(Formula _ _ labels2ids _) = Map.lookup label labels2ids

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

empty :: CacheComputations cachedInfo -> Formula cachedInfo
empty = Formula Map.empty 0 Map.empty
