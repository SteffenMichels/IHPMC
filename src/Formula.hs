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
    , RefWithNode(entryRef,entryNode,entryRFuncs,entryScores)
    , empty
    , insert
    , augmentWithEntry
    , labelId
    , exportAsDot
    , uncondNodeLabel
    , conditionBool
    , conditionReal
    , Formula.negate
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
import Interval (Interval, IntervalLimit, IntervalLimitPoint(..), LowerUpper(..))
import qualified Interval
import Data.Foldable (forM_)
import Debug.Trace (trace)

-- Formula nodes "counter for fresh nodes"
data Formula = Formula (HashMap ComposedId (Maybe ComposedLabel, FormulaEntry)) Int (HashMap ComposedLabel ComposedId)
type ComposedId = Int

data RefWithNode = RefWithNode
    { entryRef    :: NodeRef
    , entryNode   :: Node
    , entryLabel  :: Maybe ComposedLabel
    , entryRFuncs :: HashSet RFuncLabel
    , entryScores :: Scores
    } deriving (Eq)
instance Hashable RefWithNode where
    hash                  = Hashable.hashWithSalt 0
    hashWithSalt salt rwn = case entryRef rwn of
        RefComposed sign id -> Hashable.hashWithSalt (Hashable.hashWithSalt salt sign) id
        ref                 -> Hashable.hashWithSalt salt ref

data NodeRef = RefComposed Bool ComposedId
             | RefBuildInPredicate AST.BuildInPredicate
             | RefDeterministic Bool
             deriving (Eq, Show, Generic)
instance Hashable NodeRef

-- last element is stored hash to avoid recomputation
data ComposedLabel = ComposedLabel String (HashMap RFuncLabel Bool) (HashMap RFuncLabel Interval) Int
                   deriving (Eq)

instance Show ComposedLabel where
    show (ComposedLabel name bConds rConds _) = printf
        "%s|%s"
        name
        (List.intercalate "," (fmap showCondBool (Map.toList bConds) ++ fmap showCondReal (Map.toList rConds)))
        where
            showCondBool (rf, val)    = printf "%s=%s"    rf $ show val
            showCondReal (rf, interv) = printf "%s in %s" rf $ show interv

instance Hashable ComposedLabel where
    hash              (ComposedLabel _ _ _ hash) = hash
    hashWithSalt salt (ComposedLabel _ _ _ hash) = Hashable.hashWithSalt salt hash

-- the FormulaEntry contain a Formula operator node, plus additional, redundant, cached information to avoid recomputations
data FormulaEntry = FormulaEntry NodeType (HashSet NodeRef) (HashSet RFuncLabel) Scores

data Node = Composed NodeType (HashSet NodeRef)
          | BuildInPredicate AST.BuildInPredicate
          | Deterministic Bool
          deriving (Eq)

data NodeType = And | Or deriving (Eq, Show, Generic)
instance Hashable NodeType

type Scores = (Int, HashMap RFuncLabel Int)

uncondNodeLabel :: PredicateLabel -> ComposedLabel
uncondNodeLabel name = ComposedLabel name Map.empty Map.empty $ Hashable.hash name

condNodeLabelBool :: RFuncLabel -> Bool -> ComposedLabel -> ComposedLabel
condNodeLabelBool rf val (ComposedLabel name bConds rConds hash) = ComposedLabel name bConds' rConds hash' where
    bConds' = Map.insert rf val bConds
    hash'   = Hashable.hashWithSalt (Hashable.hashWithSalt hash val) rf

condNodeLabelReal :: RFuncLabel -> Interval -> ComposedLabel -> ComposedLabel
condNodeLabelReal rf interv (ComposedLabel name bConds rConds hash) = ComposedLabel name bConds rConds' hash' where
    rConds' = Map.insert rf interv rConds
    hash'   = Hashable.hashWithSalt (Hashable.hashWithSalt hash interv) rf

empty :: Formula
empty = Formula Map.empty 0 Map.empty

insert ::  Maybe ComposedLabel -> Bool -> NodeType -> HashSet NodeRef -> Formula -> (RefWithNode, Formula)
insert mbLabel sign op children f@(Formula nodes freshCounter labels2ids) = (refWithNode, f')
    where
        (refWithNode, f') = case simplifiedNode of
            Composed nType nChildren -> ( RefWithNode { entryRef    = RefComposed (sign == simplifiedSign) freshCounter
                                                      , entryNode   = simplifiedNode
                                                      , entryLabel  = mbLabel
                                                      , entryRFuncs = rFuncs
                                                      , entryScores = scores
                                                      }
                                        , Formula (Map.insert freshCounter (mbLabel, FormulaEntry nType nChildren rFuncs scores) nodes)
                                                  (freshCounter+1)
                                                  (maybe labels2ids (\l -> Map.insert l freshCounter labels2ids) mbLabel)
                                        )
            BuildInPredicate pred -> (predRefWithNode $ if sign then pred else AST.negatePred pred, f)
            Deterministic val     -> (deterministicRefWithNode (val == sign), f)

        (simplifiedNode, simplifiedSign) = simplify (Composed op children) f
        children' = Set.map (`augmentWithEntry` f) $ nodeChildren simplifiedNode
        rFuncs = case simplifiedNode of
            Deterministic _       -> Set.empty
            BuildInPredicate pred -> AST.predRandomFunctions pred
            Composed _ _ ->
                Set.foldr (\child rfuncs -> Set.union rfuncs $ entryRFuncs child) Set.empty children'

        scores = case simplifiedNode of
            Deterministic _       -> (0, Map.empty)
            BuildInPredicate pred -> let rfs = AST.predRandomFunctions pred in (Set.size rfs, Map.fromList [(rf, 0) | rf <- Set.toList rfs])
            Composed op _         -> (primitiveCount, Set.foldr (\rf map -> Map.insert rf primitiveCount map) newRFScores rfsInPrimitive)
                where
                    newRFScores    = foldr (\(_,child) all -> Map.unionWith (+) all child) Map.empty childrenScores
                    primitiveCount = foldr (\(cc,_) c -> c + cc) 0 childrenScores
                    rfsInPrimitive = Set.foldr (\child rfs -> case entryNode child of
                            BuildInPredicate _ -> Set.union rfs $ entryRFuncs child
                            _                  -> rfs
                        ) Set.empty children'
                    childrenScores = [entryScores c | c <- Set.toList children']

        simplify :: Node -> Formula -> (Node, Bool)
        simplify node@(Deterministic val) _ = (node, undefined)
        simplify node@(BuildInPredicate pred) _ = case AST.deterministicValue pred of
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

augmentWithEntry :: NodeRef -> Formula -> RefWithNode
augmentWithEntry label f = fromMaybe
                               (error $ printf "non-existing Formula node '%s'" $ show label)
                               (tryAugmentWithEntry label f)

tryAugmentWithEntry :: NodeRef -> Formula -> Maybe RefWithNode
tryAugmentWithEntry ref@(RefComposed _ id) (Formula nodes _ _) = case Map.lookup id nodes of
    Just (mbLabel, FormulaEntry nType nChildren rFuncs scores) -> Just RefWithNode
        { entryRef    = ref
        , entryNode   = Composed nType nChildren
        , entryLabel  = mbLabel
        , entryRFuncs = rFuncs
        , entryScores = scores
        }
    Nothing                            -> Nothing
tryAugmentWithEntry ref@(RefBuildInPredicate pred) _ = Just $ predRefWithNode pred
tryAugmentWithEntry ref@(RefDeterministic val) _     = Just $ deterministicRefWithNode val

labelId :: ComposedLabel -> Formula -> Maybe ComposedId
labelId label f@(Formula _ _ labels2ids) = Map.lookup label labels2ids

entryRefWithNode :: Bool -> ComposedId -> FormulaEntry -> RefWithNode
entryRefWithNode sign id (FormulaEntry op children rFuncs scores) = RefWithNode
    { entryRef    = RefComposed sign id
    , entryNode   = Composed op children
    , entryLabel  = Nothing
    , entryRFuncs = rFuncs
    , entryScores = scores
    }

predRefWithNode :: AST.BuildInPredicate -> RefWithNode
predRefWithNode pred = RefWithNode
    { entryRef    = RefBuildInPredicate pred
    , entryNode   = BuildInPredicate pred
    , entryLabel  = Nothing
    , entryRFuncs = rFuncs
    , entryScores = let rfs = AST.predRandomFunctions pred in (Set.size rfs, Map.fromList [(rf, 0) | rf <- Set.toList rfs])
    }
    where
        rFuncs = AST.predRandomFunctions pred

deterministicRefWithNode :: Bool -> RefWithNode
deterministicRefWithNode val = RefWithNode
    { entryRef    = RefDeterministic val
    , entryNode   = Deterministic val
    , entryLabel  = Nothing
    , entryRFuncs = Set.empty
    , entryScores = (0, Map.empty)
    }

conditionBool :: RefWithNode -> RFuncLabel -> Bool -> Formula -> (RefWithNode, Formula)
conditionBool origNodeEntry rf val f@(Formula nodes _ labels2ids)
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
                newLabel = condNodeLabelBool rf val <$> entryLabel origNodeEntry
        RefBuildInPredicate pred -> let condPred = conditionPred pred
                                    in case AST.deterministicValue condPred of
                                        Just val -> (deterministicRefWithNode val, f)
                                        Nothing  -> (predRefWithNode condPred,     f)
        RefDeterministic _       -> error "should not happen as deterministic nodes contains no rfunctions"
    where
        conditionPred :: AST.BuildInPredicate -> AST.BuildInPredicate
        conditionPred (AST.BoolEq eq exprL exprR) = AST.BoolEq eq (conditionExpr exprL) (conditionExpr exprR)
            where
                conditionExpr expr@(AST.UserRFunc exprRFuncLabel)
                    | exprRFuncLabel == rf = AST.BoolConstant val
                    | otherwise            = expr
                conditionExpr expr = expr
        conditionPred pred = pred

conditionReal :: RefWithNode -> RFuncLabel -> Interval -> HashMap RFuncLabel (Interval, Int) -> Formula -> (RefWithNode, Formula)
conditionReal origNodeEntry rf interv otherRealChoices f@(Formula nodes _ labels2ids)
    | not $ Set.member rf $ entryRFuncs origNodeEntry = (origNodeEntry, f)
    | otherwise = case entryRef origNodeEntry of
        RefComposed sign origLabel -> case maybe Nothing (`Map.lookup` labels2ids) newLabel of
                                        Just nodeId -> (augmentWithEntry (RefComposed sign nodeId) f, f)
                                        _ -> let (mbLabel, FormulaEntry op children _ _) = fromJust $ Map.lookup origLabel nodes
                                                 (condChildren, f') = Set.foldr
                                                    (\child (children, f) ->
                                                        let (condChild, f') = conditionReal (Formula.augmentWithEntry child f) rf interv otherRealChoices f
                                                        in (Set.insert condChild children, f')
                                                    )
                                                    (Set.empty, f)
                                                    children
                                             in insert newLabel sign op (Set.map entryRef condChildren) f'
            where
                newLabel = condNodeLabelReal rf interv <$> entryLabel origNodeEntry
        RefBuildInPredicate pred -> let condPred = conditionPred pred
                                    in case AST.deterministicValue condPred of
                                        Just val -> (deterministicRefWithNode val, f)
                                        Nothing  -> (predRefWithNode condPred,     f)
        RefDeterministic _       -> error "should not happen as deterministic nodes contains no rfunctions"
    where
        conditionPred :: AST.BuildInPredicate -> AST.BuildInPredicate
        conditionPred pred@(AST.RealIn predRf predInterv)
            | predRf == rf && Interval.subsetEq interv predInterv = AST.Constant True
            | predRf == rf && Interval.disjoint interv predInterv = AST.Constant False
            | otherwise                                           = pred
        conditionPred pred@(AST.RealIneq op left right)
            -- check if choice is made for all rFuncs in pred
            | length conditions == Set.size predRFuncs = conditionPred'
            | otherwise = pred
            where
                conditionPred'
                    |       and checkedPreds = AST.Constant True
                    | not $ or  checkedPreds = AST.Constant False
                    | otherwise              = pred

                checkedPreds = [checkPred corner | corner <- corners]

                checkPred corner = case op of
                    AST.Lt   -> evalLeft <  evalRight
                    AST.LtEq -> evalLeft <= evalRight
                    AST.Gt   -> evalLeft >  evalRight
                    AST.GtEq -> evalLeft >= evalRight
                    where
                        evalLeft  = eval left
                        evalRight = eval right
                        eval (AST.UserRFunc rf)   = fromJust $ Map.lookup rf corner
                        eval (AST.RealConstant r) = Point r
                        eval (AST.RealSum x y)    = eval x + eval y

                conditions@((firstRf, (firstLower,firstUpper)):otherConditions) = (rf, interv):[(rf',interv) | (rf',(interv, _)) <- Map.toList otherRealChoices, Set.member rf' predRFuncs && rf' /= rf]
                corners = foldr (\(rf, (l,u)) corners -> [Map.insert rf (Interval.toPoint Lower l) c | c <- corners] ++ [Map.insert rf (Interval.toPoint Upper u) c | c <- corners]) [Map.fromList [(firstRf, Interval.toPoint Lower firstLower)], Map.fromList [(firstRf, Interval.toPoint Upper firstUpper)]] otherConditions
                predRFuncs = AST.predRandomFunctions pred
        conditionPred pred = pred

nodeChildren :: Node -> HashSet NodeRef
nodeChildren (Composed _ children) = children
nodeChildren _                     = Set.empty

negate :: NodeRef -> NodeRef
negate (Formula.RefComposed sign label)   = Formula.RefComposed (not sign) label
negate (Formula.RefBuildInPredicate pred) = Formula.RefBuildInPredicate (AST.negatePred pred)
negate (Formula.RefDeterministic val)     = Formula.RefDeterministic (not val)

exportAsDot :: FilePath -> Formula -> ExceptionalT String IO ()
exportAsDot path (Formula nodes _ _) = do
    file <- doIO (openFile path WriteMode)
    doIO (hPutStrLn file "digraph Formula {")
    forM_ (Map.toList nodes) (printNode file)
    doIO (hPutStrLn file "}")
    doIO (hClose file)
    where
        printNode :: Handle -> (ComposedId, (Maybe ComposedLabel, FormulaEntry)) -> ExceptionalT String IO ()
        printNode file (id, (mbLabel, FormulaEntry op children _ _)) = do
            doIO (hPutStrLn file (printf "%i[label=\"%s%s\"];" id (maybe "" (\l -> show l ++ "\\n") mbLabel) descr))
            void $ forM_ children writeEdge
            where
                descr = case op of And -> "AND"; Or -> "OR"
                writeEdge childRef = doIO (hPutStrLn file (printf "%i->%s;" id (childStr childRef)))

                childStr :: NodeRef -> String
                childStr (RefComposed sign childId) = printf "%i[label=\"%s\"]" childId (show sign)
                childStr (RefBuildInPredicate pred) = let h = Hashable.hashWithSalt id pred in printf "%i;\n%i[label=\"%s\"]" h h $ show pred
                childStr (RefDeterministic _)       = error "Formula export: should this happen?"
