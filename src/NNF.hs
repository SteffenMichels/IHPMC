-----------------------------------------------------------------------------
--
-- Module      :  NNF
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

module NNF
    ( NNF
    , Node(..)
    , NodeType(..)
    , NodeRef(..) -- TODO: constructors should not be exposed
    , RefWithNode(entryRef,entryNode,entryRFuncs,entryScores)
    --, ComposedLabel(..)
    , empty
    --, member
    , insert
    --, insertFresh
    , augmentWithEntry
    , exportAsDot
    --, uncondNodeLabel
    , conditionBool
    , conditionReal
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

-- NNF nodes "counter for fresh nodes"
data NNF = NNF (HashMap ComposedId NNFEntry) Int
type ComposedId = Int

data RefWithNode = RefWithNode
    { entryRef    :: NodeRef
    , entryNode   :: Node
    , entryRFuncs :: HashSet RFuncLabel
    , entryScores :: Scores
    } deriving (Eq)
instance Hashable RefWithNode where
    hash                  = Hashable.hashWithSalt 0
    hashWithSalt salt rwn = case entryRef rwn of
        RefComposed sign id -> Hashable.hashWithSalt (Hashable.hashWithSalt salt sign) id
        ref                 -> Hashable.hashWithSalt salt ref

-- last element is stored hash to avoid recomputation
data NodeRef = RefComposed Bool ComposedId
             | RefBuildInPredicate AST.BuildInPredicate
             | RefDeterministic Bool
             deriving (Eq, Show, Generic)
instance Hashable NodeRef

--data ComposedLabel = ComposedLabel String (HashMap RFuncLabel Bool) (HashMap RFuncLabel Interval) Int
--                   deriving (Eq)
--instance Eq ComposedLabel where
 --   (ComposedLabel _ _ _ x) == (ComposedLabel _ _ _ y) = x == y
{-instance Show ComposedLabel where
    show (ComposedLabel name bConds rConds _) = printf
        "%s|%s"
        name
        (List.intercalate "," (fmap showCondBool (Map.toList bConds) ++ fmap showCondReal (Map.toList rConds)))
        where
            showCondBool (rf, val)    = printf "%s=%s"    rf $ show val
            showCondReal (rf, interv) = printf "%s in %s" rf $ show interv-}
{-instance Hashable ComposedLabel where
    hash              (ComposedLabel _ _ _ hash) = hash
    hashWithSalt salt (ComposedLabel _ _ _ hash) = Hashable.hashWithSalt salt hash-}

-- the NNFEntry contain an NNF operator node, plus additional, redundant, cached information to avoid recomputations
data NNFEntry = NNFEntry NodeType (HashSet NodeRef) (HashSet RFuncLabel) Scores

data Node = Composed NodeType (HashSet NodeRef)
          | BuildInPredicate AST.BuildInPredicate
          | Deterministic Bool
          deriving (Eq)

data NodeType = And | Or deriving (Eq, Show, Generic)
instance Hashable NodeType

type Scores = (Int, HashMap RFuncLabel Int)

{-uncondNodeLabel :: RFuncLabel -> ComposedLabel
uncondNodeLabel name = ComposedLabel name Map.empty Map.empty $ Hashable.hash name

condNodeLabelBool :: RFuncLabel -> Bool -> ComposedLabel -> ComposedLabel
condNodeLabelBool rf val (ComposedLabel name bConds rConds hash) = ComposedLabel name bConds' rConds hash' where
    bConds' = Map.insert rf val bConds
    hash'   = Hashable.hashWithSalt (Hashable.hashWithSalt hash val) rf

condNodeLabelReal :: RFuncLabel -> Interval -> ComposedLabel -> ComposedLabel
condNodeLabelReal rf interv (ComposedLabel name bConds rConds hash) = ComposedLabel name bConds rConds' hash' where
    rConds' = Map.insert rf interv rConds
    hash'   = Hashable.hashWithSalt (Hashable.hashWithSalt hash interv) rf-}

empty :: NNF
empty = NNF Map.empty 0

--member :: ComposedLabel -> NNF -> Bool
--member label (NNF nodes _) = Map.member label nodes

insert ::  Bool -> NodeType -> HashSet NodeRef -> NNF -> (RefWithNode, NNF)
insert sign op children nnf@(NNF nodes freshCounter) = (refWithNode, nnf')
    where
        (refWithNode, nnf') = case simplifiedNode of
            Composed nType nChildren -> ( RefWithNode { entryRef    = RefComposed (sign == simplifiedSign) freshCounter
                                                      , entryNode   = simplifiedNode
                                                      , entryRFuncs = rFuncs
                                                      , entryScores = scores
                                                      }
                                        , NNF (Map.insert freshCounter (NNFEntry nType nChildren rFuncs scores) nodes) (freshCounter+1)
                                        )
            BuildInPredicate pred -> (predRefWithNode $ if sign then pred else AST.negatePred pred, nnf)
            Deterministic val     -> (deterministicRefWithNode (val == sign), nnf)

        (simplifiedNode, simplifiedSign, children') = simplify (Composed op children) nnf
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
                    newRFScores = foldr (\(_,child) all -> Map.unionWith (+) all child) Map.empty childrenScores
                    primitiveCount = foldr (\(cc,_) c -> c + cc) 0 childrenScores
                    rfsInPrimitive = Set.foldr (\child rfs -> case entryNode child of
                            BuildInPredicate pred -> Set.union rfs $ AST.predRandomFunctions pred
                            _                     -> rfs
                        ) Set.empty children'
                    childrenScores = [entryScores c | c <- Set.toList children']

        -- return children to avoid double Map lookup
        simplify :: Node -> NNF -> (Node, Bool, HashSet RefWithNode)
        simplify node@(Deterministic _) _ = (node, undefined, Set.empty)
        simplify node@(BuildInPredicate pred) _ = case AST.deterministicValue pred of
            Just val -> (Deterministic val, undefined, Set.empty)
            Nothing  -> (node, undefined, Set.empty)
        simplify (Composed operator childLabels) nnf = (simplified, sign, children)
            where
                sign = case (nChildren, entryRef $ getFirst children) of
                    (1, RefComposed s _) -> s
                    _                    -> True
                simplified
                    | nChildren == 0 = Deterministic filterValue
                    | nChildren == 1 = entryNode $ getFirst children
                    | Foldable.any (\c -> entryNode c == Deterministic singleDeterminismValue) children =
                        Deterministic singleDeterminismValue
                    | otherwise = Composed operator $ Set.map entryRef children

                originalChildren = Set.map (`augmentWithEntry` nnf) childLabels
                children = Set.filter (\c -> entryNode c /= Deterministic filterValue) originalChildren
                nChildren = Set.size children
                -- truth value that causes determinism if at least a single child has it
                singleDeterminismValue = operator == Or
                -- truth value that can be filtered out
                filterValue = operator == And

{-insertFresh :: Bool -> NodeType -> HashSet NodeRef -> NNF -> (RefWithNode, NNF)
insertFresh sign nType nChildren nnf@(NNF nodes freshCounter) = (entry, NNF nodes' (freshCounter+1))
     where
        (entry, NNF nodes' _) = insert sign label nType nChildren nnf
        label = uncondNodeLabel (show freshCounter)-}

augmentWithEntry :: NodeRef -> NNF -> RefWithNode
augmentWithEntry label nnf = fromMaybe
                               (error $ printf "non-existing NNF node '%s'" $ show label)
                               (tryAugmentWithEntry label nnf)

tryAugmentWithEntry :: NodeRef -> NNF -> Maybe RefWithNode
tryAugmentWithEntry ref@(RefComposed _ label) (NNF nodes _) = case Map.lookup label nodes of
    Just (NNFEntry nType nChildren rFuncs scores) -> Just RefWithNode
        { entryRef    = ref
        , entryNode   = Composed nType nChildren
        , entryRFuncs = rFuncs
        , entryScores = scores
        }
    Nothing                            -> Nothing
tryAugmentWithEntry ref@(RefBuildInPredicate pred) _ = Just $ predRefWithNode pred
tryAugmentWithEntry ref@(RefDeterministic val) _     = Just $ deterministicRefWithNode val

entryRefWithNode :: Bool -> ComposedId -> NNFEntry -> RefWithNode
entryRefWithNode sign id (NNFEntry op children rFuncs scores) = RefWithNode
    { entryRef    = RefComposed sign id
    , entryNode   = Composed op children
    , entryRFuncs = rFuncs
    , entryScores = scores
    }

predRefWithNode :: AST.BuildInPredicate -> RefWithNode
predRefWithNode pred = RefWithNode
    { entryRef    = RefBuildInPredicate pred
    , entryNode   = BuildInPredicate pred
    , entryRFuncs = rFuncs
    , entryScores = let rfs = AST.predRandomFunctions pred in (Set.size rfs, Map.fromList [(rf, 0) | rf <- Set.toList rfs])
    }
    where
        rFuncs = AST.predRandomFunctions pred

deterministicRefWithNode :: Bool -> RefWithNode
deterministicRefWithNode val = RefWithNode
    { entryRef    = RefDeterministic val
    , entryNode   = Deterministic val
    , entryRFuncs = Set.empty
    , entryScores = (0, Map.empty)
    }

conditionBool :: RefWithNode -> RFuncLabel -> Bool -> NNF -> (RefWithNode, NNF)
conditionBool origNodeEntry rf val nnf@(NNF nodes _)
    | not $ Set.member rf $ entryRFuncs origNodeEntry = (origNodeEntry, nnf)
    | otherwise = case entryRef origNodeEntry of
        RefComposed sign origId -> case const Nothing of-- TODO: Map.lookup label nodes of
                                        --Just entry -> (entryRefWithNode sign label entry, nnf)
                                        _ -> let (NNFEntry op children _ _) = fromJust $ Map.lookup origId nodes
                                                 (condChildren, nnf') = Set.foldr
                                                    (\child (children, nnf) ->
                                                        let (condChild, nnf') = conditionBool (NNF.augmentWithEntry child nnf) rf val nnf
                                                        in (Set.insert condChild children, nnf')
                                                    )
                                                    (Set.empty, nnf)
                                                    children
                                             in insert sign op (Set.map entryRef condChildren) nnf'
        RefBuildInPredicate pred -> let condPred = conditionPred pred
                                    in case AST.deterministicValue condPred of
                                        Just val -> (deterministicRefWithNode val, nnf)
                                        Nothing  -> (predRefWithNode condPred,     nnf)
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

conditionReal :: RefWithNode -> RFuncLabel -> Interval -> HashMap RFuncLabel (Interval, Int) -> NNF -> (RefWithNode, NNF)
conditionReal origNodeEntry rf interv otherRealChoices nnf@(NNF nodes _)
    | not $ Set.member rf $ entryRFuncs origNodeEntry = (origNodeEntry, nnf)
    | otherwise = case entryRef origNodeEntry of
        RefComposed sign origLabel -> --TODO: let label = condNodeLabelReal rf interv origLabel
                                      case const Nothing of--TODO: Map.lookup label nodes of
                                        --Just entry -> (entryRefWithNode sign label entry, nnf)
                                        _ -> let (NNFEntry op children _ _) = fromJust $ Map.lookup origLabel nodes
                                                 (condChildren, nnf') = Set.foldr
                                                    (\child (children, nnf) ->
                                                        let (condChild, nnf') = conditionReal (NNF.augmentWithEntry child nnf) rf interv otherRealChoices nnf
                                                        in (Set.insert condChild children, nnf')
                                                    )
                                                    (Set.empty, nnf)
                                                    children
                                             in insert sign op (Set.map entryRef condChildren) nnf'
        RefBuildInPredicate pred -> let condPred = conditionPred pred
                                    in case AST.deterministicValue condPred of
                                        Just val -> (deterministicRefWithNode val, nnf)
                                        Nothing  -> (predRefWithNode condPred,     nnf)
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
                    | all (== True)  checkedPreds = AST.Constant True
                    | all (== False) checkedPreds = AST.Constant False
                    | otherwise                   = pred

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

                conditions@((firstRf, (firstLower,firstUpper)):otherConditions) = (rf, interv):[(rf',interv) | (rf',(interv, _)) <- Map.toList otherRealChoices, Set.member rf' predRFuncs && rf' /= rf]
                corners = foldr (\(rf, (l,u)) corners -> [Map.insert rf (Interval.toPoint Lower l) c | c <- corners] ++ [Map.insert rf (Interval.toPoint Upper u) c | c <- corners]) [Map.fromList [(firstRf, Interval.toPoint Lower firstLower)], Map.fromList [(firstRf, Interval.toPoint Upper firstUpper)]] otherConditions
                predRFuncs = AST.predRandomFunctions pred
        conditionPred pred = pred

exportAsDot :: FilePath -> NNF -> ExceptionalT String IO ()
exportAsDot path (NNF nodes _) = do
    file <- doIO (openFile path WriteMode)
    doIO (hPutStrLn file "digraph NNF {")
    forM_ (Map.toList nodes) (printNode file)
    doIO (hPutStrLn file "}")
    doIO (hClose file)
    where
        printNode :: Handle -> (ComposedId, NNFEntry) -> ExceptionalT String IO ()
        printNode file (id, NNFEntry op children _ _) = do
            doIO (hPutStrLn file (printf "%i[label=\"%s\\n%s\"];" id (show id) descr))
            void $ forM_ children writeEdge
            where
                descr = case op of And -> "AND"; Or -> "OR"
                writeEdge childRef = doIO (hPutStrLn file (printf "%i->%s;" id (childStr childRef)))

                childStr :: NodeRef -> String
                childStr (RefComposed sign childLabel) = printf "%i[label=\"%s\"]" (Hashable.hash childLabel) (show sign)
                childStr (RefBuildInPredicate pred)    = let h = Hashable.hashWithSalt id pred in printf "%i;\n%i[label=\"%s\"]" h h $ show pred
                childStr (RefDeterministic _)          = error "NNF export: should this happen?"
