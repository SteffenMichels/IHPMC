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
    , NodeLabel
    , LabelWithEntry(entryLabel,entryNode,entryRFuncs,entryScores)
    , empty
    , member
    , insert
    , insertFresh
    , augmentWithEntry
    , exportAsDot
    , uncondNodeLabel
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
import Control.Monad (forM)
import Data.Maybe (fromJust)
import Text.Printf (printf)
import qualified Data.Foldable as Foldable
import BasicTypes
import qualified AST
import GHC.Generics (Generic)
import Data.Hashable (Hashable)
import qualified Data.Hashable as Hashable
import qualified Data.List as List
import Interval (Interval, IntervalLimit)
import qualified Interval

-- NNF nodes "counter for fresh nodes"
data NNF = NNF (HashMap NodeLabel NNFEntry) Int

instance Show NNF where
    show (NNF nodes _) = show nodes

data LabelWithEntry = LabelWithEntry
    { entryLabel  :: NodeLabel
    , entryNode   :: Node
    , entryRFuncs :: HashSet RFuncLabel
    , entryScores :: HashMap RFuncLabel (Double, Double)
    , entryHash   :: Int
    } deriving (Eq, Show)
instance Hashable LabelWithEntry where
    hash lwe              = entryHash lwe
    hashWithSalt salt lwe = Hashable.hashWithSalt salt $ entryHash lwe

-- last element is stored hash to avoid recomputation
data NodeLabel = NodeLabel String (HashMap RFuncLabel Bool) (HashMap RFuncLabel Interval) Int deriving (Eq)

instance Show NodeLabel where
    show (NodeLabel label bConds rConds _) = printf
        "%s|%s"
        label
        (List.intercalate "," ((fmap showCondBool $ Map.toList bConds) ++ (fmap showCondReal $ Map.toList rConds)))
        where
            showCondBool (rf, val)    = printf "%s=%s"    rf $ show val
            showCondReal (rf, interv) = printf "%s in %s" rf $ show interv

instance Hashable NodeLabel where
    hash (NodeLabel _ _ _ hash)              = hash
    hashWithSalt salt (NodeLabel _ _ _ hash) = Hashable.hashWithSalt salt hash

-- the NNFEntry contain an NNF node, plus additional, redundant, cached information to avoid recomputations
data NNFEntry = NNFEntry Node (HashSet RFuncLabel) (HashMap RFuncLabel (Double, Double)) deriving (Show)

data Node = Operator NodeType (HashSet NodeLabel)
          | BuildInPredicate AST.BuildInPredicate
          | Deterministic Bool
          deriving (Eq, Show)

data NodeType = And | Or deriving (Eq, Show, Generic)
instance Hashable NodeType

uncondNodeLabel :: PredicateLabel -> NodeLabel
uncondNodeLabel label = NodeLabel label Map.empty Map.empty $ Hashable.hash label where

condNodeLabelBool :: RFuncLabel -> Bool -> NodeLabel -> NodeLabel
condNodeLabelBool rFuncLabel rFuncVal (NodeLabel l bConds rConds hash) = NodeLabel l bConds' rConds hash' where
    bConds' = Map.insert rFuncLabel rFuncVal bConds
    hash'   = Hashable.hashWithSalt (Hashable.hashWithSalt hash rFuncVal) rFuncLabel

condNodeLabelReal :: RFuncLabel -> Interval -> NodeLabel -> NodeLabel
condNodeLabelReal rf interv (NodeLabel l bConds rConds hash) = NodeLabel l bConds rConds' hash' where
    rConds' = Map.insert rf interv rConds
    hash'   = Hashable.hashWithSalt (Hashable.hashWithSalt hash interv) rf

empty :: NNF
empty = NNF Map.empty 0

member :: NodeLabel -> NNF -> Bool
member label (NNF nodes _) = Map.member label nodes

insert :: NodeLabel -> Node -> NNF -> (LabelWithEntry, NNF)
insert label node nnf@(NNF nodes freshCounter) = (labelWithEntry, nnf')
    where
        labelWithEntry = LabelWithEntry { entryLabel  = label
                                        , entryNode   = simplifiedNode
                                        , entryRFuncs = rFuncs
                                        , entryScores = scores
                                        -- just use label hash, as label uniquely determines content
                                        , entryHash   = Hashable.hash label
                                        }
        nnf' = NNF (Map.insert label (NNFEntry simplifiedNode rFuncs scores) nodes) freshCounter

        (simplifiedNode, children) = simplify node nnf
        rFuncs = case simplifiedNode of
            Deterministic _       -> Set.empty
            BuildInPredicate pred -> AST.randomFunctions pred
            Operator _ _ ->
                Set.foldr (\child rfuncs -> Set.union rfuncs $ entryRFuncs child) Set.empty children

        scores = case simplifiedNode of
            Deterministic _       -> Map.empty
            BuildInPredicate pred -> Map.fromList [(rf, (1.0,1.0)) | rf <- Set.toList rFuncs]
            Operator op _         -> Map.fromList [(rf, scores rf) | rf <- Set.toList rFuncs] where
                scores rf = case op of
                    NNF.And -> (posScore/nRFuncs, negScore)
                    NNF.Or  -> (posScore, negScore/nRFuncs)
                    where
                    (posScore', negScore') = foldr (\childScores (posScore, negScore) ->
                                                    let (cPosScore, cNegScore) = Map.lookupDefault (0.0,0.0) rf childScores
                                                    in  (posScore+cPosScore, negScore+cNegScore)
                                                 )
                                                 (0.0, 0.0)
                                                 childrenScores
                    (posScore, negScore) = (posScore'/nChildren, negScore'/nChildren)
                    nChildren = fromIntegral $ Set.size children
                    childrenScores = [entryScores c | c <- Set.toList children]
        nRFuncs = fromIntegral (Set.size rFuncs)

        -- return children to avoid double Map lookup
        simplify :: Node -> NNF -> (Node, HashSet LabelWithEntry)
        simplify node@(Deterministic _) _ = (node, Set.empty)
        simplify node@(BuildInPredicate pred) _ = case AST.deterministicValue pred of
            Just val -> (Deterministic val, Set.empty)
            Nothing  -> (node, Set.empty)
        simplify (Operator operator childLabels) nnf = (simplified, children)
            where
                simplified
                    | nChildren == 0 = (Deterministic filterValue)
                    | nChildren == 1 = entryNode $ getFirst children
                    | Foldable.any (\c -> entryNode c == Deterministic singleDeterminismValue) children =
                        Deterministic singleDeterminismValue
                    | otherwise = Operator operator $ Set.map entryLabel children

                originalChildren = Set.map (\c -> augmentWithEntry c nnf) childLabels
                children = Set.filter (\c -> entryNode c /= Deterministic filterValue) originalChildren
                nChildren = Set.size children
                -- truth value that causes determinism if at least a single child has it
                singleDeterminismValue = if operator == And then False else True
                -- truth value that can be filtered out
                filterValue = if operator == And then True else False

-- possible optimisation: check whether equal node is already in NNF
insertFresh :: Node -> NNF -> (LabelWithEntry, NNF)
insertFresh node nnf@(NNF nodes freshCounter) = (entry, NNF nodes' (freshCounter+1))
     where
        (entry, NNF nodes' _) = insert label node nnf
        label = uncondNodeLabel (show freshCounter)

augmentWithEntry :: NodeLabel -> NNF -> LabelWithEntry
augmentWithEntry label nnf = case tryAugmentWithEntry label nnf of
    Just entry -> entry
    Nothing    -> error "non-existing NNF node"

tryAugmentWithEntry :: NodeLabel -> NNF -> Maybe LabelWithEntry
tryAugmentWithEntry label (NNF nodes _) = case Map.lookup label nodes of
    Just (NNFEntry node rFuncs scores) -> Just LabelWithEntry
        { entryLabel  = label
        , entryNode   = node
        , entryRFuncs = rFuncs
        , entryScores = scores
        -- just use label hash, as label uniquely determines content
        , entryHash   = Hashable.hash label
        }
    Nothing                            -> Nothing


conditionBool :: LabelWithEntry -> RFuncLabel -> Bool -> NNF -> (LabelWithEntry, NNF)
conditionBool origNodeEntry rf val nnf
    | not $ Set.member rf $ entryRFuncs origNodeEntry = (origNodeEntry, nnf)
    | otherwise = case tryAugmentWithEntry condLabel nnf of
        Just entry -> (entry, nnf)
        _ -> case entryNode origNodeEntry of
            Operator operator children ->
                let (condChildren, nnf') = Set.foldr
                        (\child (children, nnf) ->
                            let (condChild, nnf') = conditionBool (NNF.augmentWithEntry child nnf) rf val nnf
                            in (Set.insert condChild children, nnf')
                        )
                        (Set.empty, nnf)
                        children
                in insert condLabel (Operator operator $ Set.map entryLabel condChildren) nnf'
            BuildInPredicate pred ->
                insert condLabel (BuildInPredicate $ conditionPred pred) nnf
            Deterministic _ -> error "should not happen as deterministic nodes contains no rfunctions"
    where
        condLabel = condNodeLabelBool rf val $ NNF.entryLabel origNodeEntry

        conditionPred :: AST.BuildInPredicate -> AST.BuildInPredicate
        conditionPred (AST.BoolEq exprL exprR) = AST.BoolEq (conditionExpr exprL) (conditionExpr exprR)
            where
                conditionExpr expr@(AST.UserRFunc exprRFuncLabel)
                    | exprRFuncLabel == rf = AST.BoolConstant val
                    | otherwise            = expr
                conditionExpr expr = expr
        conditionPred pred = pred

conditionReal :: LabelWithEntry -> RFuncLabel -> Interval -> NNF -> (LabelWithEntry, NNF)
conditionReal origNodeEntry rf interv nnf
    | not $ Set.member rf $ entryRFuncs origNodeEntry = (origNodeEntry, nnf)
    | otherwise = case tryAugmentWithEntry condLabel nnf of
        Just entry -> (entry, nnf)
        _ -> case entryNode origNodeEntry of
            Operator operator children ->
                let (condChildren, nnf') = Set.foldr
                        (\child (children, nnf) ->
                            let (condChild, nnf') = conditionReal (NNF.augmentWithEntry child nnf) rf interv nnf
                            in (Set.insert condChild children, nnf')
                        )
                        (Set.empty, nnf)
                        children
                in insert condLabel (Operator operator $ Set.map entryLabel condChildren) nnf'
            BuildInPredicate pred ->
                insert condLabel (BuildInPredicate $ conditionPred pred) nnf
            Deterministic _ -> error "should not happen as deterministic nodes contains no rfunctions"
    where
        condLabel = condNodeLabelReal rf interv $ NNF.entryLabel origNodeEntry

        conditionPred :: AST.BuildInPredicate -> AST.BuildInPredicate
        conditionPred pred@(AST.RealIn predRf predInterv)
            | predRf == rf && Interval.subsetEq interv predInterv = AST.Constant True
            | predRf == rf && Interval.disjoint interv predInterv = AST.Constant False
            | otherwise                                           = pred
        conditionPred (AST.RealIneq _ _ _) = error "conditionPred (AST.RealIneq ...) not implemented"
        conditionPred pred = pred

exportAsDot :: FilePath -> NNF -> ExceptionalT String IO ()
exportAsDot path (NNF nodes _) = do
    file <- doIO (openFile path WriteMode)
    doIO (hPutStrLn file "digraph NNF {")
    forM (Map.toList nodes) (printNode file)
    doIO (hPutStrLn file "}")
    doIO (hClose file)
    where
        printNode :: Handle -> (NodeLabel, NNFEntry) -> ExceptionalT String IO ()
        printNode file (label, NNFEntry node _ _) = do
            doIO (hPutStrLn file (printf "%i[label=\"%s\\n%s\"];" labelHash (show label) (descr node)))
            case node of
                (Operator _ children) -> forM (Set.toList children) writeEdge >> return ()
                _                     -> return ()
            where
                descr (Operator t _)          = case t of And -> "AND"; Or -> "OR"
                descr (BuildInPredicate pred) = show pred
                descr (Deterministic val)     = if val then "TRUE" else "FALSE"

                writeEdge childLabel = doIO (hPutStrLn file (printf "%i->%i;" labelHash $ Hashable.hash childLabel))
                labelHash = Hashable.hash label
