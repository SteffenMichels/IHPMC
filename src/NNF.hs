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
    , empty
    , member
    , insert
    , insertFresh
    , lookUp
    , simplify
    , exportAsDot
    ) where
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified AST
import Control.Monad.Exception.Synchronous
import System.IO
import Exception
import Control.Monad (forM)
import Data.Maybe (fromJust)
import Text.Printf (printf)
import qualified Data.Foldable as Foldable

data NNF = NNF (Map NodeLabel Node) Int

instance Show NNF where
    show _ = "NNF String"

type NodeLabel = String

data Node = Operator NodeType (Set NodeLabel)
          | BuildInPredicate AST.BuildInPredicate
          | Deterministic Bool
          deriving (Eq, Ord)

data NodeType = And | Or deriving (Eq, Ord)

empty :: NNF
empty = NNF Map.empty 0

member :: NodeLabel -> NNF -> Bool
member label (NNF nodes freshCounter) = Map.member label nodes

insert :: NodeLabel -> Node -> NNF -> NNF
insert label node (NNF nodes freshCounter) = NNF (Map.insert label node nodes) freshCounter

-- possible optimisation: check whether equal node is already in NNF
insertFresh :: Node -> NNF -> (NodeLabel, NNF)
insertFresh node (NNF nodes freshCounter) =
    (label, NNF (Map.insert label node nodes) (freshCounter + 1)) where label = show freshCounter

lookUp :: NodeLabel -> NNF -> Maybe Node
lookUp label (NNF nodes _) = Map.lookup label nodes

--deterministicValue :: NodeLabel -> NNF -> Maybe Bool
--deterministicValue label nnf = case fromJust (lookUp label nnf) of
--    Deterministic val -> Just val
--    _                 -> Nothing

simplify :: AST.PredicateLabel -> NNF -> NNF
simplify root nnf =
    if root == topLabel
    then nnf'
    else insert root topNode nnf' -- copy topmost node content for root
    where
        (topLabel, topNode, nnf') = addNode root nnf

        addNode :: AST.PredicateLabel -> NNF -> (AST.PredicateLabel, Node, NNF)
        addNode label nnf = (topLabel, topNode, insert label topNode nnf')
            where
                (topLabel, topNode, nnf') = case node of
                    (Operator nType children) -> addOperatorNode nType children
                    (BuildInPredicate pred) -> case AST.deterministicValue pred of
                        Just val -> (label, node', nnf) where node' = Deterministic val
                        Nothing  -> (label, node, nnf)
                    where
                        node = fromJust (lookUp label nnf)

                        addOperatorNode nType children
                            | nChildren == 0 = (label, Deterministic filterValue, nnf')
                            | nChildren == 1 = let singleChildLabel = Set.findMax childLabels
                                                   singeChildNode   = Set.findMax childNodes
                                               in (singleChildLabel, singeChildNode, nnf')
                            | Foldable.any (\n -> n == Deterministic singleDeterminismValue) childNodes =
                                let node = Deterministic singleDeterminismValue in (label, node, nnf')
                            | otherwise =
                                let node = Operator nType childLabels in (label, node, nnf')
                            where
                                (childLabels, childNodes, nnf') = Set.fold
                                    (\child (childLabels, childNodes, nnf) ->
                                        let (newLabel, newNode, nnf') = addNode child nnf
                                        in if newNode == Deterministic filterValue then
                                                (childLabels, childNodes, nnf')
                                           else
                                                (Set.insert newLabel childLabels, Set.insert newNode childNodes, nnf')
                                    )
                                    (Set.empty, Set.empty, nnf)
                                    children

                                nChildren = Set.size childLabels
                                -- truth value that causes determinism if at least a single child has it
                                singleDeterminismValue = if nType == And then False else True
                                -- truth value that can be filtered out
                                filterValue = if nType == And then True else False

exportAsDot :: FilePath -> NNF -> ExceptionalT String IO ()
exportAsDot path (NNF nodes _) = do
    file <- doIO (openFile path WriteMode)
    doIO (hPutStrLn file "digraph NNF {")
    forM (Map.assocs nodes) (printNode file)
    doIO (hPutStrLn file "}")
    doIO (hClose file)
    where
        printNode :: Handle -> (NodeLabel, Node) -> ExceptionalT String IO ()
        printNode file (label,node) = do
            doIO (hPutStrLn file (printf "    %s[label=\"%s\\n%s\"];" label label $ descr node))
            case node of
                (Operator _ children) -> forM (Set.toList children) writeEdge >> return ()
                _                     -> return ()
            where
                descr (Operator t _)          = case t of And -> "AND"; Or -> "OR"
                descr (BuildInPredicate pred) = show pred
                descr (Deterministic val)     = if val then "TRUE" else "FALSE"

                writeEdge childLabel = doIO (hPutStrLn file (printf "    %s -> %s;" label childLabel))
