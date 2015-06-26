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
    , emptyNNF
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

data NNF = NNF (Map NodeLabel Node) Int

instance Show NNF where
    show _ = "NNF String"

type NodeLabel = String

data Node = Operator NodeType (Set NodeLabel)
          | BuildInPredicate AST.BuildInPredicate

data NodeType = And | Or

emptyNNF :: NNF
emptyNNF = NNF Map.empty 0

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

simplify :: AST.PredicateLabel -> NNF -> NNF
simplify root nnf =
    if root == topLabel
    then nnf'
    else insert root (fromJust (lookUp topLabel nnf')) nnf' -- copy topmost node content for root
    where
        (topLabel, nnf') = addNode root nnf

        addNode :: AST.PredicateLabel -> NNF -> (AST.PredicateLabel, NNF)
        addNode label nnf =
            let node = fromJust (lookUp label nnf)
            in case node of
                (Operator nType children)
                    | nChildren == 0 -> error "should not happen?"
                    | nChildren == 1 -> let (childLabel, nnf') = addNode (Set.findMin children) nnf
                                        in (childLabel, nnf')
                    | otherwise      -> let (newChildren, nnf') = Set.fold
                                                (\child (newChildren, nnf) -> let (newLabel, nnf'') = addNode child nnf
                                                                           in (Set.insert newLabel newChildren, nnf'')
                                                )
                                                (Set.empty, nnf)
                                                children
                                        in (label, insert label (Operator nType newChildren) nnf')
                    where
                        nChildren = Set.size children
                (BuildInPredicate _) -> (label, nnf)

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
                (BuildInPredicate _)  -> return ()
            where
                descr (Operator t _)          = case t of And -> "AND"; Or -> "OR"
                descr (BuildInPredicate pred) = show pred

                writeEdge childLabel = doIO (hPutStrLn file (printf "    %s -> %s;" label childLabel))

