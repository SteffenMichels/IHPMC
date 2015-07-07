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
    , randomFunctions
    , exportAsDot
    , uncondNodeLabel
    , condition
    , deterministicValue
    ) where
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Exception.Synchronous
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

-- NNF nodes "counter for fresh nodes"
data NNF = NNF (HashMap NodeLabel (Node, Set RFuncLabel)) Int

instance Show NNF where
    show _ = "NNF String"

data NodeLabel = NodeLabel String (Set (RFuncLabel, Bool)) deriving (Eq, Ord, Generic)

instance Show NodeLabel where
    show (NodeLabel label conds) = printf "%s|%s" label (List.intercalate "," (fmap showCond $ Set.toAscList conds)) where
        showCond (label, val) = printf "%s=%s" label $ show val

instance Hashable NodeLabel
instance Hashable a => Hashable (Set a) where
    hash set = Hashable.hashWithSalt 0 set
    hashWithSalt salt set = Set.fold (\el hash -> Hashable.hashWithSalt hash el) salt set

data Node = Operator NodeType (Set NodeLabel)
          | BuildInPredicate AST.BuildInPredicate
          | Deterministic Bool
          deriving (Eq, Ord)

data NodeType = And | Or deriving (Eq, Ord)

uncondNodeLabel :: PredicateLabel -> NodeLabel
uncondNodeLabel label = NodeLabel label Set.empty

condNodeLabel :: RFuncLabel -> Bool -> NodeLabel -> NodeLabel
condNodeLabel rFuncLabel rFuncVal (NodeLabel l conds) = NodeLabel l $ Set.insert (rFuncLabel, rFuncVal) conds

empty :: NNF
empty = NNF Map.empty 0

member :: NodeLabel -> NNF -> Bool
member label (NNF nodes _) = Map.member label nodes

insert :: NodeLabel -> Node -> NNF -> NNF
insert label node nnf@(NNF nodes freshCounter) = NNF (Map.insert label (simplifiedNode, rFuncs) nodes) freshCounter
    where
        simplifiedNode = simplify node nnf
        rFuncs = case simplifiedNode of
            Deterministic _ -> Set.empty
            BuildInPredicate pred -> AST.randomFunctions pred
            Operator _ children ->
                Set.fold (\child rfuncs -> Set.union rfuncs $ randomFunctions child nnf) Set.empty children

        simplify :: Node -> NNF -> Node
        simplify node@(Deterministic _) _ = node
        simplify node@(BuildInPredicate pred) _ = case AST.deterministicValue pred of
            Just val -> Deterministic val
            Nothing  -> node
        simplify (Operator operator originalChildren) nnf
            | nChildren == 0 = Deterministic filterValue
            | nChildren == 1 = let singleChildNode   = Set.findMax children
                               in fromJust $ lookUp singleChildNode nnf
            | Foldable.any (\c -> fromJust (lookUp c nnf) == Deterministic singleDeterminismValue) children =
                Deterministic singleDeterminismValue
            | otherwise = Operator operator children
            where
                children = Set.filter (\c -> fromJust (lookUp c nnf) /= Deterministic filterValue) originalChildren
                nChildren = Set.size children
                -- truth value that causes determinism if at least a single child has it
                singleDeterminismValue = if operator == And then False else True
                -- truth value that can be filtered out
                filterValue = if operator == And then True else False

-- possible optimisation: check whether equal node is already in NNF
insertFresh :: Node -> NNF -> (NodeLabel, NNF)
insertFresh node nnf@(NNF nodes freshCounter) = (label, NNF nodes' (freshCounter+1))
    where
        (NNF nodes' _) = insert label node nnf
        label = uncondNodeLabel (show freshCounter)

lookUp :: NodeLabel -> NNF -> Maybe Node
lookUp label (NNF nodes _) = fmap fst $ Map.lookup label nodes

randomFunctions :: NodeLabel -> NNF -> Set RFuncLabel
randomFunctions label (NNF nodes _) = snd $ fromJust $ Map.lookup label nodes

deterministicValue :: NodeLabel -> NNF -> Maybe Bool
deterministicValue label (NNF nodes _) = case fst $ fromJust $ Map.lookup label nodes of
    Deterministic val -> Just val
    _                 -> Nothing

condition :: NodeLabel -> RFuncLabel -> Bool -> NNF -> (NodeLabel, NNF)
condition topLabel rFuncLabel rFuncVal nnf = (topLabel', nnf')
    where
        (topLabel', nnf') = condition' topLabel rFuncLabel rFuncVal nnf
            where
                condition' label rFuncLabel rFuncVal nnf
                    | not $ Set.member rFuncLabel $ randomFunctions label nnf = (label, nnf)
                    | member condLabel nnf                                    = (condLabel, nnf)
                    | otherwise = case node of
                        Operator operator children ->
                            let (condChildren, nnf') = Set.fold
                                    (\child (children, nnf) ->
                                        let (condChild, nnf') = condition child rFuncLabel rFuncVal nnf
                                        in (Set.insert condChild children, nnf')
                                    )
                                    (Set.empty, nnf)
                                    children
                            in (condLabel, insert condLabel (Operator operator condChildren) nnf')
                        BuildInPredicate pred ->
                            (condLabel, insert condLabel (BuildInPredicate $ conditionPred rFuncLabel rFuncVal pred) nnf)
                        Deterministic _ -> error "should not happen as deterministic nodes contains no rfunctions"
                    where
                        condLabel = condNodeLabel rFuncLabel rFuncVal label
                        node      = fromJust $ lookUp label nnf

                conditionPred :: RFuncLabel -> Bool -> AST.BuildInPredicate -> AST.BuildInPredicate
                conditionPred rFuncLabel rFuncVal (AST.BoolEq exprL exprR) = AST.BoolEq (conditionExpr exprL) (conditionExpr exprR)
                    where
                        conditionExpr expr@(AST.BoolConstant _) = expr
                        conditionExpr expr@(AST.UserRFunc exprRFuncLabel)
                            | exprRFuncLabel == rFuncLabel = AST.BoolConstant rFuncVal
                            | otherwise                    = expr

exportAsDot :: FilePath -> NNF -> ExceptionalT String IO ()
exportAsDot path (NNF nodes _) = do
    file <- doIO (openFile path WriteMode)
    doIO (hPutStrLn file "digraph NNF {")
    forM (Map.toList nodes) (printNode file)
    doIO (hPutStrLn file "}")
    doIO (hClose file)
    where
        printNode :: Handle -> (NodeLabel, (Node, Set RFuncLabel)) -> ExceptionalT String IO ()
        printNode file (label, (node, _)) = do
            doIO (hPutStrLn file (printf "    %i[label=\"%s\\n%s\"];" labelHash (show label) (descr node)))
            case node of
                (Operator _ children) -> forM (Set.toList children) writeEdge >> return ()
                _                     -> return ()
            where
                descr (Operator t _)          = case t of And -> "AND"; Or -> "OR"
                descr (BuildInPredicate pred) = show pred
                descr (Deterministic val)     = if val then "TRUE" else "FALSE"

                writeEdge childLabel = doIO (hPutStrLn file (printf "    %i -> %i;" labelHash $ Hashable.hash childLabel))
                labelHash = Hashable.hash label
