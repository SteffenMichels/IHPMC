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
    , allScores
    , exportAsDot
    , uncondNodeLabel
    , conditionBool
    , conditionReal
    , deterministicValue
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
import Interval (Interval)
import qualified Interval

-- NNF nodes(node itself, rfuncs, heuristicScores) "counter for fresh nodes"
data NNF = NNF (HashMap NodeLabel (Node, HashSet RFuncLabel, HashMap RFuncLabel (Double, Double))) Int

instance Show NNF where
    show (NNF nodes _) = show nodes

data NodeLabel = NodeLabel String (HashSet (RFuncLabel, Bool)) (HashSet (RFuncLabel, Interval)) deriving (Eq, Generic)

instance Show NodeLabel where
    show (NodeLabel label bConds rConds) = printf
        "%s|%s"
        label
        (List.intercalate "," ((fmap showCondBool $ Set.toList bConds) ++ (fmap showCondReal $ Set.toList rConds)))
        where
            showCondBool (rf, val)    = printf "%s=%s"    rf $ show val
            showCondReal (rf, interv) = printf "%s in %s" rf $ show interv
instance Hashable NodeLabel

data Node = Operator NodeType (HashSet NodeLabel)
          | BuildInPredicate AST.BuildInPredicate
          | Deterministic Bool
          deriving (Eq, Show)

data NodeType = And | Or deriving (Eq, Show, Generic)
instance Hashable NodeType

uncondNodeLabel :: PredicateLabel -> NodeLabel
uncondNodeLabel label = NodeLabel label Set.empty Set.empty

condNodeLabelBool :: RFuncLabel -> Bool -> NodeLabel -> NodeLabel
condNodeLabelBool rFuncLabel rFuncVal (NodeLabel l bConds rConds) = NodeLabel l (Set.insert (rFuncLabel, rFuncVal) bConds) rConds

condNodeLabelReal :: RFuncLabel -> Interval -> NodeLabel -> NodeLabel
condNodeLabelReal rFuncLabel interv (NodeLabel l bConds rConds) = NodeLabel l bConds (Set.insert (rFuncLabel, interv) rConds)

empty :: NNF
empty = NNF Map.empty 0

member :: NodeLabel -> NNF -> Bool
member label (NNF nodes _) = Map.member label nodes

insert :: NodeLabel -> Node -> NNF -> NNF
insert label node nnf@(NNF nodes freshCounter) = NNF (Map.insert label (simplifiedNode, rFuncs, scores) nodes) freshCounter
    where
        simplifiedNode = simplify node nnf
        rFuncs = case simplifiedNode of
            Deterministic _       -> Set.empty
            BuildInPredicate pred -> AST.randomFunctions pred
            Operator _ children ->
                Set.foldr (\child rfuncs -> Set.union rfuncs $ randomFunctions child nnf) Set.empty children

        scores = case simplifiedNode of
            Deterministic _       -> Map.empty
            BuildInPredicate pred -> Map.fromList [(rf, (1.0,1.0)) | rf <- Set.toList rFuncs]
            Operator op children  -> Map.fromList [(rf, scores rf) | rf <- Set.toList rFuncs] where
                scores rf = case op of
                    NNF.And -> (posScore/nRFuncs, negScore)
                    NNF.Or  -> (posScore, negScore/nRFuncs)
                    where
                    (posScore, negScore) = foldr (\childScores (posScore, negScore) ->
                                                    let (cPosScore, cNegScore) = Map.lookupDefault (0.0,0.0) rf childScores
                                                    in  (posScore+cPosScore, negScore+cNegScore)
                                                 )
                                                 (0.0, 0.0)
                                                 childrenScores
                childrenScores = [allScores c nnf | c <- Set.toList children]
        nRFuncs = fromIntegral (Set.size rFuncs)

        simplify :: Node -> NNF -> Node
        simplify node@(Deterministic _) _ = node
        simplify node@(BuildInPredicate pred) _ = case AST.deterministicValue pred of
            Just val -> Deterministic val
            Nothing  -> node
        simplify (Operator operator originalChildren) nnf
            | nChildren == 0 = Deterministic filterValue
            | nChildren == 1 = let singleChildNode   = getFirst children
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
lookUp label (NNF nodes _) = fmap (\(x,_,_) -> x) $ Map.lookup label nodes

randomFunctions :: NodeLabel -> NNF -> HashSet RFuncLabel
randomFunctions label (NNF nodes _) = (\(_,x,_) -> x) . fromJust $ Map.lookup label nodes

allScores :: NodeLabel -> NNF -> HashMap RFuncLabel (Double, Double)
allScores label (NNF nodes _) = (\(_,_,x) -> x) . fromJust $ Map.lookup label nodes

deterministicValue :: NodeLabel -> NNF -> Maybe Bool
deterministicValue label (NNF nodes _) = case (\(x,_,_) -> x) . fromJust $ Map.lookup label nodes of
    Deterministic val -> Just val
    _                 -> Nothing

conditionBool :: NodeLabel -> RFuncLabel -> Bool -> NNF -> (NodeLabel, NNF)
conditionBool nodeLabel rf val nnf
    | not $ Set.member rf $ randomFunctions nodeLabel nnf = (nodeLabel, nnf)
    | member condLabel nnf                                = (condLabel, nnf)
    | otherwise = case node of
        Operator operator children ->
            let (condChildren, nnf') = Set.foldr
                    (\child (children, nnf) ->
                        let (condChild, nnf') = conditionBool child rf val nnf
                        in (Set.insert condChild children, nnf')
                    )
                    (Set.empty, nnf)
                    children
            in (condLabel, insert condLabel (Operator operator condChildren) nnf')
        BuildInPredicate pred ->
            (condLabel, insert condLabel (BuildInPredicate $ conditionPred pred) nnf)
        Deterministic _ -> error "should not happen as deterministic nodes contains no rfunctions"
    where
        condLabel = condNodeLabelBool rf val nodeLabel
        node      = fromJust $ lookUp nodeLabel nnf

        conditionPred :: AST.BuildInPredicate -> AST.BuildInPredicate
        conditionPred (AST.BoolEq exprL exprR) = AST.BoolEq (conditionExpr exprL) (conditionExpr exprR)
            where
                conditionExpr expr@(AST.UserRFunc exprRFuncLabel)
                    | exprRFuncLabel == rf = AST.BoolConstant val
                    | otherwise            = expr
                conditionExpr expr = expr
        conditionPred pred = pred

conditionReal :: NodeLabel -> RFuncLabel -> Interval -> NNF -> (NodeLabel, NNF)
conditionReal nodeLabel rf interv nnf
    | not $ Set.member rf $ randomFunctions nodeLabel nnf = (nodeLabel, nnf)
    | member condLabel nnf                                = (condLabel, nnf)
    | otherwise = case node of
        Operator operator children ->
            let (condChildren, nnf') = Set.foldr
                    (\child (children, nnf) ->
                        let (condChild, nnf') = conditionReal child rf interv nnf
                        in (Set.insert condChild children, nnf')
                    )
                    (Set.empty, nnf)
                    children
            in (condLabel, insert condLabel (Operator operator condChildren) nnf')
        BuildInPredicate pred ->
            (condLabel, insert condLabel (BuildInPredicate $ conditionPred pred) nnf)
        Deterministic _ -> error "should not happen as deterministic nodes contains no rfunctions"
    where
        condLabel = condNodeLabelReal rf interv nodeLabel
        node      = fromJust $ lookUp nodeLabel nnf

        conditionPred :: AST.BuildInPredicate -> AST.BuildInPredicate
        conditionPred pred@(AST.RealIn predRf predInterv)
            | predRf == rf && Interval.subsetEq interv predInterv  = AST.Constant True
            | predRf == rf && Interval.disjoint interv predInterv  = AST.Constant False
            | otherwise = pred
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
        printNode :: Handle -> (NodeLabel, (Node, HashSet RFuncLabel, HashMap RFuncLabel (Double, Double))) -> ExceptionalT String IO ()
        printNode file (label, (node, _, _)) = do
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
