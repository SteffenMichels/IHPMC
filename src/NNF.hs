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
    , ComposedLabel(..)
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
import Interval (Interval, IntervalLimit, IntervalLimitPoint(..), LowerUpper(..))
import qualified Interval
import Debug.Trace (trace)

-- NNF nodes "counter for fresh nodes"
data NNF = NNF (HashMap ComposedLabel NNFEntry) Int

data RefWithNode = RefWithNode
    { entryRef    :: NodeRef
    , entryNode   :: Node
    , entryRFuncs :: HashSet RFuncLabel
    , entryScores :: HashMap RFuncLabel (Double, Double)
    } deriving (Eq)
instance Hashable RefWithNode where
    hash rwn              = Hashable.hashWithSalt 0 rwn
    hashWithSalt salt rwn = case entryRef rwn of
        RefComposed (ComposedLabel _ _ _ hash) -> Hashable.hashWithSalt salt hash
        ref                                    -> Hashable.hashWithSalt salt ref

-- last element is stored hash to avoid recomputation
data NodeRef = RefComposed ComposedLabel
             | RefBuildInPredicate AST.BuildInPredicate
             | RefDeterministic Bool
             deriving (Eq, Show, Generic)
instance Hashable NodeRef

--instance Show NodeRef where
--    show (RefOperator (NNFOperatorLabel name bConds rConds _)) = printf
--        "%s|%s"
--        name
--        (List.intercalate "," ((fmap showCondBool $ Map.toList bConds) ++ (fmap showCondReal $ Map.toList rConds)))
--        where
--            showCondBool (rf, val)    = printf "%s=%s"    rf $ show val
--            showCondReal (rf, interv) = printf "%s in %s" rf $ show interv

data ComposedLabel = ComposedLabel String (HashMap RFuncLabel Bool) (HashMap RFuncLabel Interval) Int
                      deriving (Eq, Show)
instance Hashable ComposedLabel where
    hash              (ComposedLabel _ _ _ hash) = hash
    hashWithSalt salt (ComposedLabel _ _ _ hash) = Hashable.hashWithSalt salt hash

-- the NNFEntry contain an NNF operator node, plus additional, redundant, cached information to avoid recomputations
data NNFEntry = NNFEntry NodeType (HashSet NodeRef) (HashSet RFuncLabel) (HashMap RFuncLabel (Double, Double))

data Node = Composed NodeType (HashSet NodeRef)
          | BuildInPredicate AST.BuildInPredicate
          | Deterministic Bool
          deriving (Eq)

data NodeType = And | Or deriving (Eq, Show, Generic)
instance Hashable NodeType

uncondNodeLabel :: RFuncLabel -> ComposedLabel
uncondNodeLabel name = ComposedLabel name Map.empty Map.empty $ Hashable.hash name

condNodeLabelBool :: RFuncLabel -> Bool -> ComposedLabel -> ComposedLabel
condNodeLabelBool = error "uncondNodeLabelBool"
--condNodeLabelBool rFuncLabel rFuncVal (RefOperator l bConds rConds hash) = RefOperator l bConds' rConds hash' where
--    bConds' = Map.insert rFuncLabel rFuncVal bConds
--    hash'   = Hashable.hashWithSalt (Hashable.hashWithSalt hash rFuncVal) rFuncLabel

condNodeLabelReal :: RFuncLabel -> Interval -> ComposedLabel -> ComposedLabel
condNodeLabelReal = error "condNodeLabelReal"
--condNodeLabelReal rf interv (RefOperator l bConds rConds hash) = RefOperator l bConds rConds' hash' where
--    rConds' = Map.insert rf interv rConds
--    hash'   = Hashable.hashWithSalt (Hashable.hashWithSalt hash interv) rf

empty :: NNF
empty = NNF Map.empty 0

member :: ComposedLabel -> NNF -> Bool
member label (NNF nodes _) = Map.member label nodes

insert ::  ComposedLabel -> Node -> NNF -> (RefWithNode, NNF)
insert label node nnf@(NNF nodes freshCounter) = (refWithNode, nnf')
    where
        (refWithNode, nnf') = case simplifiedNode of
            Composed nType nChildren -> ( RefWithNode { entryRef    = RefComposed label
                                                      , entryNode   = simplifiedNode
                                                      , entryRFuncs = rFuncs
                                                      , entryScores = scores
                                                      -- just use label hash, as label uniquely determines content
                                                      }
                                        , NNF (Map.insert label (NNFEntry nType nChildren rFuncs scores) nodes) freshCounter
                                        )
            _                        -> (error "insert", nnf)

        (simplifiedNode, children) = simplify node nnf
        rFuncs = case simplifiedNode of
            Deterministic _       -> Set.empty
            BuildInPredicate pred -> AST.predRandomFunctions pred
            Composed _ _ ->
                Set.foldr (\child rfuncs -> Set.union rfuncs $ entryRFuncs child) Set.empty children

        scores = case simplifiedNode of
            Deterministic _       -> Map.empty
            BuildInPredicate pred -> Map.fromList [(rf, (1.0,1.0)) | rf <- Set.toList rFuncs]
            Composed op _         -> Map.fromList [(rf, scores rf) | rf <- Set.toList rFuncs] where
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
        simplify :: Node -> NNF -> (Node, HashSet RefWithNode)
        simplify node@(Deterministic _) _ = (node, Set.empty)
        simplify node@(BuildInPredicate pred) _ = case AST.deterministicValue pred of
            Just val -> (Deterministic val, Set.empty)
            Nothing  -> (node, Set.empty)
        simplify (Composed operator childLabels) nnf = (simplified, children)
            where
                simplified
                    | nChildren == 0 = (Deterministic filterValue)
                    | nChildren == 1 = entryNode $ getFirst children
                    | Foldable.any (\c -> entryNode c == Deterministic singleDeterminismValue) children =
                        Deterministic singleDeterminismValue
                    | otherwise = Composed operator $ Set.map entryRef children

                originalChildren = Set.map (\c -> augmentWithEntry c nnf) childLabels
                children = Set.filter (\c -> entryNode c /= Deterministic filterValue) originalChildren
                nChildren = Set.size children
                -- truth value that causes determinism if at least a single child has it
                singleDeterminismValue = if operator == And then False else True
                -- truth value that can be filtered out
                filterValue = if operator == And then True else False

insertFresh :: NodeType -> HashSet NodeRef -> NNF -> (RefWithNode, NNF)
insertFresh nType nChildren nnf@(NNF nodes freshCounter) = (entry, NNF nodes' (freshCounter+1))
     where
        (entry, NNF nodes' _) = insert label (Composed nType nChildren) nnf
        label = uncondNodeLabel (show freshCounter)

augmentWithEntry :: NodeRef -> NNF -> RefWithNode
augmentWithEntry label nnf = case tryAugmentWithEntry label nnf of
    Just entry -> entry
    Nothing    -> error $ printf "non-existing NNF node '%s'" $ show label

tryAugmentWithEntry :: NodeRef -> NNF -> Maybe RefWithNode
tryAugmentWithEntry ref@(RefComposed label) (NNF nodes _) = case Map.lookup label nodes of
    Just (NNFEntry nType nChildren rFuncs scores) -> Just RefWithNode
        { entryRef    = ref
        , entryNode   = Composed nType nChildren
        , entryRFuncs = rFuncs
        , entryScores = scores
        }
    Nothing                            -> Nothing
tryAugmentWithEntry ref@(RefBuildInPredicate pred) _ = Just RefWithNode
    { entryRef    = ref
    , entryNode   = BuildInPredicate pred
    , entryRFuncs = rFuncs
    , entryScores = Map.fromList [(rf, (1.0,1.0)) | rf <- Set.toList rFuncs]
    }
    where
        rFuncs = AST.predRandomFunctions pred
tryAugmentWithEntry ref@(RefDeterministic val) _ = Just RefWithNode
    { entryRef    = ref
    , entryNode   = Deterministic val
    , entryRFuncs = Set.empty
    , entryScores = Map.empty
    }

conditionBool :: RefWithNode -> RFuncLabel -> Bool -> NNF -> (RefWithNode, NNF)
conditionBool origNodeEntry rf val nnf
    | not $ Set.member rf $ entryRFuncs origNodeEntry = (origNodeEntry, nnf)

conditionReal :: RefWithNode -> RFuncLabel -> Interval -> HashMap RFuncLabel Interval -> NNF -> (RefWithNode, NNF)
conditionReal origNodeEntry rf interv otherRealChoices nnf@(NNF nodes _)
    | not $ Set.member rf $ entryRFuncs origNodeEntry = (origNodeEntry, nnf)
    | otherwise = case entryRef origNodeEntry of
        RefComposed origLabel _ -> let label = condNodeLabelReal rf interv origLabel
                                   in case Map.lookup label nodes of
                                        Just entry -> (entryRefWithNode entry, nnf)
                                        _ ->
                                            let (condChildren, nnf') = Set.foldr
                                                (\child (children, nnf) ->
                                                    let (condChild, nnf') = conditionReal (NNF.augmentWithEntry child nnf) rf interv nnf
                                                    in (Set.insert condChild children, nnf')
                                                )
                                                (Set.empty, nnf)
                                                children
                                            in insert condLabel (Operator operator $ Set.map entryRef condChildren) nnf'
                                        - ->
    {-| otherwise = case tryAugmentWithEntry condRef nnf of
        Just entry -> (entry, nnf)
        _ -> case (entryRef origNodeEntry, entryNode origNodeEntry) of
            (RefOperator origLabel _, Operator operator children) ->
                let (condLabel, condRef) = condRefBool rf val origLabel
                    (condChildren, nnf') = Set.foldr
                        (\child (children, nnf) ->
                            let (condChild, nnf') = conditionBool (NNF.augmentWithEntry child nnf) rf val nnf
                            in (Set.insert condChild children, nnf')
                        )
                        (Set.empty, nnf)
                        children
                in insert condLabel (Operator operator $ Set.map entryRef condChildren) nnf'
            (_, BuildInPredicate pred) ->
                undefined--insert condRef (BuildInPredicate $ conditionPred pred) nnf
            (_, Deterministic _) -> error "should not happen as deterministic nodes contains no rfunctions"
    where
        conditionPred :: AST.BuildInPredicate -> AST.BuildInPredicate
        conditionPred (AST.BoolEq exprL exprR) = AST.BoolEq (conditionExpr exprL) (conditionExpr exprR)
            where
                conditionExpr expr@(AST.UserRFunc exprRFuncLabel)
                    | exprRFuncLabel == rf = AST.BoolConstant val
                    | otherwise            = expr
                conditionExpr expr = expr
        conditionPred pred = pred-}
{-
conditionReal :: RefWithNode -> RFuncLabel -> Interval -> HashMap RFuncLabel Interval -> NNF -> (RefWithNode, NNF)
conditionReal origNodeEntry rf interv otherRealChoices nnf
    | otherwise = case tryAugmentWithEntry condLabel nnf of
        Just entry -> (entry, nnf)
        _ -> case entryNode origNodeEntry of
            Operator operator children ->
                let (condChildren, nnf') = Set.foldr
                        (\child (children, nnf) ->
                            let (condChild, nnf') = conditionReal (NNF.augmentWithEntry child nnf) rf interv otherRealChoices nnf
                            in (Set.insert condChild children, nnf')
                        )
                        (Set.empty, nnf)
                        children
                in insert condLabel (Operator operator $ Set.map entryRef condChildren) nnf'
            BuildInPredicate pred ->
                insert condLabel (BuildInPredicate $ conditionPred pred) nnf
            Deterministic _ -> error "should not happen as deterministic nodes contains no rfunctions"
    where
        condLabel = condNodeLabelReal rf interv $ NNF.entryRef origNodeEntry

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

                conditions@((firstRf, (firstLower,firstUpper)):otherConditions) = (rf, interv):[(rf',interv) | (rf',interv) <- Map.toList otherRealChoices, Set.member rf' predRFuncs && rf' /= rf]
                corners = foldr (\(rf, (l,u)) corners -> [Map.insert rf (Interval.toPoint Lower l) c | c <- corners] ++ [Map.insert rf (Interval.toPoint Upper u) c | c <- corners]) [Map.fromList [(firstRf, Interval.toPoint Lower firstLower)], Map.fromList [(firstRf, Interval.toPoint Upper firstUpper)]] otherConditions
                predRFuncs = AST.predRandomFunctions pred
        conditionPred pred = pred
-}
exportAsDot :: FilePath -> NNF -> ExceptionalT String IO ()
exportAsDot = undefined
{-
exportAsDot path (NNF nodes _) = do
    file <- doIO (openFile path WriteMode)
    doIO (hPutStrLn file "digraph NNF {")
    forM (Map.toList nodes) (printNode file)
    doIO (hPutStrLn file "}")
    doIO (hClose file)
    where
        printNode :: Handle -> (NodeRef, NNFEntry) -> ExceptionalT String IO ()
        printNode file (label, NNFEntry node _ _ _) = do
            doIO (hPutStrLn file (printf "%i[label=\"%s\\n%s\"];" labelHash (show label) (descr node)))
            case node of
                (Operator _ children) -> forM (Set.toList children) writeEdge >> return ()
                _                     -> return ()
            where
                descr (Operator t _)          = case t of And -> "AND"; Or -> "OR"
                descr (BuildInPredicate pred) = show pred
                descr (Deterministic val)     = if val then "TRUE" else "FALSE"

                writeEdge childLabel = doIO (hPutStrLn file (printf "%i->%i;" labelHash $ Hashable.hash childLabel))
                labelHash = Hashable.hash label-}
