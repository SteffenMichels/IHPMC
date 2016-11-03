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
    , Node
    , NodeType(..)
    , NodeRef
    , refDeterministic
    , refBuildInPredicate
    , refComposed
    , deterministicNodeRef
    , RefWithNode(entryRef, entryCachedInfo)
    , CacheComputations(..)
    , ComposedId
    , Conditions(..)
    , FState
    , empty
    , insert
    , augmentWithEntry
    , labelId
    , exportAsDot
    , uncondComposedLabel
    , uncondComposedLabelExcluded
    , uncondComposedLabelNr
    , conditionBool
    , conditionString
    , conditionReal
    , Formula.negate
    , entryChoices
    , nodeRefToText
    ) where
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import System.IO
import Exception
import Data.Maybe (fromJust, fromMaybe)
import qualified GroundedAST
import qualified AST
import GHC.Generics (Generic)
import Data.Hashable (Hashable)
import qualified Data.Hashable as Hashable
import Interval (Interval)
import qualified Interval
import Control.Monad.State.Strict
import Data.Foldable (foldl')
import Util
import Data.Text (Text)
import qualified Data.Text.Lazy as LT
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as TB
import TextShow
import qualified Data.Text.Lazy.IO as LTIO
import Data.Monoid ((<>))

-- INTERFACE
data Node = Composed NodeType [NodeRef]
          | BuildInPredicateBool   (GroundedAST.TypedBuildInPred Bool) -- don't have to store choices, as rfs are always substituted
          | BuildInPredicateString (GroundedAST.TypedBuildInPred Text)              (HashMap (GroundedAST.PFunc Text) (HashSet Text))
          | BuildInPredicateReal   (GroundedAST.TypedBuildInPred GroundedAST.RealN) (HashMap (GroundedAST.PFunc GroundedAST.RealN) Interval)
          | Deterministic Bool

data RefWithNode cachedInfo = RefWithNode
    { entryRef        :: NodeRef
    , entryNode       :: Node
    , entryLabel      :: Maybe ComposedLabel
    , entryPFuncs     :: HashSet GroundedAST.PFuncLabel
    , entryCachedInfo :: cachedInfo
    }

type FState cachedInfo = State (Formula cachedInfo)

empty :: CacheComputations cachedInfo -> Formula cachedInfo
empty cacheComps = Formula { nodes              = Map.empty
                           , freshCounter       = 0
                           , labels2ids         = Map.empty
                           , buildinCacheString = Map.empty
                           , buildinCacheReal   = Map.empty
                           , cacheComps         = cacheComps
                           }

insert :: ComposedLabel
       -> Bool
       -> NodeType
       -> [NodeRef]
       -> FState cachedInfo (RefWithNode cachedInfo)
insert label sign op children = do
    (simplifiedNode, simplifiedSign) <- simplify op children
    children' <- forM (nodeChildren simplifiedNode) augmentWithEntry
    Formula{cacheComps, freshCounter, labels2ids, nodes} <- get
    let cachedInfo = cachedInfoComposed cacheComps (entryCachedInfo <$> children')
    case simplifiedNode of
        Composed nType nChildren -> do
            let pFuncs = foldl' (\pfuncs child -> Set.union pfuncs $ entryPFuncs child) Set.empty children'
            modify' (\f -> f{ nodes       = Map.insert (ComposedId freshCounter) (label, FormulaEntry nType nChildren pFuncs cachedInfo) nodes
                            , freshCounter = succ freshCounter
                            , labels2ids   = Map.insert label (ComposedId freshCounter) labels2ids
                            }
                   )
            return RefWithNode { entryRef        = RefComposed (sign == simplifiedSign) $ ComposedId freshCounter
                               , entryNode       = simplifiedNode
                               , entryLabel      = Just label
                               , entryPFuncs     = pFuncs
                               , entryCachedInfo = cachedInfo
                               }
        BuildInPredicateBool   prd        -> return $ predRefWithNodeBool   (if sign then prd else GroundedAST.negatePred prd) cachedInfo
        BuildInPredicateString prd sConds -> return $ predRefWithNodeString (if sign then prd else GroundedAST.negatePred prd) sConds cachedInfo
        BuildInPredicateReal   prd rConds -> return $ predRefWithNodeReal   (if sign then prd else GroundedAST.negatePred prd) rConds cachedInfo
        Deterministic val           -> return $ deterministicRefWithNode (val == sign) cachedInfo
    where
    simplify :: NodeType -> [NodeRef] -> FState cachedInfo (Node, Bool)
    simplify operator childRefs = case newChildRefs of
        []          -> return (Deterministic filterValue, True)
        [onlyChild] -> do
            let sign' = case onlyChild of
                    RefComposed sign'' _ -> sign''
                    _                    -> True
            e <- augmentWithEntry onlyChild
            return (entryNode e, sign')
        _ | RefDeterministic singleDeterminismValue `elem`childRefs  ->
            return (Deterministic singleDeterminismValue, True)
        _ ->
            return (Composed operator newChildRefs, True)
        where
        newChildRefs = filter (RefDeterministic filterValue /=) childRefs
        -- truth value that causes determinism if at least a single child has it
        singleDeterminismValue = operator == Or
        -- truth value that can be filtered out
        filterValue = operator == And

    nodeChildren :: Node -> [NodeRef]
    nodeChildren (Composed _ children'') = children''
    nodeChildren _                       = []

augmentWithEntry :: NodeRef -> FState cachedInfo (RefWithNode cachedInfo)
augmentWithEntry ref = fromMaybe (error "Formula: non-existing Formula node")
                       <$>
                       tryAugmentWithEntry ref

tryAugmentWithEntry :: NodeRef -> FState cachedInfo (Maybe (RefWithNode cachedInfo))
tryAugmentWithEntry ref@(RefComposed _ i) = do
    Formula{nodes} <- get
    case Map.lookup i nodes of
        Just (label, FormulaEntry nType nChildren pFuncs cachedInfo) -> return $ Just RefWithNode
            { entryRef        = ref
            , entryNode       = Composed nType nChildren
            , entryLabel      = Just label
            , entryPFuncs     = pFuncs
            , entryCachedInfo = cachedInfo
            }
        Nothing -> return Nothing
tryAugmentWithEntry (RefBuildInPredicateBool prd) = do
    Formula{cacheComps} <- get
    return $ Just $ predRefWithNodeBool prd $ cachedInfoBuildInPredBool cacheComps prd
tryAugmentWithEntry (RefBuildInPredicateString prd sConds) = state (\f@Formula{buildinCacheString, cacheComps} ->
        let (cachedInfo, buildinCache') = cachedInfoBuildInPredCached sConds prd (cachedInfoBuildInPredString cacheComps) buildinCacheString
        in  (Just $ predRefWithNodeString prd sConds cachedInfo, f {buildinCacheString = buildinCache'})
    )
tryAugmentWithEntry (RefBuildInPredicateReal prd rConds) = state (\f@Formula{buildinCacheReal, cacheComps} ->
        let (cachedInfo, buildinCache') = cachedInfoBuildInPredCached rConds prd (cachedInfoBuildInPredReal cacheComps) buildinCacheReal
        in  (Just $ predRefWithNodeReal prd rConds cachedInfo, f {buildinCacheReal = buildinCache'})
    )
tryAugmentWithEntry (RefDeterministic val) = do
    Formula{cacheComps} <- get
    return $ Just $ deterministicRefWithNode val $ cachedInfoDeterministic cacheComps val

predRefWithNodeBool :: GroundedAST.TypedBuildInPred Bool
                    -> cachedInfo
                    -> RefWithNode cachedInfo
predRefWithNodeBool prd =
    predRefWithNode prd (RefBuildInPredicateBool prd) (BuildInPredicateBool prd)

predRefWithNodeString :: GroundedAST.TypedBuildInPred Text
                      -> HashMap (GroundedAST.PFunc Text) (HashSet Text)
                      -> cachedInfo
                      -> RefWithNode cachedInfo
predRefWithNodeString prd sConds =
    predRefWithNode prd (RefBuildInPredicateString prd sConds) (BuildInPredicateString prd sConds)

predRefWithNodeReal :: GroundedAST.TypedBuildInPred GroundedAST.RealN
                    -> HashMap (GroundedAST.PFunc GroundedAST.RealN) Interval
                    -> cachedInfo
                    -> RefWithNode cachedInfo
predRefWithNodeReal prd rConds =
    predRefWithNode prd (RefBuildInPredicateReal prd rConds) (BuildInPredicateReal prd rConds)

predRefWithNode :: GroundedAST.TypedBuildInPred a
                -> NodeRef
                -> Node
                -> cachedInfo
                -> RefWithNode cachedInfo
predRefWithNode prd ref node cachedInfo = RefWithNode
    { entryRef        = ref
    , entryNode       = node
    , entryLabel      = Nothing
    , entryPFuncs     = Set.map GroundedAST.probabilisticFuncLabel $ GroundedAST.predProbabilisticFunctions prd
    , entryCachedInfo = cachedInfo
    }

deterministicRefWithNode :: Bool -> cachedInfo -> RefWithNode cachedInfo
deterministicRefWithNode val cachedInfo = RefWithNode
    { entryRef        = RefDeterministic val
    , entryNode       = Deterministic val
    , entryLabel      = Nothing
    , entryPFuncs     = Set.empty
    , entryCachedInfo = cachedInfo
    }

entryChoices :: RefWithNode cachedInfo -> Conditions
entryChoices entry = case entryRef entry of
    RefBuildInPredicateBool _           -> Conditions Map.empty Map.empty Map.empty
    RefBuildInPredicateString _ choices -> Conditions Map.empty choices Map.empty
    RefBuildInPredicateReal _ choices   -> Conditions Map.empty Map.empty choices
    _ -> case entryLabel entry of
        Just (ComposedLabel _ conds _) -> conds
        _ -> Conditions Map.empty Map.empty Map.empty

conditionBool :: RefWithNode cachedInfo
              -> GroundedAST.PFunc Bool
              -> Bool
              -> FState cachedInfo (RefWithNode cachedInfo)
conditionBool origNodeEntry pf val
    | not $ Set.member (GroundedAST.probabilisticFuncLabel pf) $ entryPFuncs origNodeEntry = return origNodeEntry
    | otherwise = case entryRef origNodeEntry of
        RefComposed sign origId -> conditionComposed sign origNodeEntry origId pf
                                       (\pf' label -> condComposedLabelBool pf' val label)
                                       (\ref pf' -> conditionBool ref pf' val)
        RefBuildInPredicateBool prd -> do
            Formula{cacheComps} <- get
            return $ case GroundedAST.deterministicValueTyped condPred of
                Just val' -> deterministicRefWithNode val' $ cachedInfoDeterministic cacheComps val'
                Nothing   -> predRefWithNodeBool condPred $ cachedInfoBuildInPredBool cacheComps condPred
            where
            condPred = conditionPred prd
        RefBuildInPredicateString prd sConds -> do
            Formula{cacheComps, buildinCacheString} <- get
            return $ predRefWithNodeString prd sConds
                   $ fst $ cachedInfoBuildInPredCached sConds prd (cachedInfoBuildInPredString cacheComps) buildinCacheString
        RefBuildInPredicateReal prd rConds -> do
            Formula{cacheComps, buildinCacheReal} <- get
            return $ predRefWithNodeReal prd rConds
                   $ fst $ cachedInfoBuildInPredCached rConds prd (cachedInfoBuildInPredReal cacheComps) buildinCacheReal
        RefDeterministic _ -> error "should not happen as deterministic nodes contain no pfunctions"
    where
        conditionPred :: GroundedAST.TypedBuildInPred Bool -> GroundedAST.TypedBuildInPred Bool
        conditionPred (GroundedAST.Equality eq exprL exprR) = GroundedAST.Equality eq (conditionExpr exprL) (conditionExpr exprR)
            where
            conditionExpr :: GroundedAST.Expr Bool -> GroundedAST.Expr Bool
            conditionExpr expr@(GroundedAST.PFuncExpr exprPFunc)
                | exprPFunc == pf = GroundedAST.ConstantExpr $ GroundedAST.BoolConstant val
                | otherwise       = expr
            conditionExpr expr = expr
        conditionPred prd = prd

conditionString :: RefWithNode cachedInfo
                -> GroundedAST.PFunc Text
                -> HashSet Text
                -> FState cachedInfo (RefWithNode cachedInfo)
conditionString origNodeEntry pf condSet
    | not $ Set.member (GroundedAST.probabilisticFuncLabel pf) $ entryPFuncs origNodeEntry = return origNodeEntry
    | otherwise = case entryRef origNodeEntry of
        RefComposed sign origId -> conditionComposed sign origNodeEntry origId pf
                                       (\pf' label -> condComposedLabelString pf' condSet label)
                                       (\ref pf' -> conditionString ref pf' condSet)
        RefBuildInPredicateString prd sConds -> do
            Formula{cacheComps, buildinCacheString} <- get
            case GroundedAST.deterministicValueTyped condPred of
                Just val' -> return $ deterministicRefWithNode val' $ cachedInfoDeterministic cacheComps val'
                Nothing -> do
                    let (cachedInfo, buildinCache') = cachedInfoBuildInPredCached sConds' condPred (cachedInfoBuildInPredString cacheComps) buildinCacheString
                    modify' (\f -> f {buildinCacheString = buildinCache'})
                    return $ predRefWithNodeString condPred sConds' cachedInfo
            where
            sConds' = Map.insert pf condSet sConds
            condPred = conditionPred prd sConds'
        RefBuildInPredicateBool prd -> do
            Formula{cacheComps} <- get
            return $ predRefWithNodeBool prd $ cachedInfoBuildInPredBool cacheComps prd
        RefBuildInPredicateReal prd rConds -> do
            Formula{cacheComps, buildinCacheReal} <- get
            return $ predRefWithNodeReal prd rConds
                   $ fst $ cachedInfoBuildInPredCached rConds prd (cachedInfoBuildInPredReal cacheComps) buildinCacheReal
        RefDeterministic _ -> error "should not happen as deterministic nodes contain no pfunctions"
    where
        conditionPred :: GroundedAST.TypedBuildInPred Text
                      -> HashMap (GroundedAST.PFunc Text) (HashSet Text)
                      -> GroundedAST.TypedBuildInPred Text
        conditionPred prd@(GroundedAST.Equality eq left right) sConds
            | Set.size possibleLeft == 1 && Set.size possibleRight == 1 =
                GroundedAST.Constant $ eq == (getFirst possibleLeft == getFirst possibleRight)
            | null $ Set.intersection possibleLeft possibleRight =
                let val = not eq
                in  GroundedAST.Constant val
            | otherwise = prd
            where
            possibleLeft  = GroundedAST.possibleValues left sConds
            possibleRight = GroundedAST.possibleValues right sConds
        conditionPred prd _ = prd

conditionReal :: RefWithNode cachedInfo
              -> GroundedAST.PFunc GroundedAST.RealN
              -> Interval
              -> FState cachedInfo (RefWithNode cachedInfo)
conditionReal origNodeEntry pf interv
    | not $ Set.member (GroundedAST.probabilisticFuncLabel pf) $ entryPFuncs origNodeEntry = return origNodeEntry
    | otherwise = case entryRef origNodeEntry of
        RefComposed sign origId -> conditionComposed sign origNodeEntry origId pf
                                       (\pf' label -> condComposedLabelReal pf' interv label)
                                       (\ref pf' -> conditionReal ref pf' interv)
        RefBuildInPredicateReal prd rConds -> do
            Formula{cacheComps, buildinCacheReal} <- get
            case GroundedAST.deterministicValueTyped condPred of
                Just val' -> return $ deterministicRefWithNode val' $ cachedInfoDeterministic cacheComps val'
                Nothing -> do
                    let (cachedInfo, buildinCache') = cachedInfoBuildInPredCached rConds' condPred (cachedInfoBuildInPredReal cacheComps) buildinCacheReal
                    modify' (\f -> f {buildinCacheReal=buildinCache'})
                    return $ predRefWithNodeReal condPred rConds' cachedInfo
            where
            rConds' = Map.insert pf interv rConds
            condPred = conditionPred prd rConds'
        RefBuildInPredicateBool prd -> do
            Formula{cacheComps} <- get
            return $ predRefWithNodeBool prd $ cachedInfoBuildInPredBool cacheComps prd
        RefBuildInPredicateString prd sConds -> do
            Formula{cacheComps, buildinCacheString} <- get
            return $ predRefWithNodeString prd sConds
                   $ fst $ cachedInfoBuildInPredCached sConds prd (cachedInfoBuildInPredString cacheComps) buildinCacheString
        RefDeterministic _ -> error "should not happen as deterministic nodes contain no pfunctions"
    where
        conditionPred :: GroundedAST.TypedBuildInPred GroundedAST.RealN
                      -> HashMap (GroundedAST.PFunc GroundedAST.RealN) Interval
                      -> GroundedAST.TypedBuildInPred GroundedAST.RealN
        conditionPred prd@(GroundedAST.Ineq op left right) rConds
            -- check if choice is made for all 'pFuncs' in 'prd'
            | length conditions == Set.size predPFuncs = conditionPred'
            | otherwise = prd
            where
            conditionPred'
                | all ((==) $ Just True)  checkedPreds = GroundedAST.Constant True
                | all ((==) $ Just False) checkedPreds = GroundedAST.Constant False
                | otherwise                            = prd

            checkedPreds = map (GroundedAST.checkRealIneqPred op left right) crns
            conditions   = (pf, interv):[(pf',interv') | (pf',interv') <- Map.toList rConds, Set.member pf' predPFuncs && pf' /= pf]
            crns         = Interval.corners conditions
            predPFuncs   = GroundedAST.predProbabilisticFunctions prd
        conditionPred prd _ = prd

conditionComposed :: Bool
                  -> RefWithNode cachedInfo
                  -> ComposedId
                  -> GroundedAST.PFunc a
                  -> (GroundedAST.PFunc a -> ComposedLabel -> ComposedLabel)
                  -> (RefWithNode cachedInfo -> GroundedAST.PFunc a -> FState cachedInfo (RefWithNode cachedInfo))
                  -> FState cachedInfo (RefWithNode cachedInfo)
conditionComposed sign origNodeEntry origLabel pf labelFunc conditionFunc = do
            Formula{labels2ids, nodes} <- get
            case Map.lookup newLabel labels2ids of
                Just nodeId -> augmentWithEntry $ RefComposed sign nodeId
                _ -> do
                    let (_, FormulaEntry op children _ _) = fromJust $ Map.lookup origLabel nodes
                    condChildren <- forM
                        children
                        (\child -> do
                            condRef   <- Formula.augmentWithEntry child
                            conditionFunc condRef pf
                        )
                    insert newLabel sign op $ map entryRef condChildren
            where
            newLabel = labelFunc pf $ fromJust $ entryLabel origNodeEntry

negate :: NodeRef -> NodeRef
negate (RefComposed sign refId)               = RefComposed (not sign) refId
negate (RefBuildInPredicateBool   prd)        = RefBuildInPredicateBool   (GroundedAST.negatePred prd)
negate (RefBuildInPredicateString prd sConds) = RefBuildInPredicateString (GroundedAST.negatePred prd) sConds
negate (RefBuildInPredicateReal   prd rConds) = RefBuildInPredicateReal   (GroundedAST.negatePred prd) rConds
negate (RefDeterministic val)                 = RefDeterministic $ not val

exportAsDot :: FilePath -> Formula cachedInfo -> HashMap Int Text -> HashMap Int (Int, [AST.ConstantExpr]) -> ExceptionalT IOException IO ()
exportAsDot path Formula{nodes} ids2str ids2label = do
    file <- doIO (openFile path WriteMode)
    doIO (hPutStrLn file "digraph Formula {")
    forM_ (Map.toList nodes) (printNode file)
    doIO (hPutStrLn file "}")
    doIO (hClose file)
    where
        printNode :: Handle -> (ComposedId, (ComposedLabel, FormulaEntry cachedInfo)) -> ExceptionalT IOException IO ()
        printNode file (ComposedId i, (label, FormulaEntry op children _ _)) = do
            doIO ( LTIO.hPutStrLn file $ TB.toLazyText $
                       showb i <>
                       "[label=\"" <>
                       showb i <>
                       ": " <>
                       TB.fromLazyText (LT.replace "\"" "\\\"" $ TB.toLazyText $ composedLabelToText label ids2str ids2label) <>
                       "\\n" <>
                       descr <>
                       "\"];"
                 )
            void $ forM_ children writeEdge
            where
                descr = case op of And -> "AND"; Or -> "OR"
                writeEdge childRef = doIO $ LTIO.hPutStrLn file $ TB.toLazyText $ showb i <> "<-" <> showb (childStr childRef) <> ";"

                childStr :: NodeRef -> Builder
                childStr (RefComposed sign (ComposedId childId)) = showb childId <> "[label=\"" <> showb sign <> "\"]"
                childStr (RefBuildInPredicateBool prd)           = printPrd prd
                childStr (RefBuildInPredicateString prd _)       = printPrd prd
                childStr (RefBuildInPredicateReal prd _)         = printPrd prd
                childStr (RefDeterministic _)                    = error "Formula export: should this happen?"

                printPrd :: GroundedAST.TypedBuildInPred a -> Builder
                printPrd prd = showb h <>
                               ";\n" <>
                               showb h <>
                               "[label=\"" <>
                               TB.fromLazyText (LT.replace "\"" "\\\"" $ TB.toLazyText $ GroundedAST.typedBuildInPredToText prd ids2str ids2label) <>
                               "\"]"
                    where
                    h = Hashable.hashWithSalt (Hashable.hash i) prd

-- FORMULA STORAGE
data Formula cachedInfo = Formula
    { nodes              :: HashMap ComposedId (ComposedLabel, FormulaEntry cachedInfo)           -- graph representing formulas
    , freshCounter       :: Int                                                                   -- counter for fresh nodes
    , labels2ids         :: HashMap ComposedLabel ComposedId                                      -- map from composed label to composed ids (ids are used for performance, as ints are most effecient as keys in the graph map)
    , buildinCacheString :: HashMap (GroundedAST.TypedBuildInPred Text,              HashMap (GroundedAST.PFunc Text) (HashSet Text))        cachedInfo -- cache for buildin predicates
    , buildinCacheReal   :: HashMap (GroundedAST.TypedBuildInPred GroundedAST.RealN, HashMap (GroundedAST.PFunc GroundedAST.RealN) Interval) cachedInfo -- cache for buildin predicates
    , cacheComps         :: CacheComputations cachedInfo                                          -- how cached information attached to formulas is computed
    }

newtype ComposedId = ComposedId Int deriving (Eq, Generic)
instance Hashable ComposedId

data ComposedLabel = ComposedLabel
    PredicateLabel -- label
    Conditions     -- conditions
    Int            -- stored hash to avoid recomputation
    deriving Eq

instance Hashable ComposedLabel
    where
    hashWithSalt salt (ComposedLabel _ _ hash) = Hashable.hashWithSalt salt hash

data PredicateLabel = PredicateLabel GroundedAST.PredicateLabel PredicateLabelModifier deriving Eq
data PredicateLabelModifier = No
                            | BodyNr Int
                            | ExcludingChildren (HashSet GroundedAST.PredicateLabel)
                            deriving Eq

-- conditioned formulas
data Conditions = Conditions { boolConds   :: HashMap (GroundedAST.PFunc Bool) Bool
                             , stringConds :: HashMap (GroundedAST.PFunc Text) (HashSet Text)
                             , realConds   :: HashMap (GroundedAST.PFunc GroundedAST.RealN) Interval
                             }
                             deriving Eq

composedLabelToText :: ComposedLabel -> HashMap Int Text -> HashMap Int (Int, [AST.ConstantExpr]) -> Builder
composedLabelToText (ComposedLabel (PredicateLabel label modif) Conditions{boolConds, stringConds, realConds} _) ids2str ids2label =
    GroundedAST.predicateLabelToText label ids2str ids2label <>
    (case modif of
        No                         -> ""
        BodyNr nr                  -> "#" <> showb nr
        ExcludingChildren excluded -> "-" <> toTextLst (Set.toList excluded) (\x -> GroundedAST.predicateLabelToText x ids2str ids2label)
    ) <>
    "|" <>
    showbLst (
        (showCondBool                               <$> Map.toList boolConds)   ++
        ((\x -> showCondString x ids2str ids2label) <$> Map.toList stringConds) ++
        ((\x -> showCondReal   x ids2str ids2label) <$> Map.toList realConds)
    )
    where
        showCondBool (pf, val) = GroundedAST.pFuncToText pf ids2str ids2label <> "=" <> showb val

uncondComposedLabel :: GroundedAST.PredicateLabel -> ComposedLabel
uncondComposedLabel label = ComposedLabel (PredicateLabel label No) (Conditions Map.empty Map.empty Map.empty) $ Hashable.hash label

uncondComposedLabelExcluded :: GroundedAST.PredicateLabel -> HashSet GroundedAST.PredicateLabel -> ComposedLabel
uncondComposedLabelExcluded label excluded =
    ComposedLabel (PredicateLabel label $ ExcludingChildren excluded) (Conditions Map.empty Map.empty Map.empty) $ Hashable.hashWithSalt (Hashable.hash label) excluded

uncondComposedLabelNr :: GroundedAST.PredicateLabel -> Int -> ComposedLabel
uncondComposedLabelNr label nr =
    ComposedLabel (PredicateLabel label $ BodyNr nr) (Conditions Map.empty Map.empty Map.empty) $ Hashable.hashWithSalt (Hashable.hash label) nr

condComposedLabelBool :: GroundedAST.PFunc Bool -> Bool -> ComposedLabel -> ComposedLabel
condComposedLabelBool pf val (ComposedLabel label conds hash) = ComposedLabel label conds{boolConds = bConds} hash'
    where
    bConds = Map.insert pf val $ boolConds conds
    hash'  = hash + Hashable.hashWithSalt (Hashable.hash pf) val

condComposedLabelString :: GroundedAST.PFunc Text -> HashSet Text -> ComposedLabel -> ComposedLabel
condComposedLabelString pf condSet (ComposedLabel label conds hash) = ComposedLabel label conds{stringConds = sConds} hash''
    where
    sConds  = Map.insert pf condSet $ stringConds conds
    hashPf  = Hashable.hash pf
    hash'   = hash + Hashable.hashWithSalt hashPf condSet
    hash''  = case Map.lookup pf $ stringConds conds of
        Just condSet' -> hash' - Hashable.hashWithSalt hashPf condSet'
        Nothing       -> hash'

condComposedLabelReal :: GroundedAST.PFunc GroundedAST.RealN -> Interval -> ComposedLabel -> ComposedLabel
condComposedLabelReal pf interv (ComposedLabel label conds hash) = ComposedLabel label conds{realConds = rConds} hash''
    where
    rConds  = Map.insert pf interv $ realConds conds
    hashPf  = Hashable.hash pf
    hash'   = hash + Hashable.hashWithSalt hashPf interv
    hash''  = case Map.lookup pf $ realConds conds of
        Just interv' -> hash' - Hashable.hashWithSalt hashPf interv'
        Nothing      -> hash'

labelId :: ComposedLabel -> FState cachednInfo (Maybe ComposedId)
labelId label = gets labels2ids >>= \l2ids -> return $ Map.lookup label l2ids

-- the FormulaEntry contains composed node, plus additional, redundant, cached information to avoid recomputations
data FormulaEntry cachedInfo = FormulaEntry NodeType [NodeRef] (HashSet GroundedAST.PFuncLabel) cachedInfo

data NodeType = And | Or deriving (Eq, Generic)
instance Hashable NodeType

-- node refs are used for optimisation, to avoid looking up leaves (build in preds and deterministic nodes) in the graph
data NodeRef = RefComposed Bool ComposedId
             | RefBuildInPredicateBool   (GroundedAST.TypedBuildInPred Bool) -- don't have to store choices, as rfs are always substituted
             | RefBuildInPredicateString (GroundedAST.TypedBuildInPred Text)              (HashMap (GroundedAST.PFunc Text) (HashSet Text))
             | RefBuildInPredicateReal   (GroundedAST.TypedBuildInPred GroundedAST.RealN) (HashMap (GroundedAST.PFunc GroundedAST.RealN) Interval)
             | RefDeterministic Bool
             deriving Eq

nodeRefToText :: NodeRef -> HashMap Int Text -> HashMap Int (Int, [AST.ConstantExpr]) -> Builder
nodeRefToText (RefComposed sign (ComposedId cid)) _ _ = if sign then "" else "-" <> showb cid
nodeRefToText (RefBuildInPredicateBool prd) ids2str ids2label = GroundedAST.typedBuildInPredToText prd ids2str ids2label
nodeRefToText (RefBuildInPredicateString prd sConds) ids2str ids2label =
   GroundedAST.typedBuildInPredToText prd ids2str ids2label <>
   "|\n  " <>
   toTextLstEnc "" ",\n" (Map.toList sConds) (\x -> showCondString x ids2str ids2label)
nodeRefToText (RefBuildInPredicateReal prd rConds) ids2str ids2label =
   GroundedAST.typedBuildInPredToText prd ids2str ids2label <>
   "|\n " <>
   toTextLstEnc "" ",\n" (Map.toList rConds) (\x -> showCondReal x ids2str ids2label)
nodeRefToText (RefDeterministic val) _ _ = showb val

showCondString :: (GroundedAST.PFunc Text, HashSet Text) -> HashMap Int Text -> HashMap Int (Int, [AST.ConstantExpr]) -> Builder
showCondString (pf, condSet) ids2str ids2label =
    GroundedAST.pFuncToText pf ids2str ids2label <> " in {" <> TB.fromLazyText (LT.replace "\"" "" $ TB.toLazyText $ showbLst $ Set.toList condSet) <> "}"

showCondReal :: (GroundedAST.PFunc GroundedAST.RealN, Interval) -> HashMap Int Text -> HashMap Int (Int, [AST.ConstantExpr]) -> Builder
showCondReal (pf, Interval.Interval l r) ids2str ids2label =
    GroundedAST.pFuncToText pf ids2str ids2label <> " in (" <> showb l <> "," <> showb r <> ")"

refDeterministic :: Bool -> NodeRef
refDeterministic = RefDeterministic

refBuildInPredicate :: GroundedAST.BuildInPredicate -> NodeRef
refBuildInPredicate prd = case GroundedAST.deterministicValue prd of
    Just val -> RefDeterministic val
    Nothing  -> case prd of
        GroundedAST.BuildInPredicateBool prd' -> RefBuildInPredicateBool   prd'
        GroundedAST.BuildInPredicateReal prd' -> RefBuildInPredicateReal   prd' Map.empty
        GroundedAST.BuildInPredicateStr  prd' -> RefBuildInPredicateString prd' Map.empty
        GroundedAST.BuildInPredicateInt  _    -> undefined

refComposed :: ComposedId -> NodeRef
refComposed = RefComposed True

deterministicNodeRef :: NodeRef -> Maybe Bool
deterministicNodeRef (RefDeterministic val) = Just val
deterministicNodeRef _                      = Nothing

data CacheComputations cachedInfo = CacheComputations
    { cachedInfoComposed          :: [cachedInfo]                                                                                             -> cachedInfo
    , cachedInfoBuildInPredBool   ::                                                           GroundedAST.TypedBuildInPred Bool              -> cachedInfo
    , cachedInfoBuildInPredString :: HashMap (GroundedAST.PFunc Text) (HashSet Text)        -> GroundedAST.TypedBuildInPred Text              -> cachedInfo
    , cachedInfoBuildInPredReal   :: HashMap (GroundedAST.PFunc GroundedAST.RealN) Interval -> GroundedAST.TypedBuildInPred GroundedAST.RealN -> cachedInfo
    , cachedInfoDeterministic     :: Bool                                                                                                     -> cachedInfo
    }

-- to avoid recomputation
cachedInfoBuildInPredCached :: (Eq a, Hashable a)
                            => HashMap (GroundedAST.PFunc b) a
                            -> GroundedAST.TypedBuildInPred b
                            -> (HashMap (GroundedAST.PFunc b) a -> GroundedAST.TypedBuildInPred b -> cachedInfo)
                            -> HashMap (GroundedAST.TypedBuildInPred b, HashMap (GroundedAST.PFunc b) a) cachedInfo
                            -> (cachedInfo, HashMap (GroundedAST.TypedBuildInPred b, HashMap (GroundedAST.PFunc b) a) cachedInfo)
cachedInfoBuildInPredCached conds prd infoComp cache = case Map.lookup (prd,conds) cache of
    Just cachedInfo -> (cachedInfo, cache)
    Nothing         -> let cachedInfo = infoComp conds prd
                       in  (cachedInfo, Map.insert (prd,conds) cachedInfo cache)
