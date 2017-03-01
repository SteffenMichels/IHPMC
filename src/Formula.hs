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
    , PredicateId(..)
    , PredicateLabel(..)
    , Conditions(..)
    , noConditions
    , ObjCondition(..)
    , FState
    , empty
    , insert
    , augmentWithEntry
    , augmentWithEntryRef
    , labelId
    , exportAsDot
    , evidenceComposedLabel
    , uncondComposedLabel
    , condition
    , reference
    , dereference
    , Formula.negate
    , entryChoices
    , nodeRefToText
    ) where
import Data.HashMap (Map)
import qualified Data.HashMap as Map
import Data.HashSet (Set)
import qualified Data.HashSet as Set
import System.IO
import Exception
import Data.Maybe (fromJust)
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
import qualified Data.Text.Lazy.Builder as TB
import TextShow
import qualified Data.Text.Lazy.IO as LTIO
import Data.Monoid ((<>))
import Control.Arrow (first)
import qualified Data.List as List

-- INTERFACE
data Node = Composed !NodeType ![NodeRef]
          | BuildInPredicateBool   (GroundedAST.TypedBuildInPred Bool) -- don't have to store choices, as rfs are always substituted
          | BuildInPredicateString (GroundedAST.TypedBuildInPred Text)               (Map GroundedAST.PFuncLabel (Set Text))
          | BuildInPredicateReal   (GroundedAST.TypedBuildInPred GroundedAST.RealN)  (Map GroundedAST.PFuncLabel Interval)
          | BuildInPredicateObject (GroundedAST.TypedBuildInPred GroundedAST.Object) (Map GroundedAST.PFuncLabel ObjCondition)
          | Deterministic Bool

data RefWithNode cachedInfo = RefWithNode
    { entryRef        :: NodeRef
    , entryNode       :: Node
    , entryLabel      :: Maybe ComposedLabel
    , entryPFuncs     :: Set GroundedAST.PFuncLabel
    , entryCachedInfo :: cachedInfo
    }

type FState cachedInfo = State (Formula cachedInfo)

empty :: CacheComputations cachedInfo -> Formula cachedInfo
empty cacheComps = Formula { nodes              = Map.empty
                           , freshCounter       = 0
                           , labels2ids         = Map.empty
                           , buildinCacheString = Map.empty
                           , buildinCacheReal   = Map.empty
                           , buildinCacheObject = Map.empty
                           , cacheComps         = cacheComps
                           }

insert :: ComposedLabel
       -> Bool
       -> NodeType
       -> [RefWithNode cachedInfo]
       -> FState cachedInfo (RefWithNode cachedInfo)
insert label sign operator children = do
    mbCId <- gets $ Map.lookup label . labels2ids
    case mbCId of
        Just cid -> augmentWithEntryRef $ RefComposed sign cid
        Nothing -> do
            cComps <- gets cacheComps
            if RefDeterministic singleDeterminismValue `elem` childRefs then do
                forM_ childRefs dereference
                return $ deterministicRefWithNode singleDeterminismValue $ cachedInfoDeterministic cComps singleDeterminismValue
            else do
                children' <- List.concat <$> mapM simplifyChild children
                case children' of
                    [] -> return $ deterministicRefWithNode filterValue $ cachedInfoDeterministic cComps filterValue
                    [onlyChild] -> return onlyChild
                    _ -> do
                        let pFuncs     = foldl' (\pfuncs child -> Set.union pfuncs $ entryPFuncs child) Set.empty children'
                        let cachedInfo = cachedInfoComposed cComps operator (Set.size pFuncs) (entryCachedInfo <$> children')
                        let childRefs' = entryRef <$> children'
                        cid <- state (\f@Formula{freshCounter} ->
                                ( freshCounter,
                                  f{ nodes        = Map.insert
                                                     (ComposedId freshCounter)
                                                     (1, FormulaEntry label operator childRefs' pFuncs cachedInfo)
                                                     (nodes f)
                                   , freshCounter = succ freshCounter
                                   , labels2ids   = Map.insert label (ComposedId freshCounter) $ labels2ids f
                                   }
                                )
                            )
                        return RefWithNode { entryRef        = RefComposed sign $ ComposedId cid
                                           , entryNode       = Composed operator childRefs'
                                           , entryLabel      = Just label
                                           , entryPFuncs     = pFuncs
                                           , entryCachedInfo = cachedInfo
                                           }
        where
            -- truth value that causes determinism if at least a single child has it
            singleDeterminismValue = operator == Or
            -- truth value that can be filtered out
            filterValue = operator == And
            childRefs = entryRef <$> children

            simplifyChild :: RefWithNode cachedInfo -> FState cachedInfo [RefWithNode cachedInfo]
            simplifyChild c = case entryNode c of
                Composed cop cs | cop == operator -> do
                    augCs <- forM cs augmentWithEntryRef
                    dereference $ entryRef c
                    return augCs
                Deterministic v | v == filterValue -> return []
                _ -> return [c]

augmentWithEntry :: NodeRef -> FState cachedInfo (RefWithNode cachedInfo)
augmentWithEntry ref = augmentWithEntryBase ref False

augmentWithEntryRef :: NodeRef -> FState cachedInfo (RefWithNode cachedInfo)
augmentWithEntryRef ref = augmentWithEntryBase ref True

augmentWithEntryBase :: NodeRef -> Bool -> FState cachedInfo (RefWithNode cachedInfo)
augmentWithEntryBase ref@(RefComposed _ i) incRefCount = do
    fNodes <- gets nodes
    (_, FormulaEntry label nType nChildren pFuncs cachedInfo) <- if incRefCount then do
        let (Just entry, fNodes') = Map.insertLookupWithKey (\_ _ (rCount, ent) -> (succ rCount, ent)) i undefined fNodes
        modify' (\st -> st{nodes = fNodes'})
        return entry
    else
        return $ Map.findWithDefault undefined i fNodes
    return RefWithNode
        { entryRef        = ref
        , entryNode       = Composed nType nChildren
        , entryLabel      = Just label
        , entryPFuncs     = pFuncs
        , entryCachedInfo = cachedInfo
        }
augmentWithEntryBase (RefBuildInPredicateBool prd) _ = do
    Formula{cacheComps} <- get
    return $ predRefWithNodeBool prd $ cachedInfoBuildInPredBool cacheComps prd
augmentWithEntryBase (RefBuildInPredicateString prd sConds) _ = state (\f@Formula{buildinCacheString, cacheComps} ->
        let (cachedInfo, buildinCache') = cachedInfoBuildInPredCached sConds prd (cachedInfoBuildInPredString cacheComps) buildinCacheString
        in  (predRefWithNodeString prd sConds cachedInfo, f {buildinCacheString = buildinCache'})
    )
augmentWithEntryBase (RefBuildInPredicateReal prd rConds) _ = state (\f@Formula{buildinCacheReal, cacheComps} ->
        let (cachedInfo, buildinCache') = cachedInfoBuildInPredCached rConds prd (cachedInfoBuildInPredReal cacheComps) buildinCacheReal
        in  (predRefWithNodeReal prd rConds cachedInfo, f {buildinCacheReal = buildinCache'})
    )
augmentWithEntryBase (RefBuildInPredicateObject prd oConds) _ = state (\f@Formula{buildinCacheObject, cacheComps} ->
        let (cachedInfo, buildinCache') = cachedInfoBuildInPredCached oConds prd (cachedInfoBuildInPredObject cacheComps) buildinCacheObject
        in  (predRefWithNodeObject prd oConds cachedInfo, f {buildinCacheObject = buildinCache'})
    )
augmentWithEntryBase (RefDeterministic val) _ = do
    Formula{cacheComps} <- get
    return $ deterministicRefWithNode val $ cachedInfoDeterministic cacheComps val

predRefWithNodeBool :: GroundedAST.TypedBuildInPred Bool
                    -> cachedInfo
                    -> RefWithNode cachedInfo
predRefWithNodeBool prd =
    predRefWithNode prd (RefBuildInPredicateBool prd) (BuildInPredicateBool prd)

predRefWithNodeString :: GroundedAST.TypedBuildInPred Text
                      -> Map GroundedAST.PFuncLabel (Set Text)
                      -> cachedInfo
                      -> RefWithNode cachedInfo
predRefWithNodeString prd sConds =
    predRefWithNode prd (RefBuildInPredicateString prd sConds) (BuildInPredicateString prd sConds)

predRefWithNodeReal :: GroundedAST.TypedBuildInPred GroundedAST.RealN
                    -> Map GroundedAST.PFuncLabel Interval
                    -> cachedInfo
                    -> RefWithNode cachedInfo
predRefWithNodeReal prd rConds =
    predRefWithNode prd (RefBuildInPredicateReal prd rConds) (BuildInPredicateReal prd rConds)

predRefWithNodeObject :: GroundedAST.TypedBuildInPred GroundedAST.Object
                      -> Map GroundedAST.PFuncLabel ObjCondition
                      -> cachedInfo
                      -> RefWithNode cachedInfo
predRefWithNodeObject prd oConds =
    predRefWithNode prd (RefBuildInPredicateObject prd oConds) (BuildInPredicateObject prd oConds)

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
    RefBuildInPredicateBool _           -> Conditions Map.empty Map.empty Map.empty Map.empty
    RefBuildInPredicateString _ choices -> Conditions Map.empty choices   Map.empty Map.empty
    RefBuildInPredicateReal _ choices   -> Conditions Map.empty Map.empty choices   Map.empty
    RefBuildInPredicateObject _ choices -> Conditions Map.empty Map.empty Map.empty choices
    _ -> case entryLabel entry of
        Just (ComposedLabel _ conds _) -> conds
        _ -> noConditions

condition :: RefWithNode cachedInfo
          -> Conditions
          -> FState cachedInfo (RefWithNode cachedInfo)
condition rootNodeEntry Conditions{boolConds, stringConds, realConds, objConds} = condition' rootNodeEntry
    where
    condition' origNodeEntry
        | Set.null $ Set.intersection allCondPFuncs pFuncs = do
            reference $ entryRef origNodeEntry
            return origNodeEntry
        | otherwise = case entryRef origNodeEntry of
            RefComposed sign _ -> do
                labels2ids <- gets labels2ids
                case Map.lookup newLabel labels2ids of
                    Just nodeId -> augmentWithEntryRef $ RefComposed sign nodeId
                    _ -> do
                        condChildren <- forM
                            children
                            (\child -> do
                                condRef <- augmentWithEntry child
                                condition' condRef
                            )
                        insert newLabel sign op condChildren
                where
                Composed op children = entryNode origNodeEntry
                newLabel = updLabel condComposedLabelBool   boolConds   $
                           updLabel condComposedLabelString stringConds $
                           updLabel condComposedLabelReal   realConds   $
                           updLabel condComposedLabelObject objConds    $
                           fromJust $ entryLabel origNodeEntry

                updLabel :: (GroundedAST.PFuncLabel -> a -> ComposedLabel -> ComposedLabel)
                         -> Map GroundedAST.PFuncLabel a
                         -> ComposedLabel
                         -> ComposedLabel
                updLabel lblCondFunc conds label = Map.foldWithKey
                    (\pf cond lbl -> if Set.member pf pFuncs then lblCondFunc pf cond lbl else lbl)
                    label
                    conds
            RefBuildInPredicateBool (GroundedAST.Equality eq exprL exprR) -> do
                let condPred = GroundedAST.Equality eq (conditionExpr exprL) (conditionExpr exprR)
                cacheComps <- gets cacheComps
                return $ case GroundedAST.deterministicValueTyped condPred of
                    Just val' -> deterministicRefWithNode val' $ cachedInfoDeterministic cacheComps val'
                    Nothing   -> predRefWithNodeBool condPred $ cachedInfoBuildInPredBool cacheComps condPred
                where
                conditionExpr :: GroundedAST.Expr Bool -> GroundedAST.Expr Bool
                conditionExpr expr@(GroundedAST.PFuncExpr exprPFunc) =
                    case Map.lookup (GroundedAST.probabilisticFuncLabel exprPFunc) boolConds of
                        Just val -> GroundedAST.ConstantExpr $ GroundedAST.BoolConstant val
                        Nothing  -> expr
                conditionExpr expr = expr
            RefBuildInPredicateString prd@(GroundedAST.Equality eq exprL exprR) sConds -> do
                Formula{cacheComps, buildinCacheString} <- get
                case GroundedAST.deterministicValueTyped condPred of
                    Just val' -> return $ deterministicRefWithNode val' $ cachedInfoDeterministic cacheComps val'
                    Nothing -> do
                        let (cachedInfo, buildinCache') = cachedInfoBuildInPredCached sConds' condPred (cachedInfoBuildInPredString cacheComps) buildinCacheString
                        modify' (\f -> f {buildinCacheString = buildinCache'})
                        return $ predRefWithNodeString condPred sConds' cachedInfo
                where
                sConds' = Set.fold
                    (\pf conds -> case Map.lookup pf stringConds of
                        Just cond -> Map.insert pf cond conds
                        Nothing   -> conds
                    )
                    sConds
                    pFuncs

                condPred :: GroundedAST.TypedBuildInPred Text
                condPred
                    | Set.size possibleLeft == 1 && Set.size possibleRight == 1 =
                        GroundedAST.Constant $ eq == (getFirst possibleLeft == getFirst possibleRight)
                    | Set.null $ Set.intersection possibleLeft possibleRight = GroundedAST.Constant $ not eq
                    | otherwise = prd
                    where
                    possibleLeft  = GroundedAST.possibleValuesStr exprL sConds'
                    possibleRight = GroundedAST.possibleValuesStr exprR sConds'
            RefBuildInPredicateReal prd@(GroundedAST.Ineq op left right) rConds -> do
                Formula{cacheComps, buildinCacheReal} <- get
                case GroundedAST.deterministicValueTyped condPred of
                    Just val' -> return $ deterministicRefWithNode val' $ cachedInfoDeterministic cacheComps val'
                    Nothing -> do
                        let (cachedInfo, buildinCache') = cachedInfoBuildInPredCached rConds' condPred (cachedInfoBuildInPredReal cacheComps) buildinCacheReal
                        modify' (\f -> f {buildinCacheReal=buildinCache'})
                        return $ predRefWithNodeReal condPred rConds' cachedInfo
                where
                rConds'  = Set.fold
                    (\pf conds -> case Map.lookup pf realConds of
                        Just cond -> Map.insert pf cond conds
                        Nothing   -> conds
                    )
                    rConds
                    pFuncs

                condPred :: GroundedAST.TypedBuildInPred GroundedAST.RealN
                condPred
                    -- check if choice is made for all 'pFuncs' in 'prd'
                    | length conditions == Set.size pFuncs = conditionPred'
                    | otherwise = prd
                    where
                    conditionPred'
                        | all ((==) $ Just True)  checkedPreds = GroundedAST.Constant True
                        | all ((==) $ Just False) checkedPreds = GroundedAST.Constant False
                        | otherwise                            = prd

                    checkedPreds = map (GroundedAST.checkRealIneqPred op left right) crns
                    conditions   = [(pf',interv') | (pf',interv') <- Map.toList rConds', Set.member pf' pFuncs]
                    crns         = Interval.corners conditions
            RefBuildInPredicateObject prd@(GroundedAST.Equality eq exprL exprR) oConds -> do
                Formula{cacheComps, buildinCacheObject} <- get
                case GroundedAST.deterministicValueTyped condPred of
                    Just val' -> return $ deterministicRefWithNode val' $ cachedInfoDeterministic cacheComps val'
                    Nothing -> do
                        let (cachedInfo, buildinCache') = cachedInfoBuildInPredCached oConds' condPred (cachedInfoBuildInPredObject cacheComps) buildinCacheObject
                        modify' (\f -> f {buildinCacheObject = buildinCache'})
                        return $ predRefWithNodeObject condPred oConds' cachedInfo
                where
                oConds' = Set.fold
                    (\pf conds -> case Map.lookup pf objConds of
                        Just cond -> Map.insert pf cond conds
                        Nothing   -> conds
                    )
                    oConds
                    pFuncs

                condPred :: GroundedAST.TypedBuildInPred GroundedAST.Object
                condPred
                    | lFrom == lUpto && rFrom == rUpto = GroundedAST.Constant $ (lFrom == rFrom) == eq
                    | otherwise = case intervIntersection lFrom lUpto rFrom rUpto of
                        Nothing -> GroundedAST.Constant $ not eq -- disjoint intervals
                        Just (from, upto)
                            -- optimisation: no need to go through all values in case of no excluded values
                            | Set.null lExcl && Set.null rExcl -> prd
                            -- all possible values excluded
                            | all (\o -> Set.member o lExcl || Set.member o rExcl) [from..upto] ->
                                GroundedAST.Constant $ not eq
                            | otherwise -> prd
                    where
                    (lFrom, lUpto, lExcl) = possibleObjects exprL
                    (rFrom, rUpto, rExcl) = possibleObjects exprR

                    intervIntersection lFrom' lUpto' rFrom' rUpto'
                        | from <= upto = Just (from, upto)
                        | otherwise    = Nothing
                        where
                        from = max lFrom' rFrom'
                        upto = min lUpto' rUpto'

                possibleObjects :: GroundedAST.Expr GroundedAST.Object -> (Integer, Integer, Set Integer)
                possibleObjects (GroundedAST.ConstantExpr (GroundedAST.ObjConstant cnst)) = (cnst, cnst, Set.empty)
                possibleObjects (GroundedAST.PFuncExpr pf') = case Map.lookup (GroundedAST.probabilisticFuncLabel pf') oConds' of
                    Nothing                                   -> (0, GroundedAST.objectPfNrObjects pf' - 1, Set.empty)
                    Just (Object o)                           -> (o , o, Set.empty)
                    Just (AnyExcept excl)                     -> (0, GroundedAST.objectPfNrObjects pf' - 1, excl)
                    Just (InInterval from upto)               -> (from, upto, Set.empty)
                    Just (AnyExceptInInterval excl from upto) -> (from, upto, excl)
                possibleObjects _ = undefined
            _ -> undefined
        where
        pFuncs = entryPFuncs origNodeEntry

    allCondPFuncs = Set.unions [ Set.fromList $ Map.keys boolConds
                               , Set.fromList $ Map.keys stringConds
                               , Set.fromList $ Map.keys realConds
                               , Set.fromList $ Map.keys objConds
                               ]

reference :: NodeRef -> FState cachedInfo ()
reference (RefComposed _ cid) = modify'
    (\st -> st{nodes = Map.adjust (first succ) cid $ nodes st})
reference _ = return ()

dereference :: NodeRef -> FState cachedInfo ()
dereference (RefComposed _ cid) = do
        (delete, children) <- state (\f ->
                let Just (refCount, FormulaEntry label _ children _ _) = Map.lookup cid (nodes f)
                    doDelete = refCount == 1
                    f' = if doDelete
                         then f{nodes = Map.delete cid $ nodes f, labels2ids = Map.delete label $ labels2ids f}
                         else f{nodes = Map.adjust (\(rc, entry) -> (rc - 1, entry)) cid $ nodes f}
                in ((doDelete, children), f')
            )
        when delete $ forM_ children dereference
dereference _ = return ()

negate :: NodeRef -> NodeRef
negate (RefComposed sign refId)               = RefComposed (not sign) refId
negate (RefBuildInPredicateBool   prd)        = RefBuildInPredicateBool   (GroundedAST.negatePred prd)
negate (RefBuildInPredicateString prd sConds) = RefBuildInPredicateString (GroundedAST.negatePred prd) sConds
negate (RefBuildInPredicateReal   prd rConds) = RefBuildInPredicateReal   (GroundedAST.negatePred prd) rConds
negate (RefBuildInPredicateObject prd oConds) = RefBuildInPredicateObject (GroundedAST.negatePred prd) oConds
negate (RefDeterministic val)                 = RefDeterministic $ not val

exportAsDot :: FilePath
            -> Formula cachedInfo
            -> Map Int Text
            -> Map Int (Int, [AST.ConstantExpr])
            -> Map Int PredicateLabel
            -> ExceptionalT IOException IO ()
exportAsDot path Formula{nodes} ids2str ids2label ids2predlbl = do
    file <- doIO (openFile path WriteMode)
    doIO (hPutStrLn file "digraph Formula {")
    forM_ (Map.toList nodes) (printNode file)
    doIO (hPutStrLn file "}")
    doIO (hClose file)
    where
        printNode :: Handle -> (ComposedId, (Int, FormulaEntry cachedInfo)) -> ExceptionalT IOException IO ()
        printNode file (ComposedId i, (refCount, FormulaEntry label op children _ _)) = do
            doIO ( LTIO.hPutStrLn file $ TB.toLazyText $
                       showb i <>
                       "[label=\"" <>
                       showb i <>
                       ": " <>
                       TB.fromLazyText (LT.replace "\"" "\\\"" $ TB.toLazyText $ composedLabelToText label ids2str ids2label ids2predlbl) <>
                       "\\n" <>
                       descr <>
                       "\"];"
                 )
            void $ forM_ children writeEdge
            where
                descr = (case op of And -> "AND "; Or -> "OR ") <> showb refCount
                writeEdge childRef = doIO $ LTIO.hPutStrLn file $ TB.toLazyText $ showb i <> "->" <> childStr childRef <> ";"

                childStr :: NodeRef -> Builder
                childStr (RefComposed sign (ComposedId childId)) = showb childId <> "[label=\"" <> showb sign <> "\"]"
                childStr (RefBuildInPredicateBool prd)           = printPrd prd
                childStr (RefBuildInPredicateString prd _)       = printPrd prd
                childStr (RefBuildInPredicateReal prd _)         = printPrd prd
                childStr (RefBuildInPredicateObject prd _)       = printPrd prd
                childStr (RefDeterministic v)                    = showb v

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
    { nodes              :: Map ComposedId (Int, FormulaEntry cachedInfo)                                                             -- graph representing formulas
    , freshCounter       :: Int                                                                                                       -- counter for fresh nodes
    , labels2ids         :: Map ComposedLabel ComposedId                                                                              -- map from composed label to composed ids (ids are used for performance, as ints are most effecient as keys in the graph map)
    , buildinCacheString :: Map (GroundedAST.TypedBuildInPred Text,               Map GroundedAST.PFuncLabel (Set Text))   cachedInfo -- cache for buildin predicates
    , buildinCacheReal   :: Map (GroundedAST.TypedBuildInPred GroundedAST.RealN,  Map GroundedAST.PFuncLabel Interval)     cachedInfo -- cache for buildin predicates
    , buildinCacheObject :: Map (GroundedAST.TypedBuildInPred GroundedAST.Object, Map GroundedAST.PFuncLabel ObjCondition) cachedInfo -- cache for buildin predicates
    , cacheComps         :: CacheComputations cachedInfo                                                                              -- how cached information attached to formulas is computed
    }

newtype ComposedId = ComposedId Int deriving (Ord, Eq)

instance Hashable ComposedId where
    hashWithSalt salt (ComposedId cid) = salt + cid

data ComposedLabel = ComposedLabel
    PredicateId -- id
    Conditions  -- conditions
    Int         -- stored hash to avoid recomputation
    deriving (Eq, Ord)

instance Hashable ComposedLabel where
    hashWithSalt salt (ComposedLabel _ _ hash) = salt + hash

data PredicateLabel = PredicateLabel GroundedAST.PredicateLabel (Set GroundedAST.PredicateLabel) (Maybe Int) deriving (Eq, Ord, Generic)
instance Hashable PredicateLabel

newtype PredicateId = PredicateId Int deriving (Eq, Ord, Generic)
instance Hashable PredicateId

-- conditioned formulas
data Conditions = Conditions { boolConds   :: Map GroundedAST.PFuncLabel Bool
                             , stringConds :: Map GroundedAST.PFuncLabel (Set Text)
                             , realConds   :: Map GroundedAST.PFuncLabel Interval
                             , objConds    :: Map GroundedAST.PFuncLabel ObjCondition
                             }
                             deriving (Eq, Ord, Generic)
instance Hashable Conditions

data ObjCondition = Object Integer
                  | AnyExcept (Set Integer)
                  | InInterval Integer Integer -- interval including end points
                  | AnyExceptInInterval (Set Integer) Integer Integer
                  deriving (Eq, Ord, Generic, Show)
instance Hashable ObjCondition

noConditions :: Conditions
noConditions = Conditions Map.empty Map.empty Map.empty Map.empty

composedLabelToText :: ComposedLabel -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Map Int PredicateLabel -> Builder
composedLabelToText (ComposedLabel (PredicateId cid) Conditions{boolConds, stringConds, realConds} _) ids2str ids2label ids2predlbl =
    GroundedAST.predicateLabelToText label ids2str ids2label <>
    "-" <>
    toTextLst (Set.toList excluded) (\x -> GroundedAST.predicateLabelToText x ids2str ids2label) <>
    (case mbNr of Just nr -> "#" <> showb nr; Nothing -> "") <>
    "|" <>
    showbLst (
        (showCondBool                               <$> Map.toList boolConds)   ++
        ((\x -> showCondString x ids2str ids2label) <$> Map.toList stringConds) ++
        ((\x -> showCondReal   x ids2str ids2label) <$> Map.toList realConds)
    )
    where
        Just (PredicateLabel label excluded mbNr) = Map.lookup cid ids2predlbl
        showCondBool (pf, val) = GroundedAST.pFuncLabelToText pf ids2str ids2label <> "=" <> showb val

-- '-1 is unused predicate label, reserved for evidence
evidenceComposedLabel :: ComposedLabel
evidenceComposedLabel = ComposedLabel (PredicateId (-1)) noConditions 0

uncondComposedLabel :: PredicateId -> ComposedLabel
uncondComposedLabel pid = ComposedLabel pid noConditions 0

condComposedLabelBool :: GroundedAST.PFuncLabel -> Bool -> ComposedLabel -> ComposedLabel
condComposedLabelBool pf val (ComposedLabel label conds hash) = ComposedLabel label conds{boolConds = bConds} hash'
    where
    bConds = Map.insert pf val $ boolConds conds
    hash'  = hash + Hashable.hashWithSalt (Hashable.hash pf) val

condComposedLabelString :: GroundedAST.PFuncLabel -> Set Text -> ComposedLabel -> ComposedLabel
condComposedLabelString pf condSet (ComposedLabel label conds hash) = ComposedLabel label conds{stringConds = sConds} hash''
    where
    sConds  = Map.insert pf condSet $ stringConds conds
    hashPf  = Hashable.hash pf
    hash'   = hash + Hashable.hashWithSalt hashPf condSet
    hash''  = case Map.lookup pf $ stringConds conds of
        Just condSet' -> hash' - Hashable.hashWithSalt hashPf condSet'
        Nothing       -> hash'

condComposedLabelReal :: GroundedAST.PFuncLabel -> Interval -> ComposedLabel -> ComposedLabel
condComposedLabelReal pf interv (ComposedLabel label conds hash) = ComposedLabel label conds{realConds = rConds} hash''
    where
    rConds  = Map.insert pf interv $ realConds conds
    hashPf  = Hashable.hash pf
    hash'   = hash + Hashable.hashWithSalt hashPf interv
    hash''  = case Map.lookup pf $ realConds conds of
        Just interv' -> hash' - Hashable.hashWithSalt hashPf interv'
        Nothing      -> hash'

condComposedLabelObject :: GroundedAST.PFuncLabel -> ObjCondition -> ComposedLabel -> ComposedLabel
condComposedLabelObject pf condSet (ComposedLabel label conds _) = ComposedLabel label conds{objConds = oConds} hash'
    where
    oConds  = Map.insert pf condSet $ objConds conds
    hashPf  = Hashable.hash pf
    hash'   = Hashable.hashWithSalt hashPf oConds

labelId :: ComposedLabel -> FState cachednInfo (Maybe ComposedId)
labelId label = gets labels2ids >>= \l2ids -> return $ Map.lookup label l2ids

-- the FormulaEntry contains composed node, plus additional, redundant, cached information to avoid recomputations
data FormulaEntry cachedInfo = FormulaEntry ComposedLabel NodeType [NodeRef] (Set GroundedAST.PFuncLabel) cachedInfo

data NodeType = And | Or deriving (Eq, Generic)
instance Hashable NodeType

-- node refs are used for optimisation, to avoid looking up leaves (build in preds and deterministic nodes) in the graph
data NodeRef = RefComposed Bool ComposedId
             | RefBuildInPredicateBool   (GroundedAST.TypedBuildInPred Bool) -- don't have to store choices, as rfs are always substituted
             | RefBuildInPredicateString (GroundedAST.TypedBuildInPred Text)               (Map GroundedAST.PFuncLabel (Set Text))
             | RefBuildInPredicateReal   (GroundedAST.TypedBuildInPred GroundedAST.RealN)  (Map GroundedAST.PFuncLabel Interval)
             | RefBuildInPredicateObject (GroundedAST.TypedBuildInPred GroundedAST.Object) (Map GroundedAST.PFuncLabel ObjCondition)
             | RefDeterministic Bool
             deriving (Eq, Ord, Generic)

instance Hashable NodeRef

nodeRefToText :: NodeRef -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder
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
nodeRefToText (RefBuildInPredicateObject prd oConds) ids2str ids2label =
   GroundedAST.typedBuildInPredToText prd ids2str ids2label <>
   "|\n  " <>
   toTextLstEnc "" ",\n" (Map.toList oConds) (\x -> showCondObject x ids2str ids2label)
nodeRefToText (RefDeterministic val) _ _ = showb val

showCondString :: (GroundedAST.PFuncLabel, Set Text) -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder
showCondString (pf, condSet) ids2str ids2label =
    GroundedAST.pFuncLabelToText pf ids2str ids2label <> " in {" <> TB.fromLazyText (LT.replace "\"" "" $ TB.toLazyText $ showbLst $ Set.toList condSet) <> "}"

showCondReal :: (GroundedAST.PFuncLabel, Interval) -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder
showCondReal (pf, Interval.Interval l r) ids2str ids2label =
    GroundedAST.pFuncLabelToText pf ids2str ids2label <> " in (" <> showb l <> "," <> showb r <> ")"

showCondObject :: (GroundedAST.PFuncLabel, ObjCondition) -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder
showCondObject (pf, cond) ids2str ids2label =
    GroundedAST.pFuncLabelToText pf ids2str ids2label <> " " <> condStr
    where
    condStr = case cond of
        Object    s                     -> "in {" <> showb s <> "}"
        AnyExcept s                     -> "not in {" <> showbLst (Set.toList s) <> "}"
        InInterval from upto            -> "in [" <> showb from <> ", " <> showb upto <> "]"
        AnyExceptInInterval s from upto -> "in [" <> showb from <> ", " <> showb upto <> "] \\ {" <> showbLst (Set.toList s) <> "}"

refDeterministic :: Bool -> NodeRef
refDeterministic = RefDeterministic

refBuildInPredicate :: GroundedAST.BuildInPredicate -> NodeRef
refBuildInPredicate prd = case GroundedAST.deterministicValue prd of
    Just val -> RefDeterministic val
    Nothing  -> case prd of
        GroundedAST.BuildInPredicateBool prd' -> RefBuildInPredicateBool   prd'
        GroundedAST.BuildInPredicateReal prd' -> RefBuildInPredicateReal   prd' Map.empty
        GroundedAST.BuildInPredicateStr  prd' -> RefBuildInPredicateString prd' Map.empty
        GroundedAST.BuildInPredicateObj  prd' -> RefBuildInPredicateObject prd' Map.empty
        GroundedAST.BuildInPredicateInt  _    -> undefined

refComposed :: ComposedId -> NodeRef
refComposed = RefComposed True

deterministicNodeRef :: NodeRef -> Maybe Bool
deterministicNodeRef (RefDeterministic val) = Just val
deterministicNodeRef _                      = Nothing

data CacheComputations cachedInfo = CacheComputations
    { cachedInfoComposed          :: NodeType -> Int -> [cachedInfo]                                                            -> cachedInfo
    , cachedInfoBuildInPredBool   ::                                            GroundedAST.TypedBuildInPred Bool               -> cachedInfo
    , cachedInfoBuildInPredString :: Map GroundedAST.PFuncLabel (Set Text)   -> GroundedAST.TypedBuildInPred Text               -> cachedInfo
    , cachedInfoBuildInPredReal   :: Map GroundedAST.PFuncLabel Interval     -> GroundedAST.TypedBuildInPred GroundedAST.RealN  -> cachedInfo
    , cachedInfoBuildInPredObject :: Map GroundedAST.PFuncLabel ObjCondition -> GroundedAST.TypedBuildInPred GroundedAST.Object -> cachedInfo
    , cachedInfoDeterministic     :: Bool                                                                                       -> cachedInfo
    }

-- to avoid recomputation
cachedInfoBuildInPredCached :: (Ord a, Hashable a)
                            => Map GroundedAST.PFuncLabel a
                            -> GroundedAST.TypedBuildInPred b
                            -> (Map GroundedAST.PFuncLabel a -> GroundedAST.TypedBuildInPred b -> cachedInfo)
                            -> Map (GroundedAST.TypedBuildInPred b, Map GroundedAST.PFuncLabel a) cachedInfo
                            -> (cachedInfo, Map (GroundedAST.TypedBuildInPred b, Map GroundedAST.PFuncLabel a) cachedInfo)
cachedInfoBuildInPredCached conds prd infoComp cache = case Map.lookup (prd,conds) cache of
    Just cachedInfo -> (cachedInfo, cache)
    Nothing         -> let cachedInfo = infoComp conds prd
                       in  (cachedInfo, Map.insert (prd,conds) cachedInfo cache)
