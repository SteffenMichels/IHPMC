--The MIT License (MIT)
--
--Copyright (c) 2016-2017 Steffen Michels (mail@steffen-michels.de)
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

{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE Strict#-}
#endif

module HPT
    ( HPT(..)
    , HPTLeaf(..)
    , HPTLeafFormulas(..)
    , CachedSplitPoints(..)
    , SplitPoint(..)
    , Proof(..)
    , Choice(..)
    , FNodeType(..)
    , LazyNode
    , initialHPT
    , bounds
    , nextLeaf
    , addLeaf
    , addLeafWithinEvidence
    ) where
import qualified KnowledgeBase as KB
import Probability
import qualified GroundedAST
import Data.HashMap (Map)
import qualified Data.HashMap as Map
import Data.Text (Text)
import GHC.Generics (Generic)
import Data.Hashable (Hashable)
import qualified Data.Hashable as Hashable
import qualified Data.Set as PQ -- set used as PQ here
import Data.HashSet (Set)
import Control.Monad (when)

type PQ = PQ.Set

-- Hybrid Probability Tree
data HPT = HPT (PQ HPTLeaf) ProbabilityQuadruple (Map HPTLeafFormulas Probability)
data HPTLeaf = HPTLeaf HPTLeafFormulas Probability deriving Eq
data HPTLeafFormulas = MaybeWithinEv LazyNode (KB.NodeRef CachedSplitPoints) Int
                     | WithinEv      (KB.NodeRef CachedSplitPoints) Int
                     deriving (Eq, Generic)
instance Ord HPTLeafFormulas where
    compare WithinEv{} MaybeWithinEv{} = LT
    compare (WithinEv qx hx) (WithinEv qy hy) = case compare hx hy of
        EQ  -> compare qx qy
        res -> res
    compare (MaybeWithinEv qx ex hx) (MaybeWithinEv qy ey hy) = case compare hx hy of
        EQ  -> case compare ex ey of
            EQ  -> compare qx qy -- comparing lazy queries is most expensive
            res -> res
        res -> res
    compare MaybeWithinEv{} WithinEv{} = GT

instance Hashable HPTLeafFormulas where
    hashWithSalt salt (MaybeWithinEv _ _ h) = Hashable.hashWithSalt salt h
    hashWithSalt salt (WithinEv _ h)        = Hashable.hashWithSalt salt h

type LazyNode = (KB.NodeRef CachedSplitPoints, KB.Conditions)
instance Ord HPTLeaf where
    HPTLeaf fx px <= HPTLeaf fy py
        | px == py  = fx <= fy
        | otherwise = px <= py

-- CachedSplitPoints "true proofs" "false proofs" "all point [+ scores]"
data CachedSplitPoints = CachedSplitPoints (Set Proof) (Set Proof) FNodeType
data FNodeType = Primitive (Set SplitPoint) | Composed (Map SplitPoint Int)
data SplitPoint = BoolSplit         (GroundedAST.PFunc Bool)
                | StringSplit       (GroundedAST.PFunc Text)               (Set Text) -- left branch: all string in this set, right branch: all remaining strings
                | ContinuousSplit   (GroundedAST.PFunc GroundedAST.RealN)  Rational
                | ObjectSplit       (GroundedAST.PFunc GroundedAST.Object) Integer    -- left branch: including this object, right branch: excluding this object
                | ObjectIntervSplit (GroundedAST.PFunc GroundedAST.Object) Integer    -- left branch: including this object
                deriving (Eq, Generic, Ord)
instance Hashable SplitPoint

newtype Proof = Proof (Map SplitPoint Choice) deriving (Eq, Ord, Generic)
instance Hashable Proof
data Choice = Left | Right deriving (Eq, Ord, Generic)
instance Hashable Choice

initialHPT :: KB.NodeRef CachedSplitPoints -> KB.NodeRef CachedSplitPoints -> KB.KBState CachedSplitPoints HPT
initialHPT q e = addLeaf (q, KB.noConditions) e 1.0 $ HPT PQ.empty (ProbabilityQuadruple 0.0 0.0 0.0 0.0) Map.empty

nextLeaf :: HPT -> Maybe (HPTLeaf, HPT)
nextLeaf (HPT leaves (ProbabilityQuadruple t f e u) leafSet) = case PQ.maxView leaves of
    Nothing                             -> Nothing
    Just (leaf@(HPTLeaf fs p), leaves') -> Just (leaf, HPT leaves' quad $ Map.delete fs leafSet)
        where
        quad = case fs of
            MaybeWithinEv{} -> ProbabilityQuadruple t f e (u - p)
            WithinEv{}      -> ProbabilityQuadruple t f (e - p) u

addLeaf :: LazyNode -> KB.NodeRef CachedSplitPoints -> Probability -> HPT -> KB.KBState CachedSplitPoints HPT
addLeaf qWithConds@(q, qConds) ev p hpt@(HPT leaves (ProbabilityQuadruple t f e u) leafSet) = case KB.deterministicNodeRef ev of
    Just True -> do
        q'  <- KB.augmentWithEntry q
        q'' <- KB.condition q' qConds
        KB.dereference q
        addLeafWithinEvidence (KB.entryRef q'') p hpt
    Just False -> return hpt
    Nothing    -> do
        when merged $ KB.dereference q >> KB.dereference ev
        return $ HPT pq' (ProbabilityQuadruple t f e (u + p)) leafSet'
        where
        (pq', leafSet', merged) = insertIntoPQ
            (MaybeWithinEv qWithConds ev $ Hashable.hashWithSalt (Hashable.hash qWithConds) ev)
            p
            leaves
            leafSet

addLeafWithinEvidence :: KB.NodeRef CachedSplitPoints -> Probability -> HPT -> KB.KBState CachedSplitPoints HPT
addLeafWithinEvidence q p (HPT leaves (ProbabilityQuadruple t f e u) leafSet) = case KB.deterministicNodeRef q of
    Just True  -> return $ HPT leaves (ProbabilityQuadruple (t + p) f e u) leafSet
    Just False -> return $ HPT leaves (ProbabilityQuadruple t (f + p) e u) leafSet
    Nothing    -> do
        when merged $ KB.dereference q
        return $ HPT pq' (ProbabilityQuadruple t f (e + p) u) leafSet'
        where
        (pq', leafSet', merged) = insertIntoPQ (WithinEv q $ Hashable.hash q) p leaves leafSet


insertIntoPQ :: HPTLeafFormulas
             -> Probability
             -> PQ HPTLeaf
             -> Map HPTLeafFormulas Probability
             -> (PQ HPTLeaf, Map HPTLeafFormulas Probability, Bool)
insertIntoPQ fs p pq leafSet = case Map.lookup fs leafSet of
    Just p' ->
        let p'' = p + p'
        in  (PQ.insert (HPTLeaf fs p'') $ PQ.delete (HPTLeaf fs p') pq, Map.insert fs p'' leafSet, True)
    Nothing -> (PQ.insert (HPTLeaf fs p) pq, Map.insert fs p leafSet, False)

-- Nothing if evidence is inconsistent
bounds :: HPT -> Maybe ProbabilityBounds
bounds (HPT _ (ProbabilityQuadruple 0.0 0.0 0.0 0.0) _) = Nothing
bounds (HPT _ (ProbabilityQuadruple t f e u) _) =
    Just $ ProbabilityBounds lo up
    where
    lo = t / (t + f + e + u)
    up | upDen == 0.0 = 1.0
       | up' <= 1.0   = up'
       | otherwise    = 1.0
    ~up'  = (t + e + u) / upDen -- lazy to prevent division by zero
    upDen = t + f + e

-- (true prob, false prob (within evidence), within evidence, unknown prob)
data ProbabilityQuadruple = ProbabilityQuadruple Probability Probability Probability Probability
