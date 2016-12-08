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

module HPT
    ( HPT(..)
    , HPTLeaf(..)
    , HPTLeafFormulas(..)
    , CachedSplitPoints(..)
    , SplitPoint(..)
    , LazyNode
    , initialHPT
    , bounds
    , nextLeaf
    , addLeaf
    , addLeafWithinEvidence
    ) where
import qualified Formula
import Probability
import Data.PQueue.Max (MaxQueue)
import qualified Data.PQueue.Max as PQ
import qualified GroundedAST
import Data.HashMap (Map)
import Data.Text (Text)
import Data.HashSet (Set)
import GHC.Generics (Generic)
import Data.Hashable (Hashable)

-- Hybrid Probability Tree
data HPT = HPT (MaxQueue HPTLeaf) ProbabilityQuadruple
data HPTLeaf = HPTLeaf HPTLeafFormulas Probability
data HPTLeafFormulas = MaybeWithinEv LazyNode Formula.NodeRef
                     | WithinEv      Formula.NodeRef
type LazyNode = Formula.FState CachedSplitPoints (Formula.RefWithNode CachedSplitPoints)
instance Eq HPTLeaf where
    HPTLeaf fx px == HPTLeaf fy py = score fx px == score fy py
instance Ord HPTLeaf where
    HPTLeaf fx px <= HPTLeaf fy py = score fx px <= score fy py

score :: HPTLeafFormulas -> Probability -> Probability
score (MaybeWithinEv _ _) p = p
score (WithinEv _)        p = 2 * p

-- total score, split points + scores
data CachedSplitPoints = CachedSplitPoints Double (Map SplitPoint Double)
data SplitPoint = BoolSplit       (GroundedAST.PFunc Bool)
                | StringSplit     (GroundedAST.PFunc Text)              (Set Text) -- left branch: all string in this set, right branch: all remaining strings
                | ContinuousSplit (GroundedAST.PFunc GroundedAST.RealN) Rational
                deriving (Eq, Generic, Ord)
instance Hashable SplitPoint

initialHPT :: Formula.NodeRef -> Formula.NodeRef -> Formula.FState CachedSplitPoints HPT
initialHPT q e = addLeaf (Formula.augmentWithEntry q) e 1.0 $ HPT PQ.empty $ ProbabilityQuadruple 0.0 0.0 0.0 0.0

nextLeaf :: HPT -> Maybe (HPTLeaf, HPT)
nextLeaf (HPT leaves (ProbabilityQuadruple t f e u)) = case PQ.maxView leaves of
    Nothing                             -> Nothing
    Just (leaf@(HPTLeaf fs p), leaves') -> Just (leaf, HPT leaves' quad)
        where
        quad = case fs of
            MaybeWithinEv _ _ -> ProbabilityQuadruple t f e (u - p)
            WithinEv _        -> ProbabilityQuadruple t f (e - p) u

addLeaf :: LazyNode -> Formula.NodeRef -> Probability -> HPT -> Formula.FState CachedSplitPoints HPT
addLeaf q ev p hpt@(HPT leaves (ProbabilityQuadruple t f e u)) = case Formula.deterministicNodeRef ev of
    Just True -> do
        q' <- Formula.entryRef <$> q
        return $ addLeafWithinEvidence q' p hpt
    Just False -> return hpt
    Nothing    -> return $ HPT (PQ.insert (HPTLeaf (MaybeWithinEv q ev) p) leaves) (ProbabilityQuadruple t f e (u + p))

addLeafWithinEvidence :: Formula.NodeRef -> Probability -> HPT -> HPT
addLeafWithinEvidence q p (HPT leaves (ProbabilityQuadruple t f e u)) = case Formula.deterministicNodeRef q of
    Just True  -> HPT leaves (ProbabilityQuadruple (t + p) f e u)
    Just False -> HPT leaves (ProbabilityQuadruple t (f + p) e u)
    Nothing    -> HPT (PQ.insert (HPTLeaf (WithinEv q) p) leaves) (ProbabilityQuadruple t f (e + p) u)

-- Nothing if evidence is inconsistent
bounds :: HPT -> Maybe ProbabilityBounds
bounds (HPT _ (ProbabilityQuadruple 0.0 0.0 0.0 0.0)) = Nothing
bounds (HPT _ (ProbabilityQuadruple t f e u)) =
    Just $ ProbabilityBounds lo up
    where
    lo = t / (t + f + e + u)
    up | up' < 1.0 = up'
       | otherwise = 1.0
    up' = (t + e + u) / (t + f + e)

-- (true prob, false prob (within evidence), within evidence, unknown prob)
data ProbabilityQuadruple = ProbabilityQuadruple Probability Probability Probability Probability
