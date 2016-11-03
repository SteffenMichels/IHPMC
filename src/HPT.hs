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

{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE Strict #-}
#endif

module HPT
    ( HPT(..)
    , HPTLeaf(..)
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
import Data.Maybe (isJust)

-- Hybrid Probability Tree
data HPT = HPT (MaxQueue HPTLeaf) ProbabilityQuadruple
data HPTLeaf = HPTLeaf Formula.NodeRef (Maybe Formula.NodeRef) Probability

instance Eq HPTLeaf where
    HPTLeaf _ _ px == HPTLeaf _ _ py = px == py
instance Ord HPTLeaf where
    HPTLeaf _ _ px <= HPTLeaf _ _ py = px <= py

initialHPT :: Formula.NodeRef -> Formula.NodeRef -> HPT
initialHPT q e = addLeaf q e 1.0 $ HPT PQ.empty $ ProbabilityQuadruple 0.0 0.0 0.0 0.0

nextLeaf :: HPT -> Maybe (HPTLeaf, HPT)
nextLeaf (HPT leaves (ProbabilityQuadruple t f e u)) = case PQ.maxView leaves of
    Nothing                                -> Nothing
    Just (leaf@(HPTLeaf _ mbE p), leaves') -> Just (leaf, HPT leaves' quad)
        where
        quad | isJust mbE = ProbabilityQuadruple t f e (u - p)
             | otherwise  = ProbabilityQuadruple t f (e - p) u

addLeaf :: Formula.NodeRef -> Formula.NodeRef -> Probability -> HPT -> HPT
addLeaf q ev p hpt@(HPT leaves (ProbabilityQuadruple t f e u)) = case Formula.deterministicNodeRef ev of
    Just True  -> addLeafWithinEvidence q p hpt
    Just False -> hpt
    Nothing    -> HPT (PQ.insert (HPTLeaf q (Just ev) p) leaves) (ProbabilityQuadruple t f e (u + p))

addLeafWithinEvidence :: Formula.NodeRef -> Probability -> HPT -> HPT
addLeafWithinEvidence q p (HPT leaves (ProbabilityQuadruple t f e u)) = case Formula.deterministicNodeRef q of
    Just True  -> HPT leaves (ProbabilityQuadruple (t + p) f e u)
    Just False -> HPT leaves (ProbabilityQuadruple t (f + p) e u)
    Nothing    -> HPT (PQ.insert (HPTLeaf q Nothing p) leaves) (ProbabilityQuadruple t f (e + p) u)

-- Nothing if evidence is inconsistent
bounds :: HPT -> Maybe ProbabilityBounds
bounds (HPT _ (ProbabilityQuadruple 0.0 0.0 0.0 0.0)) = Nothing
bounds (HPT _ (ProbabilityQuadruple t f e u)) =
    Just $ ProbabilityBounds lo up
    where
    lo = t / (t + f + e + u)
    up | zu > 0.0 = (t + e + u) / zu
       | otherwise  = 1.0
    zu= t + f + e

-- (true prob, false prob (within evidence), within evidence, unknown prob)
data ProbabilityQuadruple = ProbabilityQuadruple Probability Probability Probability Probability
