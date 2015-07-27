-----------------------------------------------------------------------------
--
-- Module      :  Interval
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

module Interval
    ( IntervalLimit(..)
    , Interval
    , subsetEq
    , disjoint
    ) where
import Data.Hashable (Hashable)
import GHC.Generics (Generic)

data IntervalLimit = Inf | Open Rational | Closed Rational deriving (Eq, Generic, Show)
instance Hashable IntervalLimit
type Interval      = (IntervalLimit, IntervalLimit)

subsetEq :: Interval -> Interval -> Bool
subsetEq (lx, ux) (ly, uy) = gtEqLower lx ly && ltEqUpper ux uy

disjoint :: Interval -> Interval -> Bool
disjoint (lx, ux) (ly, uy) = ltUpperLower ux ly || ltUpperLower uy lx

ltUpperLower :: IntervalLimit -> IntervalLimit -> Bool
ltUpperLower (Open x)   (Open y)   = x <= y
ltUpperLower (Closed x) (Closed y) = x <  y
ltUpperLower (Open x)   (Closed y) = x <= y
ltUpperLower (Closed x) (Open y)   = x <= y
ltUpperLower _ _                   = False

gtEqLower :: IntervalLimit -> IntervalLimit -> Bool
gtEqLower _ Inf                 = True
gtEqLower (Open x)   (Open y)   = x >= y
gtEqLower (Closed x) (Closed y) = x >= y
gtEqLower (Open x)   (Closed y) = x >= y
gtEqLower (Closed x) (Open y)   = x >  y
gtEqLower _ _                   = False

ltEqUpper :: IntervalLimit -> IntervalLimit -> Bool
ltEqUpper _ Inf                 = True
ltEqUpper (Open x)   (Open y)   = x <= y
ltEqUpper (Closed x) (Closed y) = x <= y
ltEqUpper (Open x)   (Closed y) = x <= y
ltEqUpper (Closed x) (Open y)   = x <  y
ltEqUpper _ _                   = False
