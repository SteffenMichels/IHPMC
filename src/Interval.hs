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
    , IntervalLimitPoint(..)
    , LowerUpper(..)
    , Interval
    , subsetEq
    , disjoint
    , toPoint
    ) where
import Data.Hashable (Hashable)
import GHC.Generics (Generic)

data IntervalLimit = Inf | Open Rational | Closed Rational deriving (Eq, Generic, Show)
data LowerUpper = Lower | Upper
data IntervalLimitPoint = PosInf | NegInf | Point Rational | PointPlus Rational | PointMinus Rational deriving (Eq, Show)
instance Hashable IntervalLimit
type Interval = (IntervalLimit, IntervalLimit)

toPoint :: LowerUpper -> IntervalLimit -> IntervalLimitPoint
toPoint _     (Closed p) = Point p
toPoint Lower (Open p)   = PointPlus p
toPoint Upper (Open p)   = PointMinus p
toPoint Lower Inf        = NegInf
toPoint Upper Inf        = PosInf

subsetEq :: Interval -> Interval -> Bool
subsetEq (lx, ux) (ly, uy) = toPoint Lower lx >= toPoint Lower ly && toPoint Upper ux <= toPoint Upper uy

disjoint :: Interval -> Interval -> Bool
disjoint (lx, ux) (ly, uy) = toPoint Upper ux < toPoint Lower ly || toPoint Upper uy < toPoint Lower lx

instance Ord IntervalLimitPoint where
    x `compare` y | x == y = EQ
    NegInf `compare` _      = LT
    PosInf `compare` _      = GT
    _      `compare` NegInf = GT
    _      `compare` PosInf = LT
    (Point x) `compare` (Point y) = x `compare` y
    (Point x) `compare` (PointPlus y)
        | x <= y    = LT
        | otherwise = GT
    (Point x) `compare` (PointMinus y)
        | x < y     = LT
        | otherwise = GT
    (PointPlus x) `compare` (PointPlus y) = x `compare` y
    (PointPlus x) `compare` (Point y)
        | x < y     = LT
        | otherwise = GT
    (PointPlus x) `compare` (PointMinus y)
        | x < y     = LT
        | otherwise = GT
    (PointMinus x) `compare` (PointMinus y) = x `compare` y
    (PointMinus x) `compare` (Point y)
        | x <= y    = LT
        | otherwise = GT
    (PointMinus x) `compare` (PointPlus y)
        | x <= y    = LT
        | otherwise = GT

