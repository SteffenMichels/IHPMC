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
    , pointRational
    , corners
    ) where
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import qualified Data.HashMap.Lazy as Map
import Data.HashSet (HashSet)

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

pointRational :: IntervalLimitPoint -> Maybe Rational
pointRational PosInf         = Nothing
pointRational NegInf         = Nothing
pointRational (Point r)      = Just r
pointRational (PointPlus r)  = Just r
pointRational (PointMinus r) = Just r

subsetEq :: Interval -> Interval -> Bool
subsetEq (lx, ux) (ly, uy) = toPoint Lower lx >= toPoint Lower ly && toPoint Upper ux <= toPoint Upper uy

disjoint :: Interval -> Interval -> Bool
disjoint (lx, ux) (ly, uy) = toPoint Upper ux < toPoint Lower ly || toPoint Upper uy < toPoint Lower lx

--TODO: more concise +? & complete definition
instance Num IntervalLimitPoint where
    x + y = case (pointRational x, pointRational y) of
        (Just px, Just py) -> let sum = px+py in case (x,y) of
            (PointPlus _,  PointMinus _) -> Point      sum
            (PointPlus _,  _)            -> PointPlus  sum
            (PointMinus _, PointPlus _)  -> Point      sum
            (PointMinus _, _)            -> PointMinus sum
            (_,            PointPlus _)  -> PointPlus  sum
            (_,            PointMinus _) -> PointMinus sum
            _                            -> Point      sum
        _ -> case (x,y) of
            (PosInf, NegInf) -> Point 0
            (PosInf, _     ) -> PosInf
            (NegInf, PosInf) -> Point 0
            (NegInf, _     ) -> NegInf
            _                -> y

    x * y = undefined
    abs x = undefined
    signum x = undefined
    fromInteger i = undefined
    negate x = undefined

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

corners :: (Eq k, Hashable k) => [(k, (IntervalLimit, IntervalLimit))] -> [Map.HashMap k IntervalLimitPoint]
corners choices = foldr
            (\(rf, (l,u)) corners -> [Map.insert rf (Interval.toPoint Lower l) c | c <- corners] ++ [Map.insert rf (Interval.toPoint Upper u) c | c <- corners])
            [Map.fromList [(firstRf, Interval.toPoint Lower firstLower)], Map.fromList [(firstRf, Interval.toPoint Upper firstUpper)]] otherConditions
    where
        conditions@((firstRf, (firstLower,firstUpper)):otherConditions) = choices

