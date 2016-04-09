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
    , certainlSubsetEq
    , certainlDisjoint
    , toPoint
    , pointRational
    , corners
    , (~>), (~>=), (~<), (~<=)
    ) where
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import qualified Data.HashMap.Lazy as Map
import Data.HashSet (HashSet)

data IntervalLimit = Inf | Open Rational | Closed Rational deriving (Eq, Generic, Show)
data LowerUpper = Lower | Upper
data IntervalLimitPoint = PosInf | NegInf | Ind
                        | Point Rational | PointPlus Rational | PointMinus Rational deriving (Eq, Show)
instance Hashable IntervalLimit
type Interval = (IntervalLimit, IntervalLimit)

toPoint :: LowerUpper -> IntervalLimit -> IntervalLimitPoint
toPoint _     (Closed p) = Point p
toPoint Lower (Open p)   = PointPlus p
toPoint Upper (Open p)   = PointMinus p
toPoint Lower Inf        = NegInf
toPoint Upper Inf        = PosInf

pointRational :: IntervalLimitPoint -> Maybe Rational
pointRational (Point r)      = Just r
pointRational (PointPlus r)  = Just r
pointRational (PointMinus r) = Just r
pointRational _              = Nothing

certainlSubsetEq :: Interval -> Interval -> Bool
certainlSubsetEq (lx, ux) (ly, uy) = (toPoint Lower lx ~>= toPoint Lower ly) == Just True && (toPoint Upper ux ~<= toPoint Upper uy) == Just True

certainlDisjoint :: Interval -> Interval -> Bool
certainlDisjoint (lx, ux) (ly, uy) = (toPoint Upper ux ~< toPoint Lower ly) == Just True || (toPoint Upper uy ~< toPoint Lower lx) == Just False

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
            (Ind,    _     ) -> Ind
            (_,      Ind   ) -> Ind
            (PosInf, NegInf) -> Ind
            (PosInf, _     ) -> PosInf
            (NegInf, PosInf) -> Ind
            (NegInf, _     ) -> NegInf
            _                -> y+x

    x * y = undefined
    abs x = undefined
    signum x = undefined
    fromInteger = Point . fromInteger
    negate x = undefined

data IntervalLimitPointOrd = Lt | Gt | Eq | IndOrd deriving (Eq, Ord)

compareIntervalPoints :: IntervalLimitPoint -> IntervalLimitPoint -> IntervalLimitPointOrd
compareIntervalPoints x y = case (x,y) of
    (Ind, _)        -> IndOrd
    (_, Ind)        -> IndOrd
    (x, y) | x == y -> Eq
    (NegInf, _)     -> Lt
    (PosInf, _)     -> Gt
    (_, NegInf)     -> Gt
    (_, PosInf)     -> Lt
    (Point x, Point y) -> ordRat x y
    (Point x, PointPlus y)
        | x <= y    -> Lt
        | otherwise -> Gt
    (PointPlus x, PointPlus y) -> ordRat x y
    (PointPlus x, Point y)
        | x < y     -> Lt
        | otherwise -> Gt
    (PointPlus x, PointMinus y)
        | x < y     -> Lt
        | otherwise -> Gt
    (PointMinus x, PointMinus y) -> ordRat x y
    (PointMinus x, Point y)
        | x <= y    -> Lt
        | otherwise -> Gt
    (PointMinus x, PointPlus y)
        | x <= y    -> Lt
        | otherwise -> Gt
    where
        ordRat x y = case compare x y of
            LT -> Lt
            GT -> Gt
            EQ -> Eq

infix 4 ~<
(~<) :: IntervalLimitPoint -> IntervalLimitPoint -> Maybe Bool
x ~< y
    | oneArgIndet x y = Nothing
    | otherwise       = Just $ compareIntervalPoints x y == Lt
infix 4 ~<=
(~<=) :: IntervalLimitPoint -> IntervalLimitPoint -> Maybe Bool
x ~<= y
    | oneArgIndet x y = Nothing
    | otherwise       = let c = compareIntervalPoints x y in Just $ c == Lt || c == Eq
infix 4 ~>
(~>) :: IntervalLimitPoint -> IntervalLimitPoint -> Maybe Bool
x ~> y
    | oneArgIndet x y = Nothing
    | otherwise       = Just $ compareIntervalPoints x y == Gt
infix 4 ~>=
(~>=) :: IntervalLimitPoint -> IntervalLimitPoint -> Maybe Bool
x ~>= y
    | oneArgIndet x y = Nothing
    | otherwise       = let c = compareIntervalPoints x y in Just $ c == Gt || c == Eq

oneArgIndet Ind _ = True
oneArgIndet _ Ind = True
oneArgIndet _ _   = False

corners :: (Eq k, Hashable k) => [(k, (IntervalLimit, IntervalLimit))] -> [Map.HashMap k IntervalLimitPoint]
corners choices = foldr
            (\(rf, (l,u)) corners -> [Map.insert rf (Interval.toPoint Lower l) c | c <- corners] ++ [Map.insert rf (Interval.toPoint Upper u) c | c <- corners])
            [Map.fromList [(firstRf, Interval.toPoint Lower firstLower)], Map.fromList [(firstRf, Interval.toPoint Upper firstUpper)]] otherConditions
    where
        conditions@((firstRf, (firstLower,firstUpper)):otherConditions) = choices

