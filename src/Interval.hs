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
    , Infinitesimal(..)
    , LowerUpper(..)
    , Interval
    , toPoint
    , pointRational
    , corners
    , rat2IntervLimPoint
    , (~>), (~>=), (~<), (~<=)
    ) where
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import qualified Data.HashMap.Lazy as Map
import Data.HashSet (HashSet)

data IntervalLimit = Inf | Open Rational | Closed Rational deriving (Eq, Generic, Show)
data LowerUpper = Lower | Upper
data IntervalLimitPoint = PosInf | NegInf | Indet
                        | Point Rational Infinitesimal
                        deriving (Eq, Show)

data Infinitesimal = InfteNull | InftePlus | InfteMinus | InfteIndet deriving (Eq, Show)
instance Hashable IntervalLimit
type Interval = (IntervalLimit, IntervalLimit)

toPoint :: LowerUpper -> IntervalLimit -> IntervalLimitPoint
toPoint _     (Closed p) = Point p InfteNull
toPoint Lower (Open p)   = Point p InftePlus
toPoint Upper (Open p)   = Point p InfteMinus
toPoint Lower Inf        = NegInf
toPoint Upper Inf        = PosInf

pointRational :: IntervalLimitPoint -> Maybe Rational
pointRational (Point r _) = Just r
pointRational _           = Nothing

--TODO: complete definition
instance Num IntervalLimitPoint where
    x + y = case (x, y) of
        (Point x ix, Point y iy) -> Point (x+y) $ case (ix, iy) of
            (InfteIndet, _         ) -> InfteIndet
            (_,          InfteIndet) -> InfteIndet
            (InfteNull,  iy        ) -> iy
            (ix,         InfteNull ) -> ix
            _ | ix == iy             -> ix
            _                        -> InfteIndet
        (Indet,  _     )             -> Indet
        (_,      Indet )             -> Indet
        (PosInf, NegInf)             -> Indet
        (NegInf, PosInf)             -> Indet
        (PosInf, _     )             -> PosInf
        (_,      PosInf)             -> PosInf
        (NegInf, _     )             -> NegInf
        (_,      NegInf)             -> NegInf

    x * y = undefined
    abs x = undefined
    signum x = undefined
    fromInteger i = Point (fromInteger i) InfteNull
    negate x = undefined

data IntervalLimitPointOrd = Lt | Gt | Eq | IndetOrd deriving (Eq, Ord)

compareIntervalPoints :: IntervalLimitPoint -> IntervalLimitPoint -> IntervalLimitPointOrd
compareIntervalPoints x y = case (x,y) of
    (Indet,  _     ) -> IndetOrd
    (_,      Indet ) -> IndetOrd
    (x, y) | x == y  -> Eq
    (NegInf, _     ) -> Lt
    (PosInf, _     ) -> Gt
    (_,      NegInf) -> Gt
    (_,      PosInf) -> Lt
    (Point x ix, Point y iy)
        | o /= Eq                  -> o
        | otherwise -> case (ix, iy) of
            (InfteIndet, _         ) -> IndetOrd
            (_,          InfteIndet) -> IndetOrd
            _ | ix == iy             -> Eq
            (InfteMinus, _         ) -> Lt
            (InfteNull,  InftePlus ) -> Lt
            _                        -> Gt
        where o = ordRat x y
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

oneArgIndet Indet _     = True
oneArgIndet _     Indet = True
oneArgIndet _     _     = False

corners :: (Eq k, Hashable k) => [(k, (IntervalLimit, IntervalLimit))] -> [Map.HashMap k IntervalLimitPoint]
corners choices = foldr
            (\(rf, (l,u)) corners -> [Map.insert rf (Interval.toPoint Lower l) c | c <- corners] ++ [Map.insert rf (Interval.toPoint Upper u) c | c <- corners])
            [Map.fromList [(firstRf, Interval.toPoint Lower firstLower)], Map.fromList [(firstRf, Interval.toPoint Upper firstUpper)]] otherConditions
    where
        ((firstRf, (firstLower,firstUpper)):otherConditions) = choices

rat2IntervLimPoint :: Rational -> IntervalLimitPoint
rat2IntervLimPoint r = Point r InfteNull
