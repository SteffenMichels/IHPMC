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
{-# LANGUAGE Strict #-}
#endif

module Interval
    ( IntervalLimit(..)
    , IntervalLimitPoint(..)
    , Infinitesimal(..)
    , LowerUpper(..)
    , Interval(..)
    , toPoint
    , pointRational
    , corners
    , rat2IntervLimPoint
    , nullInfte
    , (~>), (~>=), (~<), (~<=)
    ) where
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Data.HashMap (Map)
import qualified Data.HashMap as Map
import Numeric (fromRat)
import Data.Foldable (foldl')
import TextShow
import Data.Monoid ((<>))

data IntervalLimit = Inf | Open Rational | Closed Rational deriving (Eq, Generic, Ord)

instance TextShow IntervalLimit where
    showb Inf        = "inf"
    showb (Open r)   = "Open "   <> showb (fromRat r :: Float)
    showb (Closed r) = "Closed " <> showb (fromRat r :: Float)

data LowerUpper = Lower | Upper
data IntervalLimitPoint = PosInf | NegInf | Indet
                        | Point Rational Infinitesimal
                        deriving (Eq)

instance TextShow IntervalLimitPoint where
    showb PosInf          = "+inf"
    showb NegInf          = "-inf"
    showb Indet           = "?"
    showb (Point r infte) = showb (fromRat r :: Float) <> "^" <> showb infte

data Infinitesimal = InfteNull | InftePlus | InfteMinus | InfteIndet deriving Eq
instance TextShow Infinitesimal where
    showb InfteNull  = "0"
    showb InftePlus  = "+"
    showb InfteMinus = "-"
    showb InfteIndet = "?"
instance Hashable IntervalLimit
data Interval = Interval IntervalLimit IntervalLimit deriving (Eq, Generic, Ord)
instance Hashable Interval

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
instance Num IntervalLimitPoint
    where
    x + y = case (x, y) of
        (Point x' ix, Point y' iy) -> Point (x' + y') $ case (ix, iy) of
            (InfteIndet, _         ) -> InfteIndet
            (_,          InfteIndet) -> InfteIndet
            (InfteNull,  iy'       ) -> iy'
            (ix',        InfteNull ) -> ix'
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

    _ * _ = error "undefined: * for IntervalLimitPoint"
    abs _ = error "undefined: abs for IntervalLimitPoint"
    signum _ = error "undefined: signum for IntervalLimitPoint"
    fromInteger i = Point (fromInteger i) InfteNull

    negate Indet           = Indet
    negate PosInf          = NegInf
    negate NegInf          = PosInf
    negate (Point x infte) = Point (-x) $ negInfte infte
        where
        negInfte InfteMinus = InftePlus
        negInfte InftePlus  = InfteMinus
        negInfte infte'     = infte'

instance Ord IntervalLimitPoint
    where
    Indet  <= _      = error "Ord IntervalLimitPoint: undefined for Indet"
    _      <= Indet  = error "Ord IntervalLimitPoint: undefined for Indet"
    NegInf <= _      = True
    _      <= NegInf = False
    _      <= PosInf = True
    PosInf <= _      = False
    Point x infteX <= Point y infteY
        | x == y    = infteX <= infteY
        | otherwise = x <= y

instance Ord Infinitesimal
    where
    InfteIndet <= _          = error "Ord Infinitesimal: undefined for InfteIndet"
    _          <= InfteIndet = error "Ord Infinitesimal: undefined for InfteIndet2"
    InfteMinus <= _          = True
    InfteNull  <= InfteNull  = True
    InfteNull  <= InftePlus  = True
    InftePlus  <= InftePlus  = True
    _          <= _          = False

nullInfte :: IntervalLimitPoint -> IntervalLimitPoint
nullInfte (Point p _) = Point p InfteNull
nullInfte p           = p

data IntervalLimitPointOrd = Lt | Gt | Eq | IndetOrd deriving (Eq, Ord)

compareIntervalPoints :: IntervalLimitPoint -> IntervalLimitPoint -> IntervalLimitPointOrd
compareIntervalPoints x y = case (x,y) of
    (Indet,  _     )    -> IndetOrd
    (_,      Indet )    -> IndetOrd
    (x', y') | x' == y' -> Eq
    (NegInf, _     )    -> Lt
    (PosInf, _     )    -> Gt
    (_,      NegInf)    -> Gt
    (_,      PosInf)    -> Lt
    (Point x' ix, Point y' iy)
        | o /= Eq                  -> o
        | otherwise -> case (ix, iy) of
            (InfteIndet, _         ) -> IndetOrd
            (_,          InfteIndet) -> IndetOrd
            _ | ix == iy             -> Eq
            (InfteMinus, _         ) -> Lt
            (InfteNull,  InftePlus ) -> Lt
            _                        -> Gt
        where
        o = ordRat x' y'
    where
    ordRat x' y' = case compare x' y' of
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

oneArgIndet :: IntervalLimitPoint -> IntervalLimitPoint -> Bool
oneArgIndet Indet _     = True
oneArgIndet _     Indet = True
oneArgIndet _     _     = False

corners :: (Ord k, Hashable k) => [(k, Interval)] -> [Map k IntervalLimitPoint]
corners choices = foldl'
        ( \crnrs (pf, Interval l u) ->
          [Map.insert pf (Interval.toPoint Lower l) c | c <- crnrs] ++ [Map.insert pf (Interval.toPoint Upper u) c | c <- crnrs]
        )
        [Map.fromList [(firstRf, Interval.toPoint Lower firstLower)], Map.fromList [(firstRf, Interval.toPoint Upper firstUpper)]]
        otherConditions
    where
    ((firstRf, Interval firstLower firstUpper):otherConditions) = choices

rat2IntervLimPoint :: Rational -> IntervalLimitPoint
rat2IntervLimPoint r = Point r InfteNull
