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

module Probability
    ( Probability
    , ProbabilityBounds(..)
    , doubleToProb
    , probToDouble
    , intToProb
    , ratToProb
    ) where
import Control.Arrow (first)
import TextShow
#ifndef FLOAT_PROBS
import Numeric (fromRat)
import Data.Ratio (numerator, denominator)
import Data.Monoid ((<>))
#endif

#ifdef FLOAT_PROBS
newtype Probability = Probability Double deriving (Eq, Show)
instance TextShow Probability where
    showb (Probability p) = showb p

ratToProb :: Rational -> Probability
ratToProb = Probability. fromRational

doubleToProb :: Double -> Probability
doubleToProb = Probability

probToDouble :: Probability -> Double
probToDouble (Probability p) = p
#else
newtype Probability = Probability Rational deriving (Eq, Show)
instance TextShow Probability where
    showb (Probability p) = showb (numerator p) <> "/" <> showb (denominator p)

ratToProb :: Rational -> Probability
ratToProb = Probability

doubleToProb :: Double -> Probability
doubleToProb = Probability . toRational

probToDouble :: Probability -> Double
probToDouble (Probability p) = fromRat p
#endif

intToProb :: Integer -> Probability
intToProb i = Probability $ fromIntegral i

instance Read Probability
    where
    readsPrec i = (first Probability <$>)       . readsPrec i
    readList    = (first (Probability <$>) <$>) . readList

instance Ord Probability
    where
    Probability x <= Probability y = x <= y

instance Num Probability
    where
    Probability x + Probability y = Probability (x + y)
    Probability x - Probability y = Probability (x - y)
    Probability x * Probability y = Probability (x * y)
    abs _       = error "BasicTypes: abs not defined for probabilities"
    signum _    = error "BasicTypes: signum not defined for probabilities"
    fromInteger = Probability . fromIntegral

instance Fractional Probability
    where
    Probability x / Probability y = Probability (x / y)
    fromRational = ratToProb

data ProbabilityBounds = ProbabilityBounds Probability Probability deriving Show
