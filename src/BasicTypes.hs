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

module BasicTypes
    ( Probability
    , ProbabilityBounds
    , PredicateLabel
    , RFuncLabel
    , printProb
    , ratToProb
    , doubleToProb
    , probToDouble
    , getFirst
    ) where
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Numeric (fromRat)
#ifndef FLOAT_PROBS
import Data.Ratio (numerator, denominator)
import Text.Printf (printf)
#endif

#ifdef FLOAT_PROBS
type Probability = Double

printProb :: Probability -> String
printProb = show

ratToProb :: Rational -> Probability
ratToProb = fromRat

doubleToProb :: Double -> Probability
doubleToProb = id

probToDouble :: Probability -> Double
probToDouble = id
#else
type Probability = Rational

printProb :: Probability -> String
printProb p = printf "%i/%i" n d where
    n = numerator p
    d = denominator p

ratToProb :: Rational -> Probability
ratToProb = id

doubleToProb :: Double -> Probability
doubleToProb = toRational

probToDouble :: Probability -> Double
probToDouble = fromRat
#endif

type ProbabilityBounds = (Probability, Probability)

type PredicateLabel  = String
type RFuncLabel      = String

getFirst :: HashSet a -> a
getFirst set = head $ Set.toList set
