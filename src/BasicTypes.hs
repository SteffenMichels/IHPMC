{-# LANGUAGE CPP #-}
-----------------------------------------------------------------------------
--
-- Module      :  BasicTypes
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
