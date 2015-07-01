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
    ) where

type Probability       = Rational
type ProbabilityBounds = (Probability, Probability)

type PredicateLabel  = String
type RFuncLabel      = String
