-----------------------------------------------------------------------------
--
-- Module      :  PST
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

module PST
    ( PST(..)
    , empty
    , bounds
    ) where
import BasicTypes
import qualified NNF
import qualified AST
import BasicTypes

-- Probabilistic Sematic Tree
data PST = Finished Bool
         | Unfinished NNF.NodeLabel
         | Choice RFuncLabel Probability PST PST

empty :: NNF.NodeLabel -> PST
empty query = Unfinished query

bounds :: PST -> ProbabilityBounds
bounds (Finished b)            = if b then (1.0, 1.0) else (0.0, 0.0)
bounds (Unfinished _)          = (0.0, 1.0)
bounds (Choice _ p left right) = (p*leftLower+(1-p)*rightLower, p*leftUpper+(1-p)*rightUpper) where
    (leftLower,  leftUpper)  = bounds left
    (rightLower, rightUpper) = bounds right
