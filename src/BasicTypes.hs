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
    , getFirst
    ) where
import Data.Ratio (numerator, denominator)
import Text.Printf (printf)
import Data.Hashable (Hashable)
import qualified Data.Hashable as Hashable
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as Map

type Probability       = Rational
type ProbabilityBounds = (Probability, Probability)

printProb :: Probability -> String
printProb p = printf "%i/%i" n d where
    n = numerator p
    d = denominator p

type PredicateLabel  = String
type RFuncLabel      = String

instance Hashable a => Hashable (HashSet a) where
    hash set = Hashable.hashWithSalt 0 set
    hashWithSalt salt set = Set.foldr (\el hash -> Hashable.hashWithSalt hash el) salt set

instance (Hashable a, Hashable b) => Hashable (HashMap a b) where
    hash set = Hashable.hashWithSalt 0 set
    hashWithSalt salt map = foldr (\el hash -> Hashable.hashWithSalt hash el) salt $ Map.toList map

getFirst :: (HashSet a) -> a
getFirst set = head $ Set.toList set
