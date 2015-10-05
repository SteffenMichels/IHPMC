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
import Data.Ratio (numerator, denominator)
import Text.Printf (printf)
import Data.Hashable (Hashable)
import qualified Data.Hashable as Hashable
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as Map
import Numeric (fromRat)
import Data.Maybe (isJust)

{-type Probability = Rational

printProb :: Probability -> String
printProb p = printf "%i/%i" n d where
    n = numerator p
    d = denominator p

ratToProb :: Rational -> Probability
ratToProb = id

doubleToProb :: Double -> Probability
doubleToProb = toRational

probToDouble :: Probability -> Double
probToDouble = fromRat-}

type Probability = Double

printProb :: Probability -> String
printProb = show

ratToProb :: Rational -> Probability
ratToProb = fromRat

doubleToProb :: Double -> Probability
doubleToProb = id

probToDouble :: Probability -> Double
probToDouble = id

type ProbabilityBounds = (Probability, Probability)

type PredicateLabel  = String
type RFuncLabel      = String

instance Hashable a => Hashable (HashSet a) where
    hash = Hashable.hashWithSalt 0
    hashWithSalt = Set.foldr (flip Hashable.hashWithSalt)

instance (Hashable a, Hashable b) => Hashable (HashMap a b) where
    hash = Hashable.hashWithSalt 0
    hashWithSalt salt map = foldr (flip Hashable.hashWithSalt) salt $ Map.toList map

getFirst :: HashSet a -> a
getFirst set = head $ Set.toList set

type MultiSet a = HashMap a Int

msInsert :: (Eq a, Hashable a) => a -> MultiSet a -> MultiSet a
msInsert x = Map.insertWith (+) x 1

msDelete :: (Eq a, Hashable a) => a -> MultiSet a -> MultiSet a
msDelete x map
    | n == 1    = Map.delete x map
    | otherwise = Map.insert x (n-1) map
    where
        n = Map.lookupDefault (error "multiset: deleted non-existing element") x  map

msMember :: (Eq a, Hashable a) => a -> MultiSet a -> Bool
msMember x map = isJust $ Map.lookup x map
