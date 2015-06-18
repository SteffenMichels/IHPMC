-----------------------------------------------------------------------------
--
-- Module      :  AST
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

module AST
    ( AST(..)
    , PredicateLabel
    , RuleBody(..)
    ) where
import Data.Map (Map)
import qualified Data.Map as Map

data AST = AST
    { rFuncDefs :: Map RFuncLabel RFuncDef
    , rules     :: Map PredicateLabel [RuleBody]
    , query     :: PredicateLabel
    } deriving (Show)

type PredicateLabel  = String
type RFuncLabel      = String

data RFuncDef = Flip Rational deriving (Show)

newtype RuleBody = RuleBody [RuleBodyElement] deriving (Show)

data RuleBodyElement = UserPredicate PredicateLabel
                     | BuildInPredicate BuildInPredicate
                     deriving (Show)

data BuildInPredicate = BoolEq (Expr Bool) (Expr Bool)
                      deriving (Show)

data Expr a where
    BoolConstant :: Bool -> Expr Bool
    UserRFunc    :: RFuncLabel -> Expr a -- type depends on user input, has to be typechecked at runtime
deriving instance Show (Expr a)
