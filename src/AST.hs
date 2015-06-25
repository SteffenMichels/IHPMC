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
    , RFuncLabel
    , RuleBody(..)
    , RuleBodyElement(..)
    , BuildInPredicate(..)
    , RFuncDef(..)
    , Expr(..)
    ) where
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

data AST = AST
    { rFuncDefs :: Map RFuncLabel [RFuncDef] -- list of func with same signature, first matches
    , rules     :: Map PredicateLabel (Set RuleBody)
    , queries   :: Set PredicateLabel
    }

instance Show AST where
    show ast = rfuncDefsStr ++ rulesStr ++ queryStr where
        rfuncDefsStr = "RANDOM FUNCTION DEFINITIONS\n" ++ foldl (\str (label,def) -> label ++ " ~ " ++ show def ++ "\n") "" (Map.toList $ rFuncDefs ast)
        rulesStr = "RULES\n" ++ foldl (\str (label,body) -> label ++ " <- " ++ show body ++ "\n") "" (Map.toList $ rules ast)
        queryStr = "QUERY\n" ++ show (queries ast)

type PredicateLabel  = String
type RFuncLabel      = String

data RFuncDef = Flip Rational deriving (Show)

newtype RuleBody = RuleBody [RuleBodyElement] deriving (Show, Eq, Ord)

data RuleBodyElement = UserPredicate PredicateLabel
                     | BuildInPredicate BuildInPredicate
                     deriving (Show, Eq, Ord)

data BuildInPredicate = BoolEq (Expr Bool) (Expr Bool)
                      | ConstantPredicate Bool
                      deriving (Eq, Ord)

instance Show BuildInPredicate where
    show (BoolEq exprX exprY) = show exprX ++ " = " ++ show exprY

data Expr a where
    BoolConstant :: Bool -> Expr Bool
    UserRFunc    :: RFuncLabel -> Expr a -- type depends on user input, has to be typechecked at runtime

deriving instance Eq  (Expr a)
deriving instance Ord (Expr a)

instance Show (Expr a) where
    show (BoolConstant const) = "#" ++ show const
    show (UserRFunc label)    = "~" ++ label

