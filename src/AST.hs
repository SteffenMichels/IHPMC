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
    , RuleBody(..)
    , RuleBodyElement(..)
    , BuildInPredicate(..)
    , RFuncDef(..)
    , Expr(..)
    , deterministicValue
    , randomFunctions
    ) where
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Text.Printf (printf)
import BasicTypes

data AST = AST
    { rFuncDefs :: Map RFuncLabel [RFuncDef] -- list of func with same signature, first matches
    , rules     :: Map PredicateLabel (Set RuleBody)
    , queries   :: Set PredicateLabel
    }

instance Show AST where
    show ast = rfuncDefsStr ++ rulesStr ++ queryStr where
        rfuncDefsStr = printf "RANDOM FUNCTION DEFINITIONS\n%s" (foldl (\str (label,def) -> printf "%s ~ %s\n" label $ show def) "" (Map.toList $ rFuncDefs ast))
        rulesStr     = printf "RULES\n%s" (foldl (\str (label,body) -> printf "%s <- %s\n" label $ show body) "" (Map.toList $ rules ast))
        queryStr     = printf "QUERY\n%s" (show $ queries ast)

data RFuncDef = Flip Rational deriving (Show)

newtype RuleBody = RuleBody [RuleBodyElement] deriving (Show, Eq, Ord)

data RuleBodyElement = UserPredicate PredicateLabel
                     | BuildInPredicate BuildInPredicate
                     deriving (Show, Eq, Ord)

data BuildInPredicate = BoolEq (Expr Bool) (Expr Bool)
                      deriving (Eq, Ord)

instance Show BuildInPredicate where
    show (BoolEq exprX exprY) = printf "%s = %s" (show exprX) (show exprY)

data Expr a where
    BoolConstant :: Bool -> Expr Bool
    UserRFunc    :: RFuncLabel -> Expr a -- type depends on user input, has to be typechecked at runtime

deriving instance Eq  (Expr a)
deriving instance Ord (Expr a)

instance Show (Expr a) where
    show (BoolConstant const) = printf "#%s" (show const)
    show (UserRFunc label)    = printf "~%s" label

deterministicValue :: BuildInPredicate -> Maybe Bool
deterministicValue (BoolEq (BoolConstant left) (BoolConstant right))           = Just (left == right)
deterministicValue (BoolEq (UserRFunc left) (UserRFunc right)) | left == right = Just True
deterministicValue _                                                           = Nothing

randomFunctions :: BuildInPredicate -> Set RFuncLabel
randomFunctions (BoolEq left right) = Set.union (randomFunctions' left) (randomFunctions' right)
    where
        randomFunctions' (BoolConstant _)  = Set.empty
        randomFunctions' (UserRFunc label) = Set.singleton(label)
