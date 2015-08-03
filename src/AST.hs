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
    , RealN
    , IneqOp(..)
    , deterministicValue
    , randomFunctions
    ) where
import BasicTypes
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Text.Printf (printf)
import BasicTypes
import Data.List (intercalate)
import Data.Char (toLower)
import Data.Hashable (Hashable)
import qualified Data.Hashable as Hashable
import GHC.Generics (Generic)
import Numeric (fromRat)
import Interval(Interval)

data AST = AST
    { rFuncDefs :: HashMap RFuncLabel [RFuncDef] -- list of func with same signature, first matches
    , rules     :: HashMap PredicateLabel (HashSet RuleBody)
    , queries   :: HashSet PredicateLabel
    }

instance Show AST where
    show ast = rfuncDefsStr ++ rulesStr ++ queryStr where
        rfuncDefsStr = concat $ concat [
                            [printf "~%s ~ %s.\n" label $ show def | def <- defs]
                       | (label, defs) <- Map.toList $ rFuncDefs ast]
        rulesStr     = concat $ concat [
                            [printf "%s <- %s.\n" label $ show body | body <- Set.toList bodies]
                       | (label,bodies) <- Map.toList $ rules ast]
        queryStr     = concat [printf "query %s.\n" query | query <- Set.toList $ queries ast]

data RFuncDef = Flip Rational
              | RealDist (Rational -> Probability) (Probability -> Rational)

instance Show RFuncDef where
    show (Flip p)       = printf "flip(%s)" $ printProb p
    show (RealDist _ _) = printf "realDist"

newtype RuleBody = RuleBody [RuleBodyElement] deriving (Eq, Generic)

instance Show RuleBody where
    show (RuleBody elements) = intercalate ", " (fmap show elements)
instance Hashable RuleBody

data RuleBodyElement = UserPredicate PredicateLabel
                     | BuildInPredicate BuildInPredicate
                     deriving (Eq, Generic)

instance Show RuleBodyElement where
    show (UserPredicate label)   = label
    show (BuildInPredicate pred) = show pred
instance Hashable RuleBodyElement

data BuildInPredicate = BoolEq (Expr Bool) (Expr Bool)
                      | RealIneq IneqOp (Expr RealN) (Expr RealN)
                      | RealIn RFuncLabel Interval
                      | Constant Bool
                      deriving (Eq, Generic)

instance Show BuildInPredicate where
    show (BoolEq exprX exprY)      = printf "%s = %s"  (show exprX) (show exprY)
    show (RealIneq op exprX exprY) = printf "%s %s %s" (show exprX) (show op) (show exprY)
    show (RealIn rf interv)        = printf "%s in %s" rf (show interv)
instance Hashable BuildInPredicate

data IneqOp = Lt | LtEq | Gt | GtEq deriving (Eq, Generic)
instance Show IneqOp where
    show Lt   = "<"
    show LtEq = "<="
    show Gt   = ">"
    show GtEq = ">="
instance Hashable IneqOp
data RealN = RealN deriving (Eq, Ord)

data Expr a where
    BoolConstant :: Bool -> Expr Bool
    RealConstant :: Rational -> Expr RealN
    UserRFunc    :: RFuncLabel -> Expr a -- type depends on user input, has to be typechecked at runtime

deriving instance Eq (Expr a)
instance Show (Expr a) where
    show (BoolConstant const) = printf "#%s" $ fmap toLower $ show const
    show (RealConstant const) = printf "%f" (fromRat const::Float)
    show (UserRFunc label)    = printf "~%s" label
instance Hashable (Expr a) where
    hash expr = Hashable.hashWithSalt 0 expr
    hashWithSalt salt (BoolConstant b) = Hashable.hashWithSalt salt b
    hashWithSalt salt (RealConstant r) = Hashable.hashWithSalt salt r
    hashWithSalt salt (UserRFunc r)    = Hashable.hashWithSalt salt r

deterministicValue :: BuildInPredicate -> Maybe Bool
deterministicValue (BoolEq (BoolConstant left) (BoolConstant right))           = Just (left == right)
deterministicValue (BoolEq (UserRFunc left) (UserRFunc right)) | left == right = Just True
deterministicValue (Constant val)                                              = Just val
deterministicValue _                                                           = Nothing

randomFunctions :: BuildInPredicate -> HashSet RFuncLabel
randomFunctions (BoolEq left right)     = Set.union (randomFunctions' left) (randomFunctions' right)
randomFunctions (RealIneq _ left right) = Set.union (randomFunctions' left) (randomFunctions' right)
randomFunctions (RealIn rf _)           = Set.singleton rf
randomFunctions (Constant _)            = Set.empty

randomFunctions' (UserRFunc label) = Set.singleton(label)
randomFunctions' (BoolConstant _)  = Set.empty
randomFunctions' (RealConstant _)  = Set.empty
