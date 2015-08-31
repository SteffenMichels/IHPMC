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
    , predRandomFunctions
    , negatePred
    ) where
import BasicTypes
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Text.Printf (printf)
import Data.List (intercalate)
import Data.Char (toLower)
import Data.Hashable (Hashable)
import qualified Data.Hashable as Hashable
import GHC.Generics (Generic)
import Numeric (fromRat)
import Interval(Interval)
import Control.Applicative ((<$>))

data AST = AST
    { rFuncDefs :: HashMap RFuncLabel [RFuncDef] -- list of func with same signature, first matches
    , rules     :: HashMap PredicateLabel (HashSet RuleBody)
    , queries   :: HashSet PredicateLabel
    , evidence  :: Maybe PredicateLabel
    }

instance Show AST where
    show ast = rfuncDefsStr ++ rulesStr ++ queryStr ++ evStr where
        rfuncDefsStr = concat $ concat [
                            [printf "~%s ~ %s.\n" label $ show def | def <- defs]
                       | (label, defs) <- Map.toList $ rFuncDefs ast]
        rulesStr     = concat $ concat [
                            [printf "%s <- %s.\n" label $ show body | body <- Set.toList bodies]
                       | (label,bodies) <- Map.toList $ rules ast]
        queryStr     = concat [printf "query %s.\n" query | query <- Set.toList $ queries ast]
        evStr = case evidence ast of
            Just ev -> printf "evidence %s.\n" ev
            Nothing -> ""

data RFuncDef = Flip Probability
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

data BuildInPredicate = BoolEq Bool (Expr Bool) (Expr Bool)
                      | RealIneq IneqOp (Expr RealN) (Expr RealN)
                      | RealIn RFuncLabel Interval
                      | Constant Bool
                      deriving (Eq, Generic)

instance Show BuildInPredicate where
    show (BoolEq eq exprX exprY)   = printf "%s %s %s"  (show exprX) (if eq then "=" else "/=") (show exprY)
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
    show (BoolConstant const) = printf "#%s" (toLower <$> show const)
    show (RealConstant const) = printf "%f" (fromRat const::Float)
    show (UserRFunc label)    = printf "~%s" label
instance Hashable (Expr a) where
    hash = Hashable.hashWithSalt 0
    hashWithSalt salt (BoolConstant b) = Hashable.hashWithSalt salt b
    hashWithSalt salt (RealConstant r) = Hashable.hashWithSalt salt r
    hashWithSalt salt (UserRFunc r)    = Hashable.hashWithSalt salt r

negatePred :: BuildInPredicate -> BuildInPredicate
negatePred (BoolEq eq exprX exprY)   = BoolEq (not eq) exprX exprY
negatePred (RealIneq op exprX exprY) = RealIneq (negateOp op) exprX exprY
negatePred (RealIn _ _)              = error "not implemented: negation for real interval inclusion"

negateOp :: IneqOp -> IneqOp
negateOp Lt   = GtEq
negateOp LtEq = Gt
negateOp Gt   = LtEq
negateOp GtEq = Lt

deterministicValue :: BuildInPredicate -> Maybe Bool
deterministicValue (BoolEq eq (BoolConstant left) (BoolConstant right))           = Just $ (if eq then (==) else (/=)) left right
deterministicValue (BoolEq eq (UserRFunc left) (UserRFunc right)) | left == right = Just eq
deterministicValue (Constant val)                                                 = Just val
deterministicValue _                                                              = Nothing

predRandomFunctions :: BuildInPredicate -> HashSet RFuncLabel
predRandomFunctions (BoolEq _ left right)   = Set.union (randomFunctions' left) (randomFunctions' right)
predRandomFunctions (RealIneq _ left right) = Set.union (randomFunctions' left) (randomFunctions' right)
predRandomFunctions (RealIn rf _)           = Set.singleton rf
predRandomFunctions (Constant _)            = Set.empty

randomFunctions' (UserRFunc label) = Set.singleton label
randomFunctions' (BoolConstant _)  = Set.empty
randomFunctions' (RealConstant _)  = Set.empty
