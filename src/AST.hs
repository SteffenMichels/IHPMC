--The MIT License (MIT)
--
--Copyright (c) 2016 Steffen Michels (mail@steffen-michels.de)
--
--Permission is hereby granted, free of charge, to any person obtaining a copy of
--this software and associated documentation files (the "Software"), to deal in
--the Software without restriction, including without limitation the rights to use,
--copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the
--Software, and to permit persons to whom the Software is furnished to do so,
--subject to the following conditions:
--
--The above copyright notice and this permission notice shall be included in all
--copies or substantial portions of the Software.
--
--THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
--IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
--FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
--COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
--IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
--CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

module AST
    ( AST(..)
    , PredicateLabel(..)
    , RFuncLabel(..)
    , RuleBody(..)
    , RuleBodyElement(..)
    , BuildInPredicate(..)
    , Argument(..)
    , RFuncDef(..)
    , Expr(..)
    , ConstantExpr(..)
    , IneqOp(..)
    , VarName(..)
    , predRandomFunctions
    , negateOp
    ) where
import BasicTypes
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Text.Printf (printf)
import Data.List (intercalate)
import Data.Char (toLower)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Numeric (fromRat)

data AST = AST
    { rFuncDefs :: HashMap (RFuncLabel, Int) [([Argument], RFuncDef)] -- first matching def applies
    , rules     :: HashMap (PredicateLabel, Int) (HashSet ([Argument], RuleBody))
    , queries   :: HashSet (PredicateLabel, [Argument])
    , evidence  :: Maybe (PredicateLabel, [Argument])
    }

instance Show AST
    where
    show ast = rfuncDefsStr ++ rulesStr ++ queryStr ++ evStr
        where
        rfuncDefsStr = concat $ concat [
                            [printf "~%s ~ %s.\n" (show label) $ show def | def <- defs]
                       | (label, defs) <- Map.toList $ rFuncDefs ast]
        rulesStr     = concat $ concat [
                            [printf "%s%s <- %s.\n" (show label) (show args) $ show body | (args,body) <- Set.toList bodies]
                       | (label,bodies) <- Map.toList $ rules ast]
        queryStr     = concat [printf "query %s%s.\n" query $ show args | (PredicateLabel query,args) <- Set.toList $ queries ast]
        evStr = case evidence ast of
            Just (PredicateLabel ev,args) -> printf "evidence %s%s.\n" ev $ show args
            Nothing                       -> ""

newtype PredicateLabel = PredicateLabel String deriving (Eq, Show, Generic)
instance Hashable PredicateLabel
newtype RFuncLabel     = RFuncLabel String     deriving (Eq, Show, Generic)
instance Hashable RFuncLabel

data RFuncDef = Flip Probability
              | RealDist (Rational -> Probability) (Probability -> Rational)

instance Show RFuncDef
    where
    show (Flip p)       = printf "flip(%s)" $ printProb p
    show (RealDist _ _) = printf "realDist"

newtype RuleBody = RuleBody [RuleBodyElement] deriving (Eq, Generic)

instance Show RuleBody
    where
    show (RuleBody elements) = intercalate ", " (show <$> elements)
instance Hashable RuleBody

data RuleBodyElement = UserPredicate    PredicateLabel [Argument]
                     | BuildInPredicate BuildInPredicate
                     deriving (Eq, Generic)

instance Show RuleBodyElement where
    show (UserPredicate (PredicateLabel label) args) = show label ++ show args
    show (BuildInPredicate prd)                      = show prd
instance Hashable RuleBodyElement

data Argument = Variable VarName
              | Constant ConstantExpr
              deriving (Eq, Show, Generic)
instance Hashable Argument

data VarName = VarName String
             | TempVar Integer
             deriving (Eq, Generic)
instance Show VarName
    where
    show (VarName str) = str
    show (TempVar i)   = printf "_%i" i
instance Hashable VarName

data BuildInPredicate = Equality Bool Expr Expr
                      | Ineq     IneqOp Expr Expr
                      deriving (Eq, Generic)

instance Show BuildInPredicate
    where
    show (Equality eq exprX exprY) = printf "%s %s %s" (show exprX) (if eq then "=" else "/=") (show exprY)
    show (Ineq     op exprX exprY) = printf "%s %s %s" (show exprX) (show op) (show exprY)
instance Hashable BuildInPredicate

data IneqOp = Lt | LtEq | Gt | GtEq deriving (Eq, Generic)
instance Show IneqOp
    where
    show Lt   = "<"
    show LtEq = "<="
    show Gt   = ">"
    show GtEq = ">="
instance Hashable IneqOp

data Expr = ConstantExpr ConstantExpr
          | RFunc        RFuncLabel [Argument]
          | Var          VarName
          | Sum          Expr Expr
          deriving (Eq, Generic)

instance Show Expr
    where
    show (ConstantExpr cnst)             = show cnst
    show (RFunc (RFuncLabel label) args) = printf "~%s(%s)" label $ intercalate ", " $ show <$> args
    show (Var var)                       = show var
    show (Sum x y)                       = printf "%s + %s" (show x) (show y)
instance Hashable Expr

data ConstantExpr = BoolConstant Bool
                  | RealConstant Rational
                  | StrConstant  String
                  | IntConstant  Integer
                  deriving (Eq, Generic)

instance Show ConstantExpr
    where
    show (BoolConstant cnst) = printf "%s" (toLower <$> show cnst)
    show (RealConstant cnst) = printf "%f" (fromRat cnst::Float)
    show (StrConstant  cnst) = cnst
    show (IntConstant  cnst) = show cnst
instance Hashable ConstantExpr


negateOp :: IneqOp -> IneqOp
negateOp Lt   = GtEq
negateOp LtEq = Gt
negateOp Gt   = LtEq
negateOp GtEq = Lt

predRandomFunctions :: BuildInPredicate -> HashSet (RFuncLabel, [Argument])
predRandomFunctions (Equality _ left right) = Set.union (exprRandomFunctions left) (exprRandomFunctions right)
predRandomFunctions (Ineq     _ left right) = Set.union (exprRandomFunctions left) (exprRandomFunctions right)

exprRandomFunctions :: Expr -> HashSet (RFuncLabel, [Argument])
exprRandomFunctions (RFunc label args) = Set.singleton (label, args)
exprRandomFunctions (Var _)            = Set.empty
exprRandomFunctions (ConstantExpr _)   = Set.empty
exprRandomFunctions (Sum x y)          = Set.union (exprRandomFunctions x) (exprRandomFunctions y)
