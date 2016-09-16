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

{-# LANGUAGE Strict #-}

module AST
    ( AST(..)
    , PredicateLabel(..)
    , RFuncLabel(..)
    , RuleBody(..)
    , RuleBodyElement(..)
    , BuildInPredicate(..)
    , HeadArgument(..)
    , RFuncDef(..)
    , Expr(..)
    , ConstantExpr(..)
    , IneqOp(..)
    , VarName(..)
    , predRandomFunctions
    , exprRandomFunctions
    , negateOp
    ) where
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Text.Printf (printf)
import Data.Char (toLower)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Numeric (fromRat)
import Probability
import Util

data AST = AST
    { rFuncDefs :: HashMap (RFuncLabel, Int)     [([HeadArgument], RFuncDef)] -- first matching def applies
    , rules     :: HashMap (PredicateLabel, Int) [([HeadArgument], RuleBody)]
    , queries   :: [RuleBodyElement]
    , evidence  :: [RuleBodyElement]
    }

instance Show AST
    where
    show ast = rfuncDefsStr ++ rulesStr ++ queryStr ++ evStr
        where
        rfuncDefsStr = concat $ concat [
                            [printf "~%s ~ %s.\n" (show label) $ show def | def <- defs]
                       | (label, defs) <- Map.toList $ rFuncDefs ast]
        rulesStr     = concat $ concat [
                            [printf "%s%s <- %s.\n" (show label) (show args) $ show body | (args, body) <- bodies]
                       | (label,bodies) <- Map.toList $ rules ast]
        queryStr     = concat [printf "query %s.\n"    $ show query | query <- queries  ast]
        evStr        = concat [printf "evidence %s.\n" $ show ev    | ev    <- evidence ast]

newtype PredicateLabel = PredicateLabel String deriving (Eq, Generic)
instance Hashable PredicateLabel
instance Show PredicateLabel
    where
    show (PredicateLabel l) = l

newtype RFuncLabel     = RFuncLabel String     deriving (Eq, Generic)
instance Show RFuncLabel
    where
    show (RFuncLabel label) = label
instance Hashable RFuncLabel

data RFuncDef = Flip     Probability
              | RealDist (Rational -> Probability) (Probability -> Rational)

instance Show RFuncDef
    where
    show (Flip p)       = printf "flip(%s)" $ show p
    show (RealDist _ _) = printf "realDist"

newtype RuleBody = RuleBody [RuleBodyElement] deriving (Eq, Generic)

instance Show RuleBody
    where
    show (RuleBody elements) = showLst elements
instance Hashable RuleBody

data RuleBodyElement = UserPredicate    PredicateLabel [Expr]
                     | BuildInPredicate BuildInPredicate
                     deriving (Eq, Generic)

instance Show RuleBodyElement where
    show (UserPredicate label args) = printf "%s(%s)" (show label) (showLst args)
    show (BuildInPredicate prd)     = show prd
instance Hashable RuleBodyElement

-- the arguments in head definitions are restricted to variables and constants
data HeadArgument = ArgVariable VarName
                  | ArgConstant ConstantExpr
                  | ArgDontCareVariable
                  deriving (Eq, Show, Generic)
instance Hashable HeadArgument

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
          | RFunc        RFuncLabel [Expr]
          | Variable     VarName
          | Sum          Expr Expr
          deriving (Eq, Generic)

instance Show Expr
    where
    show (ConstantExpr cnst)             = show cnst
    show (RFunc (RFuncLabel label) args) = printf "~%s(%s)" label $ showLst args
    show (Variable var)                  = show var
    show (Sum x y)                       = printf "%s + %s" (show x) (show y)
instance Hashable Expr

data ConstantExpr = BoolConstant Bool
                  | RealConstant Rational
                  | StrConstant  String
                  | IntConstant  Integer
                  deriving (Eq, Generic)

instance Show ConstantExpr
    where
    show (BoolConstant cnst) = toLower <$> show cnst
    show (RealConstant cnst) = printf "%f" (fromRat cnst::Float)
    show (StrConstant  cnst) = cnst
    show (IntConstant  cnst) = show cnst
instance Hashable ConstantExpr

negateOp :: IneqOp -> IneqOp
negateOp Lt   = GtEq
negateOp LtEq = Gt
negateOp Gt   = LtEq
negateOp GtEq = Lt

predRandomFunctions :: BuildInPredicate -> HashSet (RFuncLabel, [Expr])
predRandomFunctions (Equality _ left right) = Set.union (exprRandomFunctions left) (exprRandomFunctions right)
predRandomFunctions (Ineq     _ left right) = Set.union (exprRandomFunctions left) (exprRandomFunctions right)

exprRandomFunctions :: Expr -> HashSet (RFuncLabel, [Expr])
exprRandomFunctions (RFunc label args) = Set.singleton (label, args)
exprRandomFunctions (Variable _)       = Set.empty
exprRandomFunctions (ConstantExpr _)   = Set.empty
exprRandomFunctions (Sum x y)          = Set.union (exprRandomFunctions x) (exprRandomFunctions y)
