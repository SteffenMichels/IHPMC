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

module GroundedAST ( GroundedAST(..)
                   , BuildInPredicate(..)
                   , TypedBuildInPred(..)
                   , RFuncLabel(..)
                   , RFunc
                   , randomFuncDef
                   , makeRFunc
                   , Expr(..)
                   , PredicateLabel(..)
                   , ConstantExpr(..)
                   , AST.RFuncDef(..)
                   , Addition
                   , RealN
                   , RuleBody(..)
                   , RuleBodyElement(..)
                   , negatePred
                   , predRandomFunctions
                   , exprRandomFunctions
                   , deterministicValue
                   , checkRealIneqPred
                   , simplifiedBuildInPred
                   , simplifiedExpr
                   ) where
import qualified AST
import Data.Hashable (Hashable)
import qualified Data.Hashable as Hashable
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import GHC.Generics (Generic)
import Interval ((~<), (~>), (~<=), (~>=))
import qualified Interval
import Text.Printf (printf)
import Data.Char (toLower)
import Numeric (fromRat)
import Util

-- use sets here to avoid duplicate elements
data GroundedAST = GroundedAST
    { rules     :: HashMap PredicateLabel (HashSet RuleBody)
    , queries   :: HashSet RuleBodyElement
    , evidence  :: HashSet RuleBodyElement
    }
    deriving Show

-- propositional version of data types, similarly present in AST (without argument, after grounding)
newtype PredicateLabel = PredicateLabel String deriving (Eq, Generic)
instance Show PredicateLabel
    where
    show (PredicateLabel l) = l
instance Hashable PredicateLabel

data RFunc = RFunc RFuncLabel AST.RFuncDef Int -- store hash for efficiency reasons
instance Eq RFunc
    where
    RFunc x _ hx == RFunc y _ hy = hx == hy && x == y
instance Show RFunc
    where
    show (RFunc l _ _) = show l
instance Hashable RFunc
    where
    hash = Hashable.hashWithSalt 0
    -- there should never be more than one RF with the same name, so hash only name and ignore definition
    hashWithSalt salt (RFunc _ _ hash) = Hashable.hashWithSalt salt hash

randomFuncDef :: RFunc -> AST.RFuncDef
randomFuncDef (RFunc _ def _) = def

makeRFunc :: RFuncLabel -> AST.RFuncDef -> RFunc
makeRFunc label def = RFunc label def $ Hashable.hash label

newtype RFuncLabel = RFuncLabel String deriving (Eq, Generic)
instance Show RFuncLabel
    where
    show (RFuncLabel l) = l
instance Hashable RFuncLabel

newtype RuleBody = RuleBody (HashSet RuleBodyElement) deriving (Eq, Generic)

instance Show RuleBody
    where
    show (RuleBody elements) = showLst $ Set.toList elements
instance Hashable RuleBody

data RuleBodyElement = UserPredicate    PredicateLabel
                     | BuildInPredicate BuildInPredicate
                     deriving (Eq, Generic)

instance Show RuleBodyElement where
    show (UserPredicate label)  = show label
    show (BuildInPredicate prd) = show prd
instance Hashable RuleBodyElement

data BuildInPredicate = BuildInPredicateBool (TypedBuildInPred Bool)
                      | BuildInPredicateReal (TypedBuildInPred RealN)
                      | BuildInPredicateStr  (TypedBuildInPred String)
                      | BuildInPredicateInt  (TypedBuildInPred Integer)
                      deriving (Eq, Generic)
instance Show BuildInPredicate
    where
    show (BuildInPredicateBool b) = show b
    show (BuildInPredicateReal r) = show r
    show (BuildInPredicateStr  s) = show s
    show (BuildInPredicateInt  i) = show i
instance Hashable BuildInPredicate

data TypedBuildInPred a
    where
    Equality :: Bool       -> Expr a -> Expr a -> TypedBuildInPred a
    Ineq     :: AST.IneqOp -> Expr a -> Expr a -> TypedBuildInPred a
    Constant :: Bool                                   -> TypedBuildInPred a

deriving instance Eq (TypedBuildInPred a)
instance Show (TypedBuildInPred a)
    where
    show (Equality eq exprX exprY) = printf "%s %s %s" (show exprX) (if eq then "=" else "/=") (show exprY)
    show (Ineq     op exprX exprY) = printf "%s %s %s" (show exprX) (show op) (show exprY)
    show (Constant cnst)           = show cnst
instance Hashable (TypedBuildInPred a)
    where
    hash = Hashable.hashWithSalt 0
    hashWithSalt salt (Equality eq exprX exprY) = Hashable.hashWithSalt (Hashable.hashWithSalt (Hashable.hashWithSalt salt eq) exprX) exprY
    hashWithSalt salt (Ineq     op exprX exprY) = Hashable.hashWithSalt (Hashable.hashWithSalt (Hashable.hashWithSalt salt op) exprX) exprY
    hashWithSalt salt (Constant b)              = Hashable.hashWithSalt salt b

data Expr a
    where
    ConstantExpr ::               ConstantExpr a   -> Expr a
    RFuncExpr    ::               RFunc            -> Expr a
    Sum          :: Addition a => Expr a -> Expr a -> Expr a

deriving instance Eq (Expr a)
instance Show (Expr a)
    where
    show (ConstantExpr cExpr) = show cExpr
    show (RFuncExpr rf)       = show rf
    show (Sum x y)            = printf "%s + %s" (show x) (show y)
instance Hashable (Expr a)
    where
    hash = Hashable.hashWithSalt 0
    hashWithSalt salt (ConstantExpr cExpr) = Hashable.hashWithSalt salt cExpr
    hashWithSalt salt (RFuncExpr r)        = Hashable.hashWithSalt salt r
    hashWithSalt salt (Sum x y)            = Hashable.hashWithSalt (Hashable.hashWithSalt salt x) y

data ConstantExpr a
    where
    BoolConstant :: Bool     -> ConstantExpr Bool
    RealConstant :: Rational -> ConstantExpr RealN
    StrConstant  :: String   -> ConstantExpr String
    IntConstant  :: Integer  -> ConstantExpr Integer

deriving instance Eq (ConstantExpr a)
instance Show (ConstantExpr a)
    where
    show (BoolConstant cnst) = printf "%s" (toLower <$> show cnst)
    show (RealConstant cnst) = printf "%f" (fromRat cnst::Float)
    show (StrConstant  cnst) = cnst
    show (IntConstant  cnst) = show cnst
instance Hashable (ConstantExpr a)
    where
    hash = Hashable.hashWithSalt 0
    hashWithSalt salt (BoolConstant b) = Hashable.hashWithSalt salt b
    hashWithSalt salt (RealConstant r) = Hashable.hashWithSalt salt r
    hashWithSalt salt (StrConstant  s) = Hashable.hashWithSalt salt s
    hashWithSalt salt (IntConstant  i) = Hashable.hashWithSalt salt i
instance Ord (ConstantExpr a)
    where
    BoolConstant x <= BoolConstant y = x <= y
    RealConstant x <= RealConstant y = x <= y
    StrConstant  x <= StrConstant  y = x <= y
    IntConstant  x <= IntConstant  y = x <= y

data RealN -- phantom for real numbered expression etc.

class Addition a
instance Addition Integer
instance Addition RealN

predRandomFunctions :: BuildInPredicate -> HashSet RFunc
predRandomFunctions (BuildInPredicateBool b) = predRandomFunctions' b
predRandomFunctions (BuildInPredicateReal r) = predRandomFunctions' r
predRandomFunctions (BuildInPredicateStr  s) = predRandomFunctions' s
predRandomFunctions (BuildInPredicateInt  i) = predRandomFunctions' i

predRandomFunctions' :: TypedBuildInPred a -> HashSet RFunc
predRandomFunctions' (Equality _ left right) = Set.union (exprRandomFunctions left) (exprRandomFunctions right)
predRandomFunctions' (Ineq     _ left right) = Set.union (exprRandomFunctions left) (exprRandomFunctions right)
predRandomFunctions' (Constant _)            = Set.empty

exprRandomFunctions :: Expr a -> HashSet RFunc
exprRandomFunctions (RFuncExpr rf)   = Set.singleton rf
exprRandomFunctions (ConstantExpr _) = Set.empty
exprRandomFunctions (Sum x y)        = Set.union (exprRandomFunctions x) (exprRandomFunctions y)

negatePred :: BuildInPredicate -> BuildInPredicate
negatePred (BuildInPredicateBool b) = BuildInPredicateBool $ negatePred' b
negatePred (BuildInPredicateReal r) = BuildInPredicateReal $ negatePred' r
negatePred (BuildInPredicateStr  s) = BuildInPredicateStr  $ negatePred' s
negatePred (BuildInPredicateInt  i) = BuildInPredicateInt  $ negatePred' i

negatePred' :: TypedBuildInPred a -> TypedBuildInPred a
negatePred' (Equality eq exprX exprY) = Equality (not eq) exprX exprY
negatePred' (Ineq     op exprX exprY) = Ineq (AST.negateOp op) exprX exprY
negatePred' (Constant cnst)           = Constant $ not cnst

deterministicValue :: BuildInPredicate -> Maybe Bool
deterministicValue (BuildInPredicateBool b) = deterministicValue' b
deterministicValue (BuildInPredicateReal r) = deterministicValue' r
deterministicValue (BuildInPredicateStr  s) = deterministicValue' s
deterministicValue (BuildInPredicateInt  i) = deterministicValue' i

deterministicValue' :: TypedBuildInPred a -> Maybe Bool
deterministicValue' (Equality eq (ConstantExpr left) (ConstantExpr right))              = Just $ (if eq then (==) else (/=)) left right
deterministicValue' (Equality eq (RFuncExpr left)    (RFuncExpr right)) | left == right = Just eq
deterministicValue' (Ineq     op (ConstantExpr left) (ConstantExpr right))              = Just evalPred
    where
    evalPred = case op of
        AST.Lt   -> left <  right
        AST.LtEq -> left <= right
        AST.Gt   -> left >  right
        AST.GtEq -> left >= right
deterministicValue' (Constant val)                                           = Just val
deterministicValue' _                                                        = Nothing

checkRealIneqPred :: AST.IneqOp
                  -> Expr RealN
                  -> Expr RealN
                  -> Map.HashMap RFunc Interval.IntervalLimitPoint
                  -> Maybe Bool -- result may be undetermined -> Nothing
checkRealIneqPred op left right point = case op of
    AST.Lt   -> evalLeft ~<  evalRight
    AST.LtEq -> evalLeft ~<= evalRight
    AST.Gt   -> evalLeft ~>  evalRight
    AST.GtEq -> evalLeft ~>= evalRight
    where
    evalLeft  = eval left  point
    evalRight = eval right point

eval :: Expr RealN -> HashMap RFunc Interval.IntervalLimitPoint -> Interval.IntervalLimitPoint
eval (RFuncExpr rf) point              = Map.lookupDefault (error $ printf "AST.checkRealIneqPred: no point for %s" $ show rf) rf point
eval (ConstantExpr (RealConstant r)) _ = Interval.rat2IntervLimPoint r
eval (Sum x y) point                   = eval x point + eval y point

simplifiedBuildInPred :: BuildInPredicate -> BuildInPredicate
simplifiedBuildInPred (BuildInPredicateBool prd) = BuildInPredicateBool $ simplifiedTypedBuildInPred prd
simplifiedBuildInPred (BuildInPredicateReal prd) = BuildInPredicateReal $ simplifiedTypedBuildInPred prd
simplifiedBuildInPred (BuildInPredicateInt  prd) = BuildInPredicateInt  $ simplifiedTypedBuildInPred prd
simplifiedBuildInPred (BuildInPredicateStr  prd) = BuildInPredicateStr  $ simplifiedTypedBuildInPred prd

simplifiedTypedBuildInPred :: TypedBuildInPred a -> TypedBuildInPred a
simplifiedTypedBuildInPred (Equality eq exprX exprY) = Equality eq (simplifiedExpr exprX) (simplifiedExpr exprY)
simplifiedTypedBuildInPred (Ineq     op exprX exprY) = Ineq     op (simplifiedExpr exprX) (simplifiedExpr exprY)
simplifiedTypedBuildInPred prd'                      = prd'

simplifiedExpr :: Expr a -> Expr a
simplifiedExpr (Sum exprX exprY) = case (simplifiedExpr exprX, simplifiedExpr exprY) of
    (ConstantExpr x, ConstantExpr y) -> ConstantExpr (add x y)
    (exprX',        exprY')          -> Sum exprX' exprY'
simplifiedExpr expr = expr

add :: Addition a => ConstantExpr a -> ConstantExpr a -> ConstantExpr a
add (RealConstant x) (RealConstant y) = RealConstant (x + y)
add (IntConstant  x) (IntConstant  y) = IntConstant  (x + y)
add _                            _    = error "Formula.refBuildInPredicate"
