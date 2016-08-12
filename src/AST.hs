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
    , RealN
    , IneqOp(..)
    , VarName(..)
    , ObjectLabel(..)
    --, deterministicValue
    , predRandomFunctions
    --, exprRandomFunctions
    --, negatePred
    , negateOp
    --, checkRealIneqPred
    --, onBoundary
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
--import Interval ((~<), (~>), (~<=), (~>=))
--import qualified Interval

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
              | Object ObjectLabel
              deriving (Eq, Show, Generic)
instance Hashable Argument
data VarName = VarName String
             | TempVar Integer
             deriving (Eq, Show, Generic)
instance Hashable VarName
data ObjectLabel  = ObjectStr String | ObjectInt Integer deriving (Eq, Show, Generic)
instance Hashable ObjectLabel

data BuildInPredicate = BoolEq Bool (Expr Bool) (Expr Bool)
                      | RealIneq IneqOp (Expr RealN) (Expr RealN)
                      | Constant Bool
                      deriving (Eq, Generic)

instance Show BuildInPredicate
    where
    show (BoolEq eq exprX exprY)   = printf "%s %s %s"  (show exprX) (if eq then "=" else "/=") (show exprY)
    show (RealIneq op exprX exprY) = printf "%s %s %s" (show exprX) (show op) (show exprY)
    show (Constant cnst)           = show cnst
instance Hashable BuildInPredicate

data IneqOp = Lt | LtEq | Gt | GtEq deriving (Eq, Generic)
instance Show IneqOp
    where
    show Lt   = "<"
    show LtEq = "<="
    show Gt   = ">"
    show GtEq = ">="
instance Hashable IneqOp

data Expr a
    where
    ConstantExpr :: ConstantExpr a           -> Expr a
    RFunc        :: RFuncLabel -> [Argument] -> Expr a -- type depends on user input, has to be typechecked at runtime
    RealSum      :: Expr RealN -> Expr RealN -> Expr RealN

deriving instance Eq (Expr a)
instance Show (Expr a)
    where
    show (ConstantExpr cnst)             = show cnst
    show (RFunc (RFuncLabel label) args) = printf "~%s(%s)" label $ intercalate ", " $ show <$> args
    show (RealSum x y)                   = printf "%s + %s" (show x) (show y)
instance Hashable (Expr a)
    where
    hash = Hashable.hashWithSalt 0
    hashWithSalt salt (ConstantExpr cExpr) = Hashable.hashWithSalt salt cExpr
    hashWithSalt salt (RFunc r args)       = Hashable.hashWithSalt (Hashable.hashWithSalt salt r) args
    hashWithSalt salt (RealSum x y)        = Hashable.hashWithSalt (Hashable.hashWithSalt salt x) y

data ConstantExpr a
    where
    BoolConstant :: Bool     -> ConstantExpr Bool
    RealConstant :: Rational -> ConstantExpr RealN

deriving instance Eq (ConstantExpr a)
instance Show (ConstantExpr a)
    where
    show (BoolConstant cnst) = printf "%s" (toLower <$> show cnst)
    show (RealConstant cnst) = printf "%f" (fromRat cnst::Float)
instance Hashable (ConstantExpr a)
    where
    hash = Hashable.hashWithSalt 0
    hashWithSalt salt (BoolConstant b) = Hashable.hashWithSalt salt b
    hashWithSalt salt (RealConstant r) = Hashable.hashWithSalt salt r

{-negatePred :: BuildInPredicate -> BuildInPredicate
negatePred (BoolEq eq exprX exprY)   = BoolEq (not eq) exprX exprY
negatePred (RealIneq op exprX exprY) = RealIneq (negateOp op) exprX exprY
negatePred (Constant cnst)           = Constant $ not cnst-}

negateOp :: IneqOp -> IneqOp
negateOp Lt   = GtEq
negateOp LtEq = Gt
negateOp Gt   = LtEq
negateOp GtEq = Lt

{-deterministicValue :: BuildInPredicate -> Maybe Bool
deterministicValue (BoolEq eq (BoolConstant left) (BoolConstant right))                   = Just $ (if eq then (==) else (/=)) left right
deterministicValue (BoolEq eq (RFunc x argsX) (RFunc y argsY)) | x == y && argsX == argsY = Just eq
deterministicValue (Constant val)                                                         = Just val
deterministicValue _                                                                      = Nothing-}

predRandomFunctions :: BuildInPredicate -> HashSet (RFuncLabel, [Argument])
predRandomFunctions (BoolEq _ left right)   = Set.union (exprRandomFunctions left) (exprRandomFunctions right)
predRandomFunctions (RealIneq _ left right) = Set.union (exprRandomFunctions left) (exprRandomFunctions right)
predRandomFunctions (Constant _)            = Set.empty

exprRandomFunctions :: Expr t -> HashSet (RFuncLabel, [Argument])
exprRandomFunctions (RFunc label args) = Set.singleton (label, args)
exprRandomFunctions (ConstantExpr _)   = Set.empty
exprRandomFunctions (RealSum x y)      = Set.union (exprRandomFunctions x) (exprRandomFunctions y)

{-checkRealIneqPred :: IneqOp
                  -> Expr RealN
                  -> Expr RealN
                  -> Map.HashMap RFuncLabel Interval.IntervalLimitPoint
                  -> Maybe Bool -- result may be undetermined -> Nothing
checkRealIneqPred op left right point = case op of
    AST.Lt   -> evalLeft ~<  evalRight
    AST.LtEq -> evalLeft ~<= evalRight
    AST.Gt   -> evalLeft ~>  evalRight
    AST.GtEq -> evalLeft ~>= evalRight
    where
    evalLeft  = eval left  point
    evalRight = eval right point

onBoundary :: Expr RealN -> Expr RealN -> Map.HashMap RFuncLabel Interval.IntervalLimitPoint -> Bool
onBoundary left right point = Interval.nullInfte evalLeft == Interval.nullInfte evalRight
    where
    evalLeft  = eval left  point
    evalRight = eval right point

eval :: Expr RealN -> HashMap RFuncLabel Interval.IntervalLimitPoint -> Interval.IntervalLimitPoint
eval (RFunc rf@(RFuncLabel rfStr) _) point = undefined--Map.lookupDefault (error $ printf "AST.checkRealIneqPred: no point for %s" rfStr) rf point
eval (RealConstant r) _                  = Interval.rat2IntervLimPoint r
eval (RealSum x y)    point              = eval x point + eval y point-}
