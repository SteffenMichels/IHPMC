--The MIT License (MIT)
--
--Copyright (c) 2016-2017 Steffen Michels (mail@steffen-michels.de)
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

{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE Strict#-}
#endif

module GroundedASTPhase2 ( GroundedAST
                         , Expr
                         , BuildInPredicate
                         , TypedBuildInPred
                         , RuleBody
                         , RuleBodyElement
                         , PFuncLabel
                         , PFunc
                         , predProbabilisticFunctions
                         , exprProbabilisticFunctions
                         , checkRealIneqPred
                         , pFuncLabelToText
                         ) where
import qualified GroundedAST
import qualified AST
import TextShow
import Util
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Data.HashMap (Map)
import qualified Data.HashMap as Map
import Data.HashSet (Set)
import qualified Data.HashSet as Set
import Data.Text (Text)
import qualified Data.Text.Lazy.Builder as TB
import qualified Interval
import Interval ((~<), (~>), (~<=), (~>=))
import Data.Monoid ((<>))

type GroundedAST = GroundedAST.GroundedAST PFuncLabel
type BuildInPredicate = GroundedAST.BuildInPredicate PFuncLabel
type TypedBuildInPred a = GroundedAST.TypedBuildInPred PFuncLabel a
type Expr a = GroundedAST.Expr PFuncLabel a
type RuleBody = GroundedAST.RuleBody PFuncLabel
type RuleBodyElement = GroundedAST.RuleBodyElement PFuncLabel
type PFunc a = GroundedAST.PFunc PFuncLabel a

newtype PFuncLabel = PFuncLabel Int deriving (Eq, Generic, Ord)
pFuncLabelToText :: PFuncLabel -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder
pFuncLabelToText (PFuncLabel idNr) ids2str ids2label =
    "~" <>
    TB.fromText (Map.findWithDefault undefined label ids2str) <>
    if null args then "" else "(" <> showbLst args <> ")"
    where
    (label, args) = Map.findWithDefault (0, []) idNr ids2label
instance Hashable PFuncLabel

predProbabilisticFunctions :: TypedBuildInPred a -> Set (PFunc a)
predProbabilisticFunctions (GroundedAST.Equality _ left right) = Set.union (exprProbabilisticFunctions left) (exprProbabilisticFunctions right)
predProbabilisticFunctions (GroundedAST.Ineq     _ left right) = Set.union (exprProbabilisticFunctions left) (exprProbabilisticFunctions right)
predProbabilisticFunctions (GroundedAST.Constant _)            = Set.empty

exprProbabilisticFunctions :: Expr a -> Set (PFunc a)
exprProbabilisticFunctions (GroundedAST.PFuncExpr pf) = case GroundedAST.probabilisticFuncDef pf of
    GroundedAST.UniformOtherObjDist otherPf -> Set.insert pf $ exprProbabilisticFunctions $ GroundedAST.PFuncExpr undefined--otherPf
    _                                       -> Set.singleton pf
exprProbabilisticFunctions (GroundedAST.ConstantExpr _) = Set.empty
exprProbabilisticFunctions (GroundedAST.Sum x y)        = Set.union (exprProbabilisticFunctions x) (exprProbabilisticFunctions y)

checkRealIneqPred :: AST.IneqOp
                  -> Expr GroundedAST.RealN
                  -> Expr GroundedAST.RealN
                  -> Map PFuncLabel Interval.IntervalLimitPoint
                  -> Maybe Bool -- result may be undetermined -> Nothing
checkRealIneqPred op left right point = case op of
    AST.Lt   -> evalLeft ~<  evalRight
    AST.LtEq -> evalLeft ~<= evalRight
    AST.Gt   -> evalLeft ~>  evalRight
    AST.GtEq -> evalLeft ~>= evalRight
    where
    evalLeft  = eval left  point
    evalRight = eval right point

    eval :: Expr GroundedAST.RealN -> Map PFuncLabel Interval.IntervalLimitPoint -> Interval.IntervalLimitPoint
    eval (GroundedAST.PFuncExpr pf) point              = Map.findWithDefault (error "AST.checkRealIneqPred: no point") (GroundedAST.probabilisticFuncLabel pf) point
    eval (GroundedAST.ConstantExpr (GroundedAST.RealConstant r)) _ = Interval.rat2IntervLimPoint r
    eval (GroundedAST.Sum x y) point                   = eval x point + eval y point

