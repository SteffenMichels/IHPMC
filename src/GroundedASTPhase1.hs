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

module GroundedASTPhase1 ( GroundedAST
                         , GroundedAST.GroundedASTCommon(..)
                         , Expr
                         , PFunc
                         , GroundedAST.PFuncCommon(..)
                         , PFuncDef
                         , GroundedAST.PFuncDefCommon(..)
                         , GroundedAST.ExprCommon(..)
                         , GroundedAST.ConstantExpr(..)
                         , BuildInPredicate
                         , GroundedAST.BuildInPredicateCommon(..)
                         , TypedBuildInPred
                         , GroundedAST.TypedBuildInPredCommon(..)
                         , RuleBody
                         , GroundedAST.RuleBodyCommon(..)
                         , RuleBodyElement
                         , GroundedAST.RuleBodyElementCommon(..)
                         , PFuncLabel(..)
                         , GroundedAST.RealN
                         , GroundedAST.Object
                         , GroundedAST.Placeholder
                         , GroundedAST.Addition
                         , GroundedAST.Ineq
                         , GroundedAST.PredicateLabel(..)
                         , simplifiedExpr
                         , groundedAstToText
                         , exprToText
                         , pFuncLabelToText
                         , simplifiedBuildInPred
                         , GroundedAST.deterministicValue
                         , makePFuncBool
                         , makePFuncReal
                         , makePFuncString
                         , makePFuncObj
                         , makePFuncObjOther
                         ) where
import qualified GroundedASTCommon as GroundedAST
import qualified AST
import Probability
import TextShow
import Util
import Data.Text (Text)
import Data.HashMap (Map)
import Data.Monoid ((<>))
import GHC.Generics (Generic)
import Data.Hashable (Hashable)

data PFuncLabel = PFuncLabel AST.PFuncLabel [AST.ConstantExpr] deriving (Ord, Eq, Generic)
instance Hashable PFuncLabel
type GroundedAST = GroundedAST.GroundedASTCommon PFuncLabel
type BuildInPredicate = GroundedAST.BuildInPredicateCommon PFuncLabel
type TypedBuildInPred a = GroundedAST.TypedBuildInPredCommon PFuncLabel a
type Expr a = GroundedAST.ExprCommon PFuncLabel a
type RuleBody = GroundedAST.RuleBodyCommon PFuncLabel
type RuleBodyElement = GroundedAST.RuleBodyElementCommon PFuncLabel
type PFunc = GroundedAST.PFuncCommon PFuncLabel
type PFuncDef = GroundedAST.PFuncDefCommon PFuncLabel

makePFuncBool :: PFuncLabel -> Probability-> PFunc Bool
makePFuncBool label p = GroundedAST.PFunc label $ GroundedAST.Flip p

makePFuncReal :: PFuncLabel ->  (Rational -> Probability) -> (Probability -> Rational) -> PFunc GroundedAST.RealN
makePFuncReal label cdf cdf' = GroundedAST.PFunc label $ GroundedAST.RealDist cdf cdf'

makePFuncString :: PFuncLabel -> [(Probability, Text)] -> PFunc Text
makePFuncString label dist = GroundedAST.PFunc label $ GroundedAST.StrDist dist

makePFuncObj :: PFuncLabel -> Integer -> PFunc GroundedAST.Object
makePFuncObj label nr = GroundedAST.PFunc label $ GroundedAST.UniformObjDist nr

makePFuncObjOther :: PFuncLabel -> PFunc GroundedAST.Object -> PFunc GroundedAST.Object
makePFuncObjOther label other = GroundedAST.PFunc label $ GroundedAST.UniformOtherObjDist other

simplifiedBuildInPred :: BuildInPredicate -> BuildInPredicate
simplifiedBuildInPred (GroundedAST.BuildInPredicateBool prd) = GroundedAST.BuildInPredicateBool $ simplifiedTypedBuildInPred prd
simplifiedBuildInPred (GroundedAST.BuildInPredicateReal prd) = GroundedAST.BuildInPredicateReal $ simplifiedTypedBuildInPred prd
simplifiedBuildInPred (GroundedAST.BuildInPredicateInt  prd) = GroundedAST.BuildInPredicateInt  $ simplifiedTypedBuildInPred prd
simplifiedBuildInPred (GroundedAST.BuildInPredicateStr  prd) = GroundedAST.BuildInPredicateStr  $ simplifiedTypedBuildInPred prd
simplifiedBuildInPred (GroundedAST.BuildInPredicateObj  prd) = GroundedAST.BuildInPredicateObj  $ simplifiedTypedBuildInPred prd
simplifiedBuildInPred (GroundedAST.BuildInPredicatePh   prd) = GroundedAST.BuildInPredicatePh   $ simplifiedTypedBuildInPred prd

simplifiedTypedBuildInPred :: TypedBuildInPred a -> TypedBuildInPred a
simplifiedTypedBuildInPred (GroundedAST.Equality eq exprX exprY) = GroundedAST.Equality eq (simplifiedExpr exprX) (simplifiedExpr exprY)
simplifiedTypedBuildInPred (GroundedAST.Ineq     op exprX exprY) = GroundedAST.Ineq     op (simplifiedExpr exprX) (simplifiedExpr exprY)
simplifiedTypedBuildInPred prd'                                  = prd'

simplifiedExpr :: Expr a -> Expr a
simplifiedExpr (GroundedAST.Sum exprX exprY) = case (simplifiedExpr exprX, simplifiedExpr exprY) of
    (GroundedAST.ConstantExpr x, GroundedAST.ConstantExpr y) -> GroundedAST.ConstantExpr (add x y)
    (exprX',        exprY')          -> GroundedAST.Sum exprX' exprY'
simplifiedExpr expr = expr

add :: GroundedAST.Addition a => GroundedAST.ConstantExpr a -> GroundedAST.ConstantExpr a -> GroundedAST.ConstantExpr a
add (GroundedAST.RealConstant x) (GroundedAST.RealConstant y) = GroundedAST.RealConstant (x + y)
add (GroundedAST.IntConstant  x) (GroundedAST.IntConstant  y) = GroundedAST.IntConstant  (x + y)

-- Text functions

groundedAstToText :: GroundedAST
                  -> Map Int Text
                  -> Map Int (Int, [AST.ConstantExpr])
                  -> Builder
groundedAstToText gast = GroundedAST.groundedAstToText gast (\pf ids2str _ -> pFuncLabelToText pf ids2str)

pFuncLabelToText :: PFuncLabel -> Map Int Text -> Builder
pFuncLabelToText (PFuncLabel label args) ids2str =
    "~" <> AST.pFuncLabelToText label ids2str <>
    if null args then "" else "(" <> showbLst args <> ")"

exprToText :: Expr a
           -> Map Int Text
           -> Map Int (Int, [AST.ConstantExpr])
           -> Builder
exprToText expr = GroundedAST.exprToText expr (\label ids2str _ -> pFuncLabelToText label ids2str)

