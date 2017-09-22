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
                         , PFuncLabel
                         , GroundedAST.RealN
                         , GroundedAST.Object
                         , GroundedAST.Placeholder
                         , GroundedAST.Addition
                         , GroundedAST.Ineq
                         , GroundedAST.PredicateLabel(..)
                         , GroundedAST.simplifiedExpr
                         , GroundedAST.exprToText
                         , GroundedAST.simplifiedBuildInPred
                         , GroundedAST.deterministicValue
                         , makePFuncBool
                         , makePFuncReal
                         , makePFuncString
                         , makePFuncObj
                         , makePFuncObjOther
                         ) where
import qualified GroundedAST
import qualified AST
import Probability
import Data.Text (Text)

-- TODO: type for (AST.PFuncLabel, [AST.ConstantExpr])
type PFuncLabel = (AST.PFuncLabel, [AST.ConstantExpr])
type GroundedAST = GroundedAST.GroundedASTCommon PFuncLabel
type BuildInPredicate = GroundedAST.BuildInPredicateCommon PFuncLabel
type TypedBuildInPred a = GroundedAST.TypedBuildInPredCommon PFuncLabel a
type Expr a = GroundedAST.ExprCommon PFuncLabel a
type RuleBody = GroundedAST.RuleBodyCommon PFuncLabel
type RuleBodyElement = GroundedAST.RuleBodyElementCommon PFuncLabel
type PFunc = GroundedAST.PFunc PFuncLabel

makePFuncBool :: PFuncLabel -> Probability-> PFunc Bool
makePFuncBool label p = GroundedAST.PFunc label $ GroundedAST.Flip p

makePFuncReal :: PFuncLabel ->  (Rational -> Probability) -> (Probability -> Rational) -> PFunc GroundedAST.RealN
makePFuncReal label cdf cdf' = GroundedAST.PFunc label $ GroundedAST.RealDist cdf cdf'

makePFuncString :: PFuncLabel -> [(Probability, Text)] -> PFunc Text
makePFuncString label dist = GroundedAST.PFunc label $ GroundedAST.StrDist dist

makePFuncObj :: PFuncLabel -> Integer -> PFunc GroundedAST.Object
makePFuncObj label nr = GroundedAST.PFunc label $ GroundedAST.UniformObjDist nr

makePFuncObjOther :: PFuncLabel -> a{-PFuncPhase1 Object-} -> PFunc GroundedAST.Object
makePFuncObjOther label other = GroundedAST.PFunc label $ GroundedAST.UniformOtherObjDist undefined--other

