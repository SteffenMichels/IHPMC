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
                         , Expr
                         , BuildInPredicate
                         , TypedBuildInPred
                         , RuleBody
                         , RuleBodyElement
                         , PFuncLabel
                         ) where
import qualified GroundedAST
import qualified AST

-- TODO: type for (AST.PFuncLabel, [AST.ConstantExpr])
type PFuncLabel = (AST.PFuncLabel, [AST.ConstantExpr])
type GroundedAST = GroundedAST.GroundedAST PFuncLabel
type BuildInPredicate = GroundedAST.BuildInPredicate PFuncLabel
type TypedBuildInPred a = GroundedAST.TypedBuildInPred PFuncLabel a
type Expr a = GroundedAST.Expr PFuncLabel a
type RuleBody = GroundedAST.RuleBody PFuncLabel
type RuleBodyElement = GroundedAST.RuleBodyElement PFuncLabel

