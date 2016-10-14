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

module IntegrationTest
    ( IntegrationTest(..)
    , query
    , queryStr
    , queryInt
    , preciseProb
    , nonGround
    , typeError
    , nonGroundQuery
    , unsolvableConstrs
    , undefinedRf
    , undefinedPred
    , undefinedRfVal
    , pfAsArg
    )
where
import Probability
import Exception
import qualified AST
import Main (Exception(..))
import qualified Grounder

data IntegrationTest = IntegrationTest
    { label           :: String
    , model           :: String
    , expectedResults :: [(AST.RuleBodyElement, Exceptional Exception (Maybe ProbabilityBounds) -> Bool)]
    }

query :: String -> AST.RuleBodyElement
query label = AST.UserPredicate (AST.PredicateLabel label) []

queryStr :: String -> [String] -> AST.RuleBodyElement
queryStr label exprs = AST.UserPredicate (AST.PredicateLabel label) (AST.ConstantExpr . AST.StrConstant <$> exprs)

queryInt :: String -> [Integer] -> AST.RuleBodyElement
queryInt label exprs = AST.UserPredicate (AST.PredicateLabel label) (AST.ConstantExpr . AST.IntConstant <$> exprs)

preciseProb :: Probability -> Exceptional Exception (Maybe ProbabilityBounds) -> Bool
preciseProb p (Success (Just (ProbabilityBounds l u))) | l == u && l == p = True
preciseProb _ _                                                           = False

nonGround :: String -> Int -> Int -> Exceptional Exception a -> Bool
nonGround expLabel expN expNPreds (Exception (Main.GrounderException (Grounder.NonGroundPreds prds (AST.PredicateLabel label) n)))
    | label == expLabel && n == expN && length prds == expNPreds = True
nonGround _ _ _ _                                                = False

typeError :: Exceptional Exception a -> Bool
typeError (Exception (Main.GrounderException (Grounder.TypeError _ _))) = True
typeError _                                                             = False

nonGroundQuery :: Exceptional Exception a -> Bool
nonGroundQuery (Exception (Main.GrounderException (Grounder.NonGroundQuery _))) = True
nonGroundQuery _                                                                = False

unsolvableConstrs :: Exceptional Exception a -> Bool
unsolvableConstrs (Exception (Main.GrounderException (Grounder.UnsolvableConstraints _))) = True
unsolvableConstrs _                                                                       = False

undefinedRf :: String -> Int -> Exceptional Exception a -> Bool
undefinedRf expRf expN  (Exception (Main.GrounderException (Grounder.UndefinedRf pf n)))
    | AST.PFuncLabel expRf == pf && expN == n = True
undefinedRf _ _ _                             = False

undefinedPred :: String -> Int -> Exceptional Exception a -> Bool
undefinedPred expPred expN  (Exception (Main.GrounderException (Grounder.UndefinedPred prd n)))
    | AST.PredicateLabel expPred == prd && expN == n = True
undefinedPred _ _ _                                  = False

undefinedRfVal :: String -> Int -> Exceptional Exception a -> Bool
undefinedRfVal expRf expN  (Exception (Main.GrounderException (Grounder.UndefinedRfValue pf args)))
    | AST.PFuncLabel expRf == pf && expN == length args = True
undefinedRfVal _ _ _                                    = False

pfAsArg :: Exceptional Exception a -> Bool
pfAsArg (Exception (Main.GrounderException Grounder.ProbabilisticFuncUsedAsArg)) = True
pfAsArg _                                                                        = False
