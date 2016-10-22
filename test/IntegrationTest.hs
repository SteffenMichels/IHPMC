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
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map

data IntegrationTest = IntegrationTest
    { label           :: String
    , model           :: String
    , expectedResults :: [ ( HashMap String Int -> AST.RuleBodyElement
                           , Exceptional Exception (Maybe ProbabilityBounds) -> HashMap String Int -> Bool
                           )
                         ]
    }

undefinedQueryId :: Int
undefinedQueryId = -1

query :: String -> HashMap String Int -> AST.RuleBodyElement
query label strs2id = AST.UserPredicate
    (AST.PredicateLabel $ Map.lookupDefault undefinedQueryId label strs2id)
    []

queryStr :: String -> [String] -> HashMap String Int -> AST.RuleBodyElement
queryStr label exprs strs2id = AST.UserPredicate
    (AST.PredicateLabel $ Map.lookupDefault undefined label strs2id)
    (AST.ConstantExpr . AST.StrConstant <$> exprs)

queryInt :: String -> [Integer] -> HashMap String Int -> AST.RuleBodyElement
queryInt label exprs strs2id = AST.UserPredicate
    (AST.PredicateLabel $ Map.lookupDefault undefined label strs2id)
    (AST.ConstantExpr . AST.IntConstant <$> exprs)

preciseProb :: Probability -> Exceptional Exception (Maybe ProbabilityBounds) -> HashMap String Int-> Bool
preciseProb p (Success (Just (ProbabilityBounds l u))) _ | l == u && l == p = True
preciseProb _ _ _                                                           = False

nonGround :: String -> Int -> Int -> Exceptional Exception a -> HashMap String Int -> Bool
nonGround expLabel expN expNPreds (Exception (Main.GrounderException (Grounder.NonGroundPreds prds (AST.PredicateLabel label) n))) strs2id
    | label == Map.lookupDefault undefined expLabel strs2id && n == expN && length prds == expNPreds = True
nonGround _ _ _ _ _                                                                                  = False

typeError :: Exceptional Exception a -> HashMap String Int -> Bool
typeError (Exception (Main.GrounderException (Grounder.TypeError _ _))) _ = True
typeError _                                                             _ = False

nonGroundQuery :: Exceptional Exception a -> HashMap String Int -> Bool
nonGroundQuery (Exception (Main.GrounderException (Grounder.NonGroundQuery _))) _ = True
nonGroundQuery _                                                                _ = False

unsolvableConstrs :: Exceptional Exception a -> HashMap String Int -> Bool
unsolvableConstrs (Exception (Main.GrounderException (Grounder.UnsolvableConstraints _))) _ = True
unsolvableConstrs _                                                                       _ = False

undefinedRf :: String -> Int -> Exceptional Exception a -> HashMap String Int -> Bool
undefinedRf expRf expN  (Exception (Main.GrounderException (Grounder.UndefinedRf pf n))) strs2id
    | AST.PFuncLabel (Map.lookupDefault undefined expRf strs2id) == pf && expN == n = True
undefinedRf _ _ _ _                                                                 = False

undefinedPred :: String -> Int -> Exceptional Exception a -> HashMap String Int -> Bool
undefinedPred expPred expN  (Exception (Main.GrounderException (Grounder.UndefinedPred prd n))) strs2id
    | AST.PredicateLabel (Map.lookupDefault undefinedQueryId expPred strs2id) == prd && expN == n = True
undefinedPred _ _ _ _                                                                             = False

undefinedRfVal :: String -> Int -> Exceptional Exception a -> HashMap String Int -> Bool
undefinedRfVal expRf expN  (Exception (Main.GrounderException (Grounder.UndefinedRfValue pf args))) strs2id
    | AST.PFuncLabel (Map.lookupDefault undefined expRf strs2id) == pf && expN == length args = True
undefinedRfVal _ _ _ _                                                                        = False

pfAsArg :: Exceptional Exception a -> HashMap String Int -> Bool
pfAsArg (Exception (Main.GrounderException Grounder.ProbabilisticFuncUsedAsArg)) _ = True
pfAsArg _                                                                        _ = False
