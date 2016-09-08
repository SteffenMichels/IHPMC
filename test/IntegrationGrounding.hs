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

{-# LANGUAGE QuasiQuotes #-}

module IntegrationGrounding (tests)
where
import BasicTypes
import NeatInterpolation
import IntegrationTest
import Data.Text (unpack)
import Exception
import Main (Exception(..))
import qualified AST
import qualified Grounder

tests :: (String, [IntegrationTest])
tests = ("grounding", [ varsInExpr, existVars, count
                      ]
        )

varsInExpr :: IntegrationTest
varsInExpr = IntegrationTest
    { label = "variables in expressions"
    , model = unpack $ [text|
                  varsInExpr(X, Y) <- Y = X, X = abc.
              |]
    , expectedResults =
        [ (queryStr "varsInExpr" ["abc", "abc"], preciseProb 1.0)
        , (queryStr "varsInExpr" ["ab", "ab"],   preciseProb 0.0)
        , (queryStr "varsInExpr" ["abc", "ab"],  preciseProb 0.0)
        ]
    }

existVars :: IntegrationTest
existVars = IntegrationTest
    { label = "existentially quantified variables"
    , model = unpack $ [text|
                  ~a(1) ~ flip(0.1).
                  ~a(2) ~ flip(0.2).
                  ~a(3) ~ flip(0.3).
                  ~a(7) ~ flip(0.4).
                  ~a(8) ~ flip(0.5).
                  p(X).
                  q(1).
                  r(2).
                  r(3).
                  s(4).
                  exists1 <- ~a(X) = true, q(X).
                  exists2 <- ~a(X) = ~a(Y), q(X), r(Y).
                  exists3 <- ~a(X + Y + Z) = true, q(X), r(Y), s(Z).
                  nonGround <- p(X), Y = Z.
              |]
    , expectedResults =
        [ (queryStr "exists1"    [], preciseProb 0.1)
        , (queryStr "exists2"    [], preciseProb 0.89)
        , (queryStr "exists3"    [], preciseProb 0.7)
        , ( queryStr "nonGround" []
          , \res -> case res of
                Exception (Main.GrounderException (
                    Grounder.NonGroundPreds prds (AST.PredicateLabel "nonGround") 0)
                    ) | length prds == 2 -> True
                _                        -> False
          )
        ]
    }

count :: IntegrationTest
count = IntegrationTest
    { label = "count"
    , model = unpack $ [text|
                  ~count(X) ~ flip(0.1).
                  count(X) <- ~count(X) = true.
                  count(X) <- X < 10, Y = X + 1, count(Y).
              |]
    , expectedResults =
        [ (queryInt "count" [1],  preciseProb 0.6513215599)
        , (queryInt "count" [6],  preciseProb 0.40951)
        , (queryInt "count" [10], preciseProb 0.1)
        ]
    }

queryStr :: String -> [String] -> (AST.PredicateLabel, [AST.Expr])
queryStr label exprs = (AST.PredicateLabel label, AST.ConstantExpr . AST.StrConstant <$> exprs)

queryInt :: String -> [Integer] -> (AST.PredicateLabel, [AST.Expr])
queryInt label exprs = (AST.PredicateLabel label, AST.ConstantExpr . AST.IntConstant <$> exprs)

preciseProb :: Probability -> Exceptional Exception (Probability, Probability) -> Bool
preciseProb p (Success (l, u)) | l == u && l == p = True
preciseProb _ _                                   = False
