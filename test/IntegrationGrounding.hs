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
import NeatInterpolation
import IntegrationTest
import Data.Text (unpack)
import Exception
import Main (Exception(..))
import qualified AST
import qualified Grounder
import Probability

tests :: (String, [IntegrationTest])
tests = ("grounding", [ types, preds, rfs, varsInExpr, existVars, count, tablingProp, tablingFO
                      ]
        )

types :: IntegrationTest
types = IntegrationTest
    { label = "type checking"
    , model = unpack $ [text|
                  ~bool ~ flip(0.01).
                  bool    <- ~bool = true.
                  boolErr <- ~bool = 1.
                  ~real ~ norm(0.0, 1.0).
                  real     <- ~real > 0.0.
                  realErr  <- ~real > 0.
                  realErr2 <- ~real + 1 > 0.0.
                  int     <- 1 < 2.
                  intErr  <- 1 < two.
                  intErr2 <- 1 + zero < 2.
                  string    <- abc /= abcd.
                  stringErr <- abc /= false.
              |]
    , expectedResults =
        [ (query "bool",      preciseProb 0.01)
        , (query "boolErr",   typeError)
        , (query "real",      preciseProb 0.5)
        , (query "realErr",   typeError)
        , (query "realErr2",  typeError)
        , (query "int",       preciseProb 1.0)
        , (query "intErr",    typeError)
        , (query "intErr2",   typeError)
        , (query "string",    preciseProb 1.0)
        , (query "stringErr", typeError)
        ]
    }

preds :: IntegrationTest
preds = IntegrationTest
    { label = "predicates"
    , model = unpack $ [text|
                  ~x ~ flip(0.1).
                  ~y ~ flip(0.2).
                  a <- ~x = true.
                  b <- ~y = true.
                  c <- ~x = true, ~y = true.
                  d <- ~x = true.
                  d <- ~y = true.
                  p(a) <- a.
                  p(b) <- b.
                  p(c) <- c.
                  p(d) <- d.
                  two(X, Y) <- p(Y), p(X).
                  err <- two(a, ~x).
              |]
    , expectedResults =
        [ (query "a",                preciseProb 0.1)
        , (query "b",                preciseProb 0.2)
        , (query "c",                preciseProb 0.02)
        , (query "d",                preciseProb 0.28)
        --, (query "e", preciseProb 0.0)
        , (queryStr "two" ["a","a"], preciseProb 0.1)
        , (queryStr "two" ["a","b"], preciseProb 0.02)
        , (queryStr "two" ["a","c"], preciseProb 0.02)
        , (queryStr "two" ["a","d"], preciseProb 0.1)
        , (queryStr "two" ["c","d"], preciseProb 0.02)
        --, (queryStr "two" ["e","d"], preciseProb 0.0)
        , (query "err",              rfAsArg)
        ]
    }

rfs :: IntegrationTest
rfs = IntegrationTest
    { label = "random functions"
    , model = unpack $ [text|
                  ~rf      ~ flip(0.99).
                  ~rf(1)   ~ flip(0.991).
                  ~rf(2)   ~ flip(0.992).
                  ~rf(1,2) ~ flip(0.9912).
                  rf             <- ~rf      = true.
                  rf1            <- ~rf(1)   = true.
                  rf2            <- ~rf(2)   = true.
                  rfErrRfAsArg   <- ~rf(~rf) = true.
                  rfErrNonGround <- ~rf(X)   = true.
                  rfErrUndefined <- ~rf2     = true.
                  rfErrUndefVal  <- ~rf(3)   = true.
                  rfErrUndefVal2 <- ~rf(1,3) = true.
                  rfErrUndefVal3 <- ~rf(3,2) = true.
              |]
    , expectedResults =
        [ (query "rf",             preciseProb 0.99)
        , (query "rf1",            preciseProb 0.991)
        , (query "rf2",            preciseProb 0.992)
        , (query "rfErrRfAsArg",   rfAsArg)
        , (query "rfErrNonGround", nonGround "rfErrNonGround" 0 1)
        , (query "rfErrUndefined", undefinedRf "rf2" 0)
        , (query "rfErrUndefVal",  undefinedRfVal "rf" 1)
        , (query "rfErrUndefVal2", undefinedRfVal "rf" 2)
        , (query "rfErrUndefVal3", undefinedRfVal "rf" 2)
        ]
    }

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
                  exists3Per01 <- ~a(X + Y + Z) = true, q(X), r(Y), s(Z).
                  exists3Per02 <- ~a(X + Y + Z) = true, q(X), s(Z), r(Y).
                  exists3Per03 <- ~a(X + Y + Z) = true, r(Y), q(X), s(Z).
                  exists3Per04 <- ~a(X + Y + Z) = true, s(Z), q(X), r(Y).
                  exists3Per05 <- q(X), ~a(X + Y + Z) = true, r(Y), s(Z).
                  exists3Per06 <- q(X), ~a(X + Y + Z) = true, s(Z), r(Y).
                  exists3Per07 <- r(Y), ~a(X + Y + Z) = true, q(X), s(Z).
                  exists3Per08 <- s(Z), ~a(X + Y + Z) = true, q(X), r(Y).
                  exists3Per09 <- q(X), r(Y), ~a(X + Y + Z) = true, s(Z).
                  exists3Per10 <- q(X), s(Z), ~a(X + Y + Z) = true, r(Y).
                  exists3Per11 <- r(Y), q(X), ~a(X + Y + Z) = true, s(Z).
                  exists3Per12 <- s(Z), q(X), ~a(X + Y + Z) = true, r(Y).
                  exists3Per13 <- q(X), r(Y), s(Z), ~a(X + Y + Z) = true.
                  exists3Per14 <- q(X), s(Z), r(Y), ~a(X + Y + Z) = true.
                  exists3Per15 <- r(Y), q(X), s(Z), ~a(X + Y + Z) = true.
                  exists3Per16 <- s(Z), q(X), r(Y), ~a(X + Y + Z) = true.
                  nonGround <- p(X), Y = Z.
              |]
    , expectedResults =
        [ (query "exists1",      preciseProb 0.1)
        , (query "exists2",      preciseProb 0.89)
        , (query "exists3Per01", preciseProb 0.7)
        , (query "exists3Per02", preciseProb 0.7)
        , (query "exists3Per03", preciseProb 0.7)
        , (query "exists3Per04", preciseProb 0.7)
        , (query "exists3Per05", preciseProb 0.7)
        , (query "exists3Per06", preciseProb 0.7)
        , (query "exists3Per07", preciseProb 0.7)
        , (query "exists3Per08", preciseProb 0.7)
        , (query "exists3Per09", preciseProb 0.7)
        , (query "exists3Per10", preciseProb 0.7)
        , (query "exists3Per11", preciseProb 0.7)
        , (query "exists3Per12", preciseProb 0.7)
        , (query "exists3Per13", preciseProb 0.7)
        , (query "exists3Per14", preciseProb 0.7)
        , (query "exists3Per15", preciseProb 0.7)
        , (query "exists3Per16", preciseProb 0.7)
        , (query "nonGround",    nonGround "nonGround" 0 2)
        ]
    }

count :: IntegrationTest
count = IntegrationTest
    { label = "count"
    , model = unpack $ [text|
                  ~count(X) ~ flip(0.1).
                  count(X) <- ~count(X) = true.
                  count(X) <- X < 10, Y = X + 1, count(Y).

                  ~countPer(X) ~ flip(0.1).
                  countPer(X) <- ~countPer(X) = true.
                  countPer(X) <- countPer(Y), Y = X + 1, X < 10.
              |]
    , expectedResults =
        [ (queryInt "count"     [1], preciseProb 0.6513215599)
        , (queryInt "count"     [6], preciseProb 0.40951)
        , (queryInt "count"    [10], preciseProb 0.1)
        , (queryInt "countPer"  [1], preciseProb 0.6513215599)
        , (queryInt "countPer"  [6], preciseProb 0.40951)
        , (queryInt "countPer" [10], preciseProb 0.1)
        ]
    }

tablingProp :: IntegrationTest
tablingProp = IntegrationTest
    { label = "tabling (propositional)"
    , model = unpack $ [text|
                  ~c ~ flip(0.123).

                  a <- b.
                  b <- a.
                  b <- ~c = true.
              |]
    , expectedResults =
        [ (query "a", preciseProb 0.123)
        , (query "b", preciseProb 0.123)
        ]
    }

tablingFO :: IntegrationTest
tablingFO = IntegrationTest
    { label = "tabling (first-order)"
    , model = unpack $ [text|
                  ~x ~ flip(0.123).

                  p(X) <- p(X + 1), X = 1.
                  p(2) <- p(1 + 0).
                  p(2) <- ~x = true.
              |]
    , expectedResults =
        [ (queryInt "p" [1], preciseProb 0.123)
        , (queryInt "p" [2], preciseProb 0.123)
        ]
    }

query :: String -> AST.RuleBodyElement
query label = AST.UserPredicate (AST.PredicateLabel label) []

queryStr :: String -> [String] -> AST.RuleBodyElement
queryStr label exprs = AST.UserPredicate (AST.PredicateLabel label) (AST.ConstantExpr . AST.StrConstant <$> exprs)

queryInt :: String -> [Integer] -> AST.RuleBodyElement
queryInt label exprs = AST.UserPredicate (AST.PredicateLabel label) (AST.ConstantExpr . AST.IntConstant <$> exprs)

preciseProb :: Probability -> Exceptional Exception (Probability, Probability) -> Bool
preciseProb p (Success (l, u)) | l == u && l == p = True
preciseProb _ _                                   = False

nonGround :: String -> Int -> Int -> Exceptional Exception a -> Bool
nonGround expLabel expN expNPreds (Exception (Main.GrounderException (Grounder.NonGroundPreds prds (AST.PredicateLabel label) n)))
    | label == expLabel && n == expN && length prds == expNPreds = True
nonGround _ _ _ _                                                = False

typeError :: Exceptional Exception a -> Bool
typeError (Exception (Main.GrounderException (Grounder.TypeError _ _))) = True
typeError _                                                             = False

undefinedRf :: String -> Int -> Exceptional Exception a -> Bool
undefinedRf expRf expN  (Exception (Main.GrounderException (Grounder.UndefinedRf rf n)))
    | AST.RFuncLabel expRf == rf && expN == n = True
undefinedRf _ _ _                             = False

undefinedRfVal :: String -> Int -> Exceptional Exception a -> Bool
undefinedRfVal expRf expN  (Exception (Main.GrounderException (Grounder.UndefinedRfValue rf args)))
    | AST.RFuncLabel expRf == rf && expN == length args = True
undefinedRfVal _ _ _                                    = False

rfAsArg :: Exceptional Exception a -> Bool
rfAsArg (Exception (Main.GrounderException Grounder.RandomFuncUsedAsArg)) = True
rfAsArg _ = False
