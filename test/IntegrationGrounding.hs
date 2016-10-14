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
import qualified AST

tests :: (String, [IntegrationTest])
tests = ("grounding", [ queries, typesBip, typesArgs, strLits, preds, pfs, varsInExpr, existVars
                      , constraints, count, tablingProp, tablingFO, tablingPrune, network1, network2
                      ]
        )

queries :: IntegrationTest
queries = IntegrationTest
    { label = "queries"
    , model = unpack $ [text|
                  ~x ~ flip(0.1).
                  p(_).
              |]
    , expectedResults =
        [ (queryInt "p" [1], preciseProb 1.0)
        , (AST.UserPredicate (AST.PredicateLabel "p") [AST.Variable (AST.VarName "X")], nonGroundQuery)
        , ( AST.BuildInPredicate
            (AST.Equality False (AST.PFunc (AST.PFuncLabel "x") []) (AST.ConstantExpr (AST.BoolConstant False)))
          , preciseProb 0.1
          )
        , ( AST.BuildInPredicate
            (AST.Equality False (AST.PFunc (AST.PFuncLabel "x") []) (AST.Variable (AST.VarName "X")))
          , nonGroundQuery
          )
        ]
    }

typesBip :: IntegrationTest
typesBip = IntegrationTest
    { label = "type checking (build-in predicates)"
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

typesArgs :: IntegrationTest
typesArgs = IntegrationTest
    { label = "type checking (predicate/random function arguments)"
    , model = unpack $ [text|
                  p(_).
                  argPredOk  <- p(1 + 1).
                  argPredErr <- p(1 + 1.0).

                  ~f(1)   ~ flip(0.1).
                  ~f(1.0) ~ flip(0.2).
                  int  <- ~f(1 + 0) = false.
                  real <- ~f(0.5 + 0.5) = false.
                  err <- ~f(1.0 + 0) = false.
              |]
    , expectedResults =
        [ (query "argPredOk",  preciseProb 1.0)
        , (query "argPredErr", typeError)
        , (query "int",        preciseProb 0.9)
        , (query "real",       preciseProb 0.8)
        , (query "err",        typeError)
        ]
    }

strLits :: IntegrationTest
strLits = IntegrationTest
    { label = "string literals"
    , model = unpack $ [text|
                  ~p("1")         ~ flip(0.1).
                  ~p(1)           ~ flip(0.2).
                  ~p("abc")       ~ flip(0.3).
                  ~p("\"@§$%&^'") ~ flip(0.4).

                  oneStr       <- ~p("1") = true.
                  oneInt       <- ~p(1)   = true.
                  str          <- ~p(abc) = true.
                  strLit       <- ~p("abc") = true.
                  strangeChars <- ~p("\"@§$%&^'") = true.
              |]
    , expectedResults =
        [ (query "oneStr",       preciseProb 0.1)
        , (query "oneInt",       preciseProb 0.2)
        , (query "str",          preciseProb 0.3)
        , (query "strLit",       preciseProb 0.3)
        , (query "strangeChars", preciseProb 0.4)
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
        , (query "e",                undefinedPred "e" 0)
        , (queryStr "two" ["a","a"], preciseProb 0.1)
        , (queryStr "two" ["a","b"], preciseProb 0.02)
        , (queryStr "two" ["a","c"], preciseProb 0.02)
        , (queryStr "two" ["a","d"], preciseProb 0.1)
        , (queryStr "two" ["c","d"], preciseProb 0.02)
        , (queryStr "two" ["e","d"], preciseProb 0.0)
        , (query "err",              pfAsArg)
        ]
    }

pfs :: IntegrationTest
pfs = IntegrationTest
    { label = "probabilistic functions"
    , model = unpack $ [text|
                  ~pf      ~ flip(0.99).
                  ~pf(1)   ~ flip(0.991).
                  ~pf(2)   ~ flip(0.992).
                  ~pf(1,2) ~ flip(0.9912).
                  pf             <- ~pf      = true.
                  pf1            <- ~pf(1)   = true.
                  pf2            <- ~pf(2)   = true.
                  pfErrRfAsArg   <- ~pf(~pf) = true.
                  pfErrNonGround <- ~pf(X)   = true.
                  pfErrUndefined <- ~pf2     = true.
                  pfErrUndefVal  <- ~pf(3)   = true.
                  pfErrUndefVal2 <- ~pf(1,3) = true.
                  pfErrUndefVal3 <- ~pf(3,2) = true.
              |]
    , expectedResults =
        [ (query "pf",             preciseProb 0.99)
        , (query "pf1",            preciseProb 0.991)
        , (query "pf2",            preciseProb 0.992)
        , (query "pfErrRfAsArg",   pfAsArg)
        , (query "pfErrNonGround", nonGround "pfErrNonGround" 0 1)
        , (query "pfErrUndefined", undefinedRf "pf2" 0)
        , (query "pfErrUndefVal",  undefinedRfVal "pf" 1)
        , (query "pfErrUndefVal2", undefinedRfVal "pf" 2)
        , (query "pfErrUndefVal3", undefinedRfVal "pf" 2)
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

constraints :: IntegrationTest
constraints = IntegrationTest
    { label = "constraints"
    , model = unpack $ [text|
                  p(X, X). // p introduces equality constraint
                  easyT        <- p(X + 1, Y + 2), p(Y + 3, Z + 4), X = 1, Y = 0, Z = -1.
                  easyF        <- p(X + 1, Y + 2), p(Y + 3, Z + 4), X = 1, Y = 1, Z = -1.
                  // this should be possible with a better implementation
                  difficult    <- p(X + 1, Y + 2), p(Y + 3, Z + 4), X = 1,        Z = -1.
                  substitution <- p(X, Y), X = 1, Y > 0.

                  typeErr <- p(X, Y), X = 1, Y = 1.0.
              |]
    , expectedResults =
        [ (query "easyT",        preciseProb 1.0)
        , (query "easyF",        preciseProb 0.0)
        , (query "difficult",    unsolvableConstrs)
        , (query "substitution", preciseProb 1.0)
        , (query "typeErr",      typeError)
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

tablingPrune :: IntegrationTest
tablingPrune = IntegrationTest
    { label = "tabling (requires pruning after goal is selected)"
    , model = unpack $ [text|
                  a(a, X) <- b(Y, a), a(Y, b).
                  b(a, a).
              |]
    , expectedResults =
        [ (queryStr "a" ["a", "a"], preciseProb 0.0)
        ]
    }

network1 :: IntegrationTest
network1 = IntegrationTest
    { label = "tabling (network, body element order 1)"
    , model = unpack $ [text|
                  ~e(X, Y) ~ flip(0.1).

                  e(1, 2).
                  e(1, 3).
                  e(2, 4).
                  e(3, 4).
                  e(2, 1).
                  e(3, 1).
                  connected(X, Y) <- ~e(Z, Y) = true, e(Z, Y), connected(X, Z).
                  connected(X, X).
              |]
    , expectedResults =
        [ (queryInt "connected" [1, 4], preciseProb 0.0199)
        ]
    }

network2 :: IntegrationTest
network2 = IntegrationTest
    { label = "tabling (network, body element order 2)"
    , model = unpack $ [text|
                  ~e(X, Y) ~ flip(0.1).

                  e(1, 2).
                  e(1, 3).
                  e(2, 4).
                  e(3, 4).
                  e(2, 1).
                  e(3, 1).
                  connected(X, Y) <- ~e(Z, Y) = true, connected(X, Z), e(Z, Y).
                  connected(X, X).
              |]
    , expectedResults =
        [ (queryInt "connected" [1, 4], preciseProb 0.0199)
        ]
    }
