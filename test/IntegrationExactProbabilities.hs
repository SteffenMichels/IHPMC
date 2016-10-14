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

module IntegrationExactProbabilities (tests)
where
import NeatInterpolation
import IntegrationTest
import Data.Text (unpack)

tests :: (String, [IntegrationTest])
tests = ("exact probabilities", [ boolsAnd, boolsOr, boolEq, boolNonEq, stringAnd, stringOr
                                , oneDimReal, oneDimRealAnd, oneDimRealOr
                                ]
        )

boolsAnd :: IntegrationTest
boolsAnd = IntegrationTest
    { label = "boolean distributions (conjunction)"
    , model = unpack $ [text|
                  ~x ~ flip(0.1).
                  ~y ~ flip(0.2).
                  ~z ~ flip(0.3).
                  q1 <- ~x = true.
                  q2 <- q1, ~y = false.
                  q3 <- q2, ~z = true.
              |]
    , expectedResults =
        [ (query "q1", preciseProb 0.1)
        , (query "q2", preciseProb 0.08)
        , (query "q3", preciseProb 0.024)
        ]
    }

boolsOr :: IntegrationTest
boolsOr = IntegrationTest
    { label = "boolean distributions (disjunction)"
    , model = unpack $ [text|
                  ~x ~ flip(0.1).
                  ~y ~ flip(0.2).
                  ~z ~ flip(0.3).
                  q1 <- ~x = true.
                  q2 <- q1.
                  q2 <- ~y = false.
                  q3 <- q2.
                  q3 <- ~z = true.
              |]
    , expectedResults =
        [ (query "q1", preciseProb 0.1)
        , (query "q2", preciseProb 0.82)
        , (query "q3", preciseProb 0.874)
        ]
    }

boolEq :: IntegrationTest
boolEq = IntegrationTest
    { label = "equality between two boolean probabilistic functions"
    , model = unpack $ [text|
                  ~x ~ flip(0.1).
                  ~y ~ flip(0.2).
                  q <- ~x = ~y.
              |]
    , expectedResults =
        [ (query "q", preciseProb 0.74)
        ]
    }

boolNonEq :: IntegrationTest
boolNonEq = IntegrationTest
    { label = "non-equality between two boolean probabilistic functions"
    , model = unpack $ [text|
                  ~x ~ flip(0.1).
                  ~y ~ flip(0.2).
                  q <- ~x /= ~y.
              |]
    , expectedResults =
        [ (query "q", preciseProb 0.26)
        ]
    }

stringAnd :: IntegrationTest
stringAnd = IntegrationTest
    { label = "string distribution (conjunction)"
    , model = unpack $ [text|
                  ~x ~ {0.1: a, 0.2: b, 0.3: c, 0.4: d}.
                  q1 <- ~x /= a.
                  q2 <- q1, ~x /= b.
                  q3 <- q2, ~x /= c.
                  q4 <- q3, ~x /= d.
              |]
    , expectedResults =
        [ (query "q1", preciseProb 0.9)
        , (query "q2", preciseProb 0.7)
        , (query "q3", preciseProb 0.4)
        , (query "q4", preciseProb 0.0)
        ]
    }

stringOr :: IntegrationTest
stringOr = IntegrationTest
    { label = "string distribution (disjunction)"
    , model = unpack $ [text|
                  ~x ~ {0.1: a, 0.2: b, 0.3: c, 0.4: d}.
                  q1 <- ~x = a.
                  q2 <- q1.
                  q2 <- ~x = b.
                  q3 <- q2.
                  q3 <- ~x = c.
                  q4 <- q3.
                  q4 <- ~x = d.
              |]
    , expectedResults =
        [ (query "q1", preciseProb 0.1)
        , (query "q2", preciseProb 0.3)
        , (query "q3", preciseProb 0.6)
        , (query "q4", preciseProb 1.0)
        ]
    }

oneDimReal :: IntegrationTest
oneDimReal = IntegrationTest
    { label = "one-dimensional predicate on real-valued probabilistic function"
    , model = unpack $ [text|
                  ~x ~ norm(-2.5, 1.33).
                  q1 <- ~x > -2.5.
                  q2 <- ~x >= -2.5.
                  q3 <- ~x < -2.5.
                  q4 <- ~x <= -2.5.
              |]
    , expectedResults =
        [ (query "q1", preciseProb 0.5)
        , (query "q2", preciseProb 0.5)
        ]
    }

oneDimRealAnd :: IntegrationTest
oneDimRealAnd = IntegrationTest
    { label = "conjunction of one-dimensional predicates on real-valued probabilistic function"
    , model = unpack $ [text|
                  ~x ~ norm(-2.5, 1.33).
                  q <- ~x < 1.3, ~x > 1.3.
              |]
    , expectedResults =
        [ (query "q", preciseProb 0.0)
        ]
    }

oneDimRealOr :: IntegrationTest
oneDimRealOr = IntegrationTest
    { label = "disjunction of one-dimensional predicates on real-valued probabilistic function"
    , model = unpack $ [text|
                  ~x ~ norm(-2.5, 1.33).
                  q <- ~x < 1.3.
                  q <- ~x > 1.3.
              |]
    , expectedResults =
        [ (query "q", preciseProb 1.0)
        ]
    }
