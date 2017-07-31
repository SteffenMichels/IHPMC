--The MIT License (MIT)
--
--Copyright (c) 2017 Steffen Michels (mail@steffen-michels.de)
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

module IntegrationPreprocessor (tests)
where
import NeatInterpolation
import IntegrationTest
import Data.Text (unpack)

tests :: (String, [IntegrationTest])
tests = ("AST preprocessor", [ oneArg, twoArgs, twoArgsConsts
                             ]
        )

oneArg :: IntegrationTest
oneArg = IntegrationTest
    { label = "one PF argument"
    , model = unpack $ [text|
                  ~a ~ flip(0.1).
                  ~b ~ flip(0.2).
                  ~c ~ flip(0.3).
                  ~x(_) ~ flip(0.4).

                  q1 <- ~x(~a) = true.
                  q2 <- ~x(~a) = true, ~x(~b) = true.
                  q3 <- ~x(~a) = true, ~x(~b) = true, ~x(~c) = true.
              |]
    , expectedResults =
        [ (query "q1", preciseProb 0.4)
        , (query "q2", preciseProb 0.3376)
        , (query "q3", preciseProb 0.2824)
        ]
    }

twoArgs :: IntegrationTest
twoArgs = IntegrationTest
    { label = "two PF arguments"
    , model = unpack $ [text|
                  ~a ~ flip(0.1).
                  ~b ~ flip(0.2).
                  ~c ~ flip(0.3).
                  ~d ~ flip(0.4).
                  ~e ~ flip(0.5).
                  ~f ~ flip(0.6).
                  ~x(_, _) ~ flip(0.5).

                  q1 <- ~x(~a, ~b) = true.
                  q2 <- ~x(~a, ~b) = true, ~x(~c, ~d) = true.
                  q3 <- ~x(~a, ~b) = true, ~x(~c, ~d) = true, ~x(~e, ~f) = true.
              |]
    , expectedResults =
        [ (query "q1", preciseProb 0.5)
        , (query "q2", preciseProb 0.3424)
        , (query "q3", preciseProb 0.2287)
        ]
    }

twoArgsConsts :: IntegrationTest
twoArgsConsts = IntegrationTest
    { label = "two PF arguments"
    , model = unpack $ [text|
                  ~a ~ flip(0.1).
                  ~b ~ flip(0.2).
                  ~c ~ flip(0.3).
                  ~x(_, _) ~ flip(0.5).

                  q1 <- ~x(~a, 1) = true.
                  q2 <- ~x(~a, 1) = true, ~x(~b, 1) = true.
                  q3 <- ~x(~a, 1) = true, ~x(~b, 1) = true, ~x(~c, 1) = true.
              |]
    , expectedResults =
        [ (query "q1", preciseProb 0.5)
        , (query "q2", preciseProb 0.435)
        , (query "q3", preciseProb 0.3775)
        ]
    }
