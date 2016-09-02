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
import qualified Data.HashMap.Strict as Map
import Data.Text (unpack)

tests :: (String, [IntegrationTest])
tests = ("grounding", [ IntegrationTest { label = "variables in expressions"
                                        , model = varsInExprSrc
                                        , expectedResults = Map.fromList
                                            [ ("varsInExpr(abc,abc)", 1.0)
                                            , ("varsInExpr(ab,ab)",   0.0)
                                            , ("varsInExpr(abc,ab)",  0.0)
                                            ]
                                        }
                      , IntegrationTest { label = "count"
                                        , model = countSrc
                                        , expectedResults = Map.fromList
                                            [ ("count(1)",  0.6513215599)
                                            , ("count(6)",  0.40951)
                                            , ("count(10)", 0.1)
                                            ]
                                        }
                      ]
        )

varsInExprSrc :: String
varsInExprSrc = unpack $
    [text|
        varsInExpr(X, Y) <- Y = X, X = abc.

        query varsInExpr(abc, abc).
        query varsInExpr(ab,  ab).
        query varsInExpr(abc, ab).
    |]

countSrc :: String
countSrc = unpack $
    [text|
        ~count(X) ~ flip(0.1).
        count(X) <- ~count(X) = true.
        count(X) <- X < 10, Y = X + 1, count(Y).

        query count(1).
        query count(6).
        query count(10).
    |]
