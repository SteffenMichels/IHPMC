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

module MainBenchmark where
import BasicTypes
import Control.Monad (forM)
import Parser
import Grounder
import Exception
import Text.Printf (printf)
import GWMC
import qualified AST
import Control.Monad.Exception.Synchronous -- TODO: remove, should be included by Exception
import Data.Time.Clock.POSIX (getPOSIXTime)
import Control.Exception.Base (evaluate)

main = do
    result <- runExceptionalT exeMain'
    case result of
        Exception e -> putStrLn (printf "\nError: %s" e)
        Success x   -> print x
    where
        exeMain' = do
            src <- doIO $ readFile "/tmp/tmp.pclp"
            ast <- returnExceptional $ parsePclp src
            ((queries, mbEvidence), f) <- return $ groundPclp ast $ heuristicsCacheComputations $ AST.rFuncDefs ast
            doIO $ forM [100,200..1000] (\i -> do
                begin <- curTime
                (l,u) <- evaluate $ case mbEvidence of
                        Nothing -> gwmc         (getFirst queries)    (\j _ -> j >= i) (AST.rFuncDefs ast) f
                        Just ev -> gwmcEvidence (getFirst queries) ev (\j _ -> j >= i) (AST.rFuncDefs ast) f
                --err <- evaluate $ probToDouble (u-l)/2
                now <- curTime
                putStrLn $ printf "%f %f %f" (now-begin) (probToDouble l) (probToDouble u) )
            return ()

        curTime = (\x -> (fromIntegral (round (x*1000)::Int)::Double)/1000.0) <$> getPOSIXTime
