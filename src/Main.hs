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

module Main where
import BasicTypes
import System.Environment (getArgs)
import Parser
import Grounder
import Exception
import Text.Printf (printf, PrintfArg)
import IHPMC
import qualified AST
import Options (Options(..))
import qualified Options
import Control.Monad.Exception.Synchronous
import Control.Monad (forM_)
import System.Exit (exitFailure)
import Data.Maybe (isJust)

main :: IO ()
main = do
    result <- runExceptionalT exeMain'
    case result of
        Exception e -> putStrLn (printf "\nError: %s" e) >> exitFailure
        Success _   -> return ()
    where
    exeMain' = do
        args <- doIO getArgs
        Options{modelFile, nIterations, errBound, timeout, repInterval} <- Options.parseConsoleArgs args
        assertT
            "Error bound should be between 0.0 and 0.5."
            (case errBound of
                Nothing -> True
                Just b  -> b >= 0.0 && b <= 0.5
            )
        assertT
            "You should specify at least one stop condition."
            (isJust nIterations || isJust errBound || isJust timeout)
        printIfSet "Stopping after %i iterations." nIterations
        printIfSet "Stopping if error bound is at most %f." $ probToDouble <$> errBound
        printIfSet "Stopping after %ims." timeout
        src <- doIO $ readFile modelFile
        ast <- returnExceptional $ parsePclp src
        ((queries, mbEvidence), f) <- return $ groundPclp ast $ heuristicsCacheComputations $ AST.rFuncDefs ast
        let stopPred n (ProbabilityBounds l u) t =  maybe False (== n)       nIterations
                                                 || maybe False (>= (u-l)/2) errBound
                                                 || maybe False (<= t)       timeout
        results <- case mbEvidence of
            Nothing -> ihpmc         (getFirst queries)    stopPred repInterval (AST.rFuncDefs ast) f
            Just ev -> ihpmcEvidence (getFirst queries) ev stopPred repInterval (AST.rFuncDefs ast) f
        forM_
            results
            (\(i, ProbabilityBounds l u) -> doIO $ putStrLn $ printf "iteration %i: %f (error bound: %f)" i (probToDouble (u+l)/2.0) (probToDouble (u-l)/2))

printIfSet :: PrintfArg a => String -> Maybe a -> ExceptionalT String IO ()
printIfSet fstr = maybe (return ()) $ doIO . putStrLn . printf fstr
