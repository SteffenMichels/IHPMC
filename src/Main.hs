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

{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE Strict #-}
#endif

module Main (main, Exception(..)) where
import System.Environment (getArgs)
import qualified Parser
import qualified Grounder
import qualified FormulaConverter
import Exception
import Text.Printf (printf, PrintfArg)
import qualified IHPMC
import Options (Options(..))
import qualified Options
import Control.Monad.Exception.Synchronous
import Control.Monad (forM_, when)
import System.Exit (exitFailure)
import Data.Maybe (isJust)
import qualified Formula
import Probability
import qualified HPT

data Exception = GrounderException        Grounder.Exception
               | ParameterException       String
               | CommandLineArgsException String
               | ParserException          Parser.Exception
               | IOException              IOException
               | TestException            String

instance Show Exception
    where
    show (GrounderException e)        = printf "Invalid model: %s" $ show e
    show (ParameterException e)       = printf "Invalid parameter: %s" e
    show (CommandLineArgsException e) = e
    show (ParserException e)          = printf "Invalid model syntax: %s" $ show e
    show (IOException e)              = show e
    show (TestException e)            = printf "Invalid test: %s" e

main :: IO ()
main = do
    result <- runExceptionalT main'
    case result of
        Exception e -> print e >> exitFailure
        Success _   -> return ()

main' :: ExceptionalT Exception IO ()
main' = do
    args <- doIOException getArgs
    Options{modelFile, nIterations, errBound, timeout, repInterval, formExpPath, hptExpPath} <-
        mapExceptionT CommandLineArgsException $ Options.parseConsoleArgs args
    assertT
        (ParameterException "Error bound has to be between 0.0 and 0.5.")
        (case errBound of
            Nothing -> True
            Just b  -> b >= 0.0 && b <= 0.5
        )
    assertT
        (ParameterException "You have to specify at least one stop condition.")
        (isJust nIterations || isJust errBound || isJust timeout)
    printIfSet "Stopping after %i iterations." nIterations
    printIfSet "Stopping if error bound is at most %s." $ show <$> errBound
    printIfSet "Stopping after %ims." timeout
    src <- doIOException $ readFile modelFile
    ast <- returnExceptional $ mapException ParserException $ Parser.parsePclp src
    groundedAst <- returnExceptional $ mapException GrounderException $ Grounder.ground ast
    let ((queries, evidence), f) = FormulaConverter.convert groundedAst IHPMC.heuristicsCacheComputations
    whenJust formExpPath $ \path -> mapExceptionT IOException $ Formula.exportAsDot path f
    let stopPred n (ProbabilityBounds l u) t =  maybe False (<= n)       nIterations
                                             || maybe False (>= (u-l)/2) errBound
                                             || maybe False (<= t)       timeout
    let reportingIO = case repInterval of
            Just rInterv -> \qLabel n bounds t lastRep -> if   t - lastRep >= rInterv
                                                          then Just $ printResult qLabel n t $ Just bounds
                                                          else Nothing
            _            -> \_      _ _      _ _       -> Nothing
    forM_ queries $ \(qLabel, qRef) -> do
        (n, t, mbBounds, hpt) <- mapExceptionT IOException $ IHPMC.ihpmc qRef evidence stopPred (reportingIO qLabel) f
        mapExceptionT IOException $ printResult qLabel n t mbBounds
        when (isJust repInterval) $ doIOException $ putStrLn ""
        whenJust hptExpPath $ \path -> mapExceptionT IOException $ HPT.exportAsDot path hpt
        where
        printResult qLabel n t mbBounds = doIO $ putStrLn $ printf
            "%s (iteration %i, after %ims): %s"
            (show qLabel)
            n
            t
            (case mbBounds of
                Just (ProbabilityBounds l u) -> printf
                    "%s (error bound: %s)"
                    (show $ (u + l) / 2.0)
                    (show $ (u - l) / 2.0)
                Nothing -> "inconsistent evidence"
            )

doIOException :: IO a -> ExceptionalT Exception IO a
doIOException io = mapExceptionT IOException $ doIO io

printIfSet :: PrintfArg a => String -> Maybe a -> ExceptionalT Exception IO ()
printIfSet fstr = maybe (return ()) $ doIOException . putStrLn . printf fstr

whenJust :: Monad m => Maybe a -> (a -> m ()) -> m ()
whenJust Nothing _   = return ()
whenJust (Just x) fx = fx x
