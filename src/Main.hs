{-# LANGUAGE CPP, TemplateHaskell #-}
-----------------------------------------------------------------------------
--
-- Module      :  Main
-- Copyright   :
-- License     :  AllRightsReserved
--
-- Maintainer  :
-- Stability   :
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

module Main where
import Control.Monad (unless)
import Data.List (stripPrefix)
import System.Exit (exitFailure)
import Test.QuickCheck.All (quickCheckAll)
import System.IO (readFile)
import System.Environment (getArgs)
import Parser
import Grounder
import Control.Monad.Exception.Synchronous
import Exception
import NNF

-- Tell QuickCheck that if you strip "Hello " from the start of
-- hello s you will be left with s (for any s).
-- prop_hello s = stripPrefix "Hello " (hello s) == Just s

-- Hello World
exeMain = do
    result <- runExceptionalT exeMain'
    case result of
        Exception e -> putStrLn ("\nError: " ++ e)
        Success x   -> putStrLn $ show x
    where
        exeMain' = do
            args <- return ["test.pclp"]--doIO $ getArgs
            let firstArg = args !! 0
            src <- doIO (readFile firstArg)
            ast <- returnExceptional (parsePclp src)
            doIO (putStrLn $ show ast)
            nnf <- return $ groundPclp ast
            exportAsDot "/tmp/nnf.dot" nnf
            return "success"

-- Entry point for unit tests.
testMain = do
    allPass <- $quickCheckAll -- Run QuickCheck on all prop_ functions
    unless allPass exitFailure

-- This is a clunky, but portable, way to use the same Main module file
-- for both an application and for unit tests.
-- MAIN_FUNCTION is preprocessor macro set to exeMain or testMain.
-- That way we can use the same file for both an application and for tests.
#ifndef MAIN_FUNCTION
#define MAIN_FUNCTION exeMain
#endif
main = MAIN_FUNCTION
