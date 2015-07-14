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
import Text.Printf (printf)
import GWMC
import qualified AST
import qualified Data.Set as Set
import Benchmarks
import Control.Monad (forM)
import Numeric (fromRat)

-- Tell QuickCheck that if you strip "Hello " from the start of
-- hello s you will be left with s (for any s).
-- prop_hello s = stripPrefix "Hello " (hello s) == Just s

-- Hello World
exeMain = do
    result <- runExceptionalT exeMain'
    case result of
        Exception e -> putStrLn (printf "\nError: %s" e)
        Success x   -> putStrLn $ show x
    where
        exeMain' = do
            args <- return ["/tmp/tmp.pclp"]--doIO $ getArgs
            let firstArg = args !! 0
            src <- doIO (readFile firstArg)
            ast <- returnExceptional (parsePclp src)
            --doIO (putStrLn $ show ast)
            nnf <- return $ groundPclp ast
            --exportAsDot "/tmp/nnf.dot" nnf
            (bounds, nnfAfter) <- return $ gwmc (Set.findMax $ AST.queries ast) (AST.rFuncDefs ast) nnf
            --exportAsDot "/tmp/nnfAfter.dot" nnfAfter
            doIO $ forM (take 100 bounds) (\(l,u) -> putStrLn $ printf "[%f, %f]" (fromRat l::Float) (fromRat u::Float))
            return "success"

-- Entry point for unit tests.
testMain = undefined--do
--    allPass <- $quickCheckAll -- Run QuickCheck on all prop_ functions
--    unless allPass exitFailure

-- This is a clunky, but portable, way to use the same Main module file
-- for both an application and for unit tests.
-- MAIN_FUNCTION is preprocessor macro set to exeMain or testMain.
-- That way we can use the same file for both an application and for tests.
#ifndef MAIN_FUNCTION
#define MAIN_FUNCTION exeMain
#endif
main = MAIN_FUNCTION
