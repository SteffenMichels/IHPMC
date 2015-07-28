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
import BasicTypes
import Control.Monad (unless)
import Data.List (stripPrefix)
import System.Exit (exitFailure)
import Test.QuickCheck.All (quickCheckAll)
import System.IO (readFile)
import System.Environment (getArgs)
import Parser
import Grounder
import Exception
import NNF
import qualified PST
import Text.Printf (printf)
import GWMC
import qualified AST
import qualified Data.HashSet as Set
import Benchmarks
import Control.Monad (forM)
import Numeric (fromRat)
import Control.Monad.Exception.Synchronous -- TODO: remove, should be included by Exception

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
            (psts, nnfAfter) <- return $ gwmcPSTs (getFirst $ AST.queries ast) (AST.rFuncDefs ast) nnf
            --doIO $ forM psts (\pst -> let (l,u) = PST.bounds pst in putStrLn $ printf "%f %f" (fromRat l::Float) (fromRat u::Float))
            --exportAsDot "/tmp/nnfAfter.dot" nnfAfter
            --PST.exportAsDot "/tmp/pst.dot" $ last (take 10 psts)
            return (length psts)
            --return (length bounds, head $ reverse bounds)


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
