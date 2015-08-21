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
import qualified GWMCExact
import qualified AST
import qualified Data.HashSet as Set
import Benchmarks
import Control.Monad (forM)
import Numeric (fromRat)
import Control.Monad.Exception.Synchronous -- TODO: remove, should be included by Exception
import Data.Time.Clock.POSIX (getPOSIXTime)

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
            args <- return ["/tmp/tmp.pclp"]--doIO $ getArgs "/home/smichels/steffen/pclp/test.pclp"
            let firstArg = args !! 0
            src <- doIO $ readFile firstArg
            ast <- returnExceptional $ parsePclp src
            --doIO (putStrLn $ show ast)
            nnf <- return $ groundPclp ast
           -- exportAsDot "/tmp/nnf.dot" nnf
            inferenceApprox ast nnf

        inferenceApprox ast nnf = do
            results <- return $ gwmcDebug (getFirst $ AST.queries ast) (AST.rFuncDefs ast) nnf
            --results <- return $ take 7 results
            --startTime <- doIO $ fmap (\x -> round (x*1000)::Int) getPOSIXTime
            --doIO $ forM results (\(pst,_) -> let (l,u) = PST.bounds pst
            --                          in do
            --                            currentTime <- fmap (\x -> round (x*1000)::Int) getPOSIXTime
            --                            putStrLn $ printf "%f %f" (fromRat l::Float) (fromRat u::Float))
            --                            putStrLn $ printf "%i %f %f %f" (currentTime-startTime) (fromRat l::Float) (fromRat u::Float) (fromRat (u+l)/2::Float))
            --NNF.exportAsDot "/tmp/nnfAfter.dot" $ snd $ last results
            --PST.exportAsDot "/tmp/pst.dot" $ fst $ last results
            --return . (\(l,u) -> (fromRat l::Double,fromRat u::Double)) . PST.bounds $ fst $ last results
            return $ length results

        inferenceExact ast nnf = do
            (p, nnfAfter) <- return $ GWMCExact.gwmc (getFirst $ AST.queries ast) (AST.rFuncDefs ast) nnf
            return (fromRat p :: Double)

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
