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
import Control.Monad (unless, forM)
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
        Success x   -> print x
    where
        exeMain' = do
            args <- return ["/tmp/tmp.pclp"]--doIO $ getArgs "/home/smichels/steffen/pclp/test.pclp"
            let firstArg = head args
            src <- doIO $ readFile firstArg
            ast <- returnExceptional $ parsePclp src
            --doIO (putStrLn $ show ast)
            (mbEvidence, nnf) <- return $ groundPclp ast
            exportAsDot "/tmp/nnf.dot" nnf
            inferenceApprox mbEvidence ast nnf

        inferenceApprox mbEvidence ast nnf = do
            let bounds = case mbEvidence of
                    Nothing -> gwmc (getFirst $ AST.queries ast) (AST.rFuncDefs ast) nnf
                    Just ev -> gwmcEvidence (getFirst $ AST.queries ast) ev (AST.rFuncDefs ast) nnf

            startTime <- doIO $ fmap (\x -> (fromIntegral (round (x*1000)::Int)::Double)/1000.0) getPOSIXTime
            doIO $ forM bounds (\(l,u) -> do
                    currentTime <- fmap (\x -> (fromIntegral (round (x*1000)::Int)::Double)/1000.0) getPOSIXTime
                    let appr     = fromRat (u+l)/2::Double
                    let err      = (0.6339446564891053 - appr)^2
                    putStrLn $ printf "%f %f" (currentTime-startTime) appr
                )
            return . (\(l,u) -> (fromRat l::Double,fromRat u::Double)) $ last bounds

        inferenceDebug ast nnf = do
            let results = gwmcDebug (getFirst $ AST.queries ast) (AST.rFuncDefs ast) nnf
            --results <- return $ take 7 results
            startTime <- doIO $ fmap (\x -> (fromIntegral (round (x*1000)::Int)::Double)/1000.0) getPOSIXTime
            doIO $ forM results (\(pst,_) -> do
                    let (l,u)    = PST.bounds pst
                    currentTime <- fmap (\x -> (fromIntegral (round (x*1000)::Int)::Double)/1000.0) getPOSIXTime
                    let appr     = fromRat (u+l)/2::Double
                    let err      = (0.6339446564891053 - appr)^2
                    putStrLn $ printf "%f %f" (currentTime-startTime) err
                )
                --currentTime <- fmap (\x -> round (x*1000)::Int) getPOSIXTime
            --                                    appr <- return $ fromRat (u+l)/2::Float
            --                                    err  <- return (0.4053876623346897 - appr)^2
            --                                    putStrLn $ printf "%i %f" (currentTime-startTime) err
            --                            putStrLn $ printf "%f %f" (fromRat l::Float) (fromRat u::Float))0.4053876623346897
            --                            putStrLn $ printf "%i %f %f %f" (currentTime-startTime) (fromRat l::Float) (fromRat u::Float) (fromRat (u+l)/2::Float))
            --NNF.exportAsDot "/tmp/nnfAfter.dot" $ snd $ last results
            --PST.exportAsDot "/tmp/pst.dot" $ fst $ last results
            --return ()
            return . (\(l,u) -> (fromRat l::Double,fromRat u::Double)) . PST.bounds $ fst $ last results
            --return $ length results

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
