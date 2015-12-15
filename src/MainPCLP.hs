module MainPCLP where
import BasicTypes
import Control.Monad (unless, forM)
import Data.List (stripPrefix)
import System.Exit (exitFailure)
--import Test.QuickCheck.All (quickCheckAll)
import System.IO (readFile)
import System.Environment (getArgs)
import Parser
import Grounder
import Exception
import Formula
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
import Control.Arrow ((***))

-- Tell QuickCheck that if you strip "Hello " from the start of
-- hello s you will be left with s (for any s).
-- prop_hello s = stripPrefix "Hello " (hello s) == Just s

-- Hello World
main = do
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
            ((queries, mbEvidence), f) <- return $ groundPclp ast
            --exportAsDot "/tmp/Formula.dot" Formula
            inferenceApprox queries mbEvidence ast f

        inferenceApprox queries mbEvidence ast f = do
            let bounds = case mbEvidence of
                    Nothing -> gwmc (getFirst queries) (AST.rFuncDefs ast) f
                    Just ev -> gwmcEvidence (getFirst queries) ev (AST.rFuncDefs ast) f

            startTime <- doIO $ fmap (\x -> (fromIntegral (round (x*1000)::Int)::Double)/1000.0) getPOSIXTime
            {-doIO $ forM bounds (\(l,u) -> do
                    currentTime <- fmap (\x -> (fromIntegral (round (x*1000)::Int)::Double)/1000.0) getPOSIXTime
                    let appr     = probToDouble (u+l)/2
                    let err      = (0.40522773712567817 - appr)^2
                    putStrLn $ printf "%f %f" (currentTime-startTime) ((u-l)/2)
                )-}
            --return $ last $ take 5000000 bounds
            return . (probToDouble *** probToDouble) $ last bounds

        inferenceDebug queries Nothing ast f = do
            let results = gwmcDebug (getFirst queries) (AST.rFuncDefs ast) f
            results <- return $ take 2000 results
            startTime <- doIO $ fmap (\x -> (fromIntegral (round (x*1000)::Int)::Double)/1000.0) getPOSIXTime
            --currentTime <- fmap (\x -> round (x*1000)::Int) getPOSIXTime
            --                                    appr <- return $ fromRat (u+l)/2::Float
            --                                    err  <- return (0.4053876623346897 - appr)^2
            --                                    putStrLn $ printf "%i %f" (currentTime-startTime) err
                                        --putStrLn $ printf "%f %f" (fromRat l::Float) (fromRat u::Float)
            --                            putStrLn $ printf "%i %f %f %f" (currentTime-startTime) (fromRat l::Float) (fromRat u::Float) (fromRat (u+l)/2::Float))
            ----Formula.exportAsDot "/tmp/FormulaAfter.dot" $ snd $ last results
            --PST.exportAsDot "/tmp/pst.dot" $ fst $ last results
            --return ()
            return . (probToDouble *** probToDouble) . PST.bounds $ fst $ last results
            --return $ length results

        inferenceExact ast f = do
            (p, _) <- return $ GWMCExact.gwmc (getFirst $ AST.queries ast) (AST.rFuncDefs ast) f
            return (probToDouble p)

-- Entry point for unit tests.
testMain = undefined--do
--    allPass <- $quickCheckAll -- Run QuickCheck on all prop_ functions
--    unless allPass exitFailure

-- This is a clunky, but portable, way to use the same Main module file
-- for both an application and for unit tests.
-- MAIN_FUNCTION is preprocessor macro set to exeMain or testMain.
-- That wa y we can use the same file for both an application and for tests.
-- #ifndef MAIN_FUNCTION
-- #define MAIN_FUNCTION exeMain
-- #endif
--main = MAIN_FUNCTION