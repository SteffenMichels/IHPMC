module Main where
import BasicTypes
import System.Environment (getArgs)
import Parser
import Grounder
import Exception
import Text.Printf (printf)
import Text.Read (readMaybe)
import GWMC
import qualified AST
import Control.Monad.Exception.Synchronous

main = do
    result <- runExceptionalT exeMain'
    case result of
        Exception e -> putStrLn $ printf "\nError: %s" e
        Success _   -> return ()
    where
        exeMain' = do
            args <- doIO getArgs
            assertT "Wrong number of arguments. Should be: MODELFILE NRITERATIONS" (length args == 2)
            let [modelFile,nIterationsStr] = args
            nIterations <- returnExceptional $ fromMaybe (printf "'%s' is not a valid number!" nIterationsStr) $ readMaybe nIterationsStr
            assertT "There should be at least one iteration." (nIterations > 0)
            src <- doIO $ readFile modelFile
            ast <- returnExceptional $ parsePclp src
            ((queries, mbEvidence), f) <- return $ groundPclp ast $ heuristicsCacheComputations $ AST.rFuncDefs ast
            let (l,u) = gwmc (getFirst queries) (\n (l,u) -> n == nIterations) (AST.rFuncDefs ast) f
            doIO $ putStrLn $ printf "%i iterations..." nIterations
            doIO $ putStrLn $ printf "%s: %f (error bound: %f)" (getFirst $ AST.queries ast) (probToDouble (u+l)/2) (probToDouble (u-l)/2)
