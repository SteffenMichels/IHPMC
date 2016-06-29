module Main where
import BasicTypes
import System.Environment (getArgs)
import Parser
import Grounder
import Exception
import Text.Printf (printf, PrintfArg)
import GWMC
import qualified AST
import Options (Options(..))
import qualified Options
import Control.Monad.Exception.Synchronous

main = do
    result <- runExceptionalT exeMain'
    case result of
        Exception e -> putStrLn $ printf "\nError: %s" e
        Success _   -> return ()
    where
        exeMain' = do
            args <- doIO getArgs
            Options{modelFile, nIterations, errBound, timeout} <- Options.parseConsoleArgs args
            assertT
                "Error bound should be between 0.0 and 0.5."
                (case errBound of
                    Nothing -> True
                    Just b  -> b >= 0 && b <= 0.5
                )
            printIfSet "Stopping after %i iterations." nIterations
            printIfSet "Stopping if error bound is at most %f." $ probToDouble <$> errBound
            printIfSet "Stopping after %ims." timeout
            src <- doIO $ readFile modelFile
            ast <- returnExceptional $ parsePclp src
            ((queries, mbEvidence), f) <- return $ groundPclp ast $ heuristicsCacheComputations $ AST.rFuncDefs ast
            let stopPred n (l,u) t =  maybe False (== n)       nIterations
                                   || maybe False (>= (u-l)/2) errBound
                                   || maybe False (<= t)       timeout
            (l,u) <- doIO $ gwmc (getFirst queries) stopPred (AST.rFuncDefs ast) f
            doIO $ putStrLn $ printf "%s: %f (error bound: %f)" (getFirst $ AST.queries ast) (probToDouble (u+l)/2) (probToDouble (u-l)/2)

printIfSet :: PrintfArg a => String -> Maybe a -> ExceptionalT String IO ()
printIfSet fstr = maybe (return ()) $ doIO . putStrLn . printf fstr
