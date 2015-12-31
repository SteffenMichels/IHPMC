module MainBenchmark where
import BasicTypes
import Control.Monad (unless, forM)
import Data.List (stripPrefix)
import System.Exit (exitFailure)
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
import Control.Exception.Base (evaluate)

main = do
    result <- runExceptionalT exeMain'
    case result of
        Exception e -> putStrLn (printf "\nError: %s" e)
        Success x   -> print x
    where
        exeMain' = do
            src <- doIO $ readFile "/tmp/tmp.pclp"
            ast <- returnExceptional $ parsePclp src
            ((queries, mbEvidence), f) <- return $ groundPclp ast
            doIO $ forM [1000,2000..25000] (\i -> do
                begin <- curTime
                (l,u) <- evaluate $ case mbEvidence of
                        Nothing -> gwmc (getFirst queries) (\j _ -> j >= i) (AST.rFuncDefs ast) f
                        --Just ev -> gwmcEvidence (getFirst queries) (\j _ -> j <= i) ev (AST.rFuncDefs ast) f
                --err <- evaluate $ probToDouble (u-l)/2
                now <- curTime
                putStrLn $ printf "%f %f %f" (now-begin) (probToDouble l) (probToDouble u) )
            return ()

        curTime = fmap (\x -> (fromIntegral (round (x*1000)::Int)::Double)/1000.0) getPOSIXTime
