module MainBenchmark where
import BasicTypes
import Control.Monad (forM)
import Parser
import Grounder
import Exception
import Text.Printf (printf)
import GWMC
import qualified AST
import Control.Monad.Exception.Synchronous -- TODO: remove, should be included by Exception
import Data.Time.Clock.POSIX (getPOSIXTime)
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
            doIO $ forM [1000,2000..10000] (\i -> do
                begin <- curTime
                (l,u) <- evaluate $ case mbEvidence of
                        Nothing -> gwmc         (getFirst queries)    (\j _ -> j >= i) (AST.rFuncDefs ast) f
                        Just ev -> gwmcEvidence (getFirst queries) ev (\j _ -> j >= i) (AST.rFuncDefs ast) f
                --err <- evaluate $ probToDouble (u-l)/2
                now <- curTime
                putStrLn $ printf "%f %f %f" (now-begin) (probToDouble l) (probToDouble u) )
            return ()

        curTime = fmap (\x -> (fromIntegral (round (x*1000)::Int)::Double)/1000.0) getPOSIXTime
