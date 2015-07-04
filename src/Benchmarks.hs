-----------------------------------------------------------------------------
--
-- Module      :  Benchmarks
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

module Benchmarks where
import AST (AST)
import qualified AST as AST
import System.IO
import qualified Data.Set as Set
import qualified Data.Map as Map
import Text.Printf (printf)

exe = writeBenchmark $ growingAnd 25

growingAnd :: Int -> AST
growingAnd n = AST.AST { AST.rFuncDefs = Map.empty
                       , AST.rules     = rules
                       , AST.queries   = Set.singleton "a0"
                       }
    where
        rules = foldr rule Map.empty [0..n-1]
        rule i rules = Map.insert
            (printf "a%i" i)
            (Set.singleton $ AST.RuleBody (equality:fmap bodyEl [i+1..n-1]))
            rules
            where
                equality = AST.BuildInPredicate $ AST.BoolEq (AST.UserRFunc (printf "x%i" i)) (AST.BoolConstant True)
        bodyEl i = AST.UserPredicate (printf "a%i" i)

writeBenchmark :: AST -> IO ()
writeBenchmark ast = do
    file <- openFile "/tmp/tmp.pclp" WriteMode
    hPutStr file $ show ast
    hClose file
