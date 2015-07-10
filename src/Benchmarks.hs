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
import Data.List (intercalate)
import Numeric (fromRat)

exe = do
    writeBenchmark show "/tmp/tmp.pclp" $ growingAnd n
    writeBenchmark toProblogSource "/tmp/tmp.pl" $ growingAnd n
        where
            n = 200

writeBenchmark :: (AST -> String) -> FilePath -> AST -> IO ()
writeBenchmark printFunc path ast = do
    file <- openFile path WriteMode
    hPutStr file $ printFunc ast
    hClose file

-- Problog
toProblogSource :: AST -> String
toProblogSource  ast = rfuncDefsStr ++ rulesStr ++ queryStr where
    rfuncDefsStr =  concat [printf "%f :: %s.\n" (fromRat p::Float) label | (label, [AST.Flip p]) <- Map.toList $ AST.rFuncDefs ast]
    rulesStr     = concat $ concat [[printf "%s :- %s.\n" label $ toProblogSourceBody body | body <- Set.toList bodies] | (label,bodies) <- Map.toList $ AST.rules ast]
    queryStr     = concat [printf "query(%s).\n" query | query <- Set.toList $ AST.queries ast]

toProblogSourceBody :: AST.RuleBody -> String
toProblogSourceBody (AST.RuleBody elements) = intercalate ", " (fmap toProblogSourceBodyElement elements)

toProblogSourceBodyElement :: AST.RuleBodyElement -> String
toProblogSourceBodyElement (AST.UserPredicate label)   = label
toProblogSourceBodyElement (AST.BuildInPredicate (AST.BoolEq (AST.UserRFunc label) (AST.BoolConstant True))) = label
toProblogSourceBodyElement _ = error "not supported to Problog printing"

-- Benchmarks
growingAnd :: Int -> AST
growingAnd n = AST.AST { AST.rFuncDefs = rFuncDefs
                       , AST.rules     = rules
                       , AST.queries   = Set.singleton "a0"
                       }
    where
        rFuncDefs = foldr rFuncDef Map.empty [0..n-1]
        rFuncDef i defs = Map.insert (printf "x%i" i) [AST.Flip 0.5] defs

        rules = foldr rule Map.empty [0..n-1]
        rule i rules = Map.insert
            (printf "a%i" i)
            (Set.singleton $ AST.RuleBody (equality:fmap bodyEl [i+1..n-1]))
            rules
            where
                equality = AST.BuildInPredicate $ AST.BoolEq (AST.UserRFunc (printf "x%i" i)) (AST.BoolConstant True)
        bodyEl i = AST.UserPredicate (printf "a%i" i)
