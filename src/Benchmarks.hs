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
import qualified AST
import System.IO
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as Map
import Text.Printf (printf)
import Data.List (intercalate)
import Numeric (fromRat)
import BasicTypes

exe = do
    writeBenchmark show "/tmp/tmp.pclp" $ bench n
    writeBenchmark toProblogSource "/tmp/tmp.pl" $ bench n
        where
            n = 4
            bench = paths

writeBenchmark :: (AST -> String) -> FilePath -> AST -> IO ()
writeBenchmark printFunc path ast = do
    file <- openFile path WriteMode
    hPutStr file $ printFunc ast
    hClose file

-- Problog
toProblogSource :: AST -> String
toProblogSource  ast = rfuncDefsStr ++ rulesStr ++ queryStr where
    rfuncDefsStr = concat [printf "%f :: %s.\n" (probToDouble p) label | (label, [AST.Flip p]) <- Map.toList $ AST.rFuncDefs ast]
    rulesStr     = concat $ concat [[printf "%s :- %s.\n" label $ toProblogSourceBody body | body <- Set.toList bodies] | (label,bodies) <- Map.toList $ AST.rules ast]
    queryStr     = concat [printf "query(%s).\n" query | query <- Set.toList $ AST.queries ast]

toProblogSourceBody :: AST.RuleBody -> String
toProblogSourceBody (AST.RuleBody elements) = intercalate ", " (fmap toProblogSourceBodyElement elements)

toProblogSourceBodyElement :: AST.RuleBodyElement -> String
toProblogSourceBodyElement (AST.UserPredicate label)   = label
toProblogSourceBodyElement (AST.BuildInPredicate (AST.BoolEq True (AST.UserRFunc label) (AST.BoolConstant True))) = label
toProblogSourceBodyElement _ = error "not supported to Problog printing"

-- Benchmarks
growingAnd :: Int -> AST
growingAnd n = AST.AST { AST.rFuncDefs = rFuncDefs
                       , AST.rules     = rules
                       , AST.queries   = Set.singleton "a0"
                       , AST.evidence  = Nothing
                       }
    where
        rFuncDefs = foldr rFuncDef Map.empty [0..n-1]
        rFuncDef i = Map.insert (printf "x%i" i) [AST.Flip 0.5]

        rules = foldr rule Map.empty [0..n-1]
        rule i = Map.insert
            (printf "a%i" i)
            (Set.singleton $ AST.RuleBody (equality:fmap bodyEl [i+1..n-1]))
            where
                equality = AST.BuildInPredicate $ AST.BoolEq True (AST.UserRFunc (printf "x%i" i)) (AST.BoolConstant True)
        bodyEl i = AST.UserPredicate (printf "a%i" i)

paths :: Int -> AST
paths n = AST.AST { AST.rFuncDefs = rFuncDefs
                  , AST.rules     = rules
                  , AST.queries   = Set.singleton "reachable"
                  , AST.evidence  = Nothing
                  }
    where
        rFuncDefs = foldr rFuncDef Map.empty [(x,y) | x <- [0..n-1], y <- [0..n-1]]
        rFuncDef (x, y) defs = defs'' where
            defs'  = if x < n-1 then def (x+1) y defs else defs
            defs'' = if y < n-1 then def x (y+1) defs' else defs'
            def dx dy = Map.insert (printConnection ((x, y), (dx, dy))) [AST.Flip $ prob dx]
            prob x = case x of
                0 -> 0.1
                1 -> 0.9
                2 -> 0.2
                3 -> 0.8
                4 -> 0.5
        rules = Map.singleton "reachable" bodies
        bodies = Set.foldr body Set.empty $ paths undefined (0,0) Set.empty Set.empty
        body path = Set.insert
            (AST.RuleBody [bodyEl connection | connection <- Set.toList path])
        bodyEl con = AST.BuildInPredicate $ AST.BoolEq True (AST.UserRFunc $ printConnection con) (AST.BoolConstant True)

        printConnection ((x0, y0), (x1, y1))
            | x0 < x1 || y0 < y1 = print x0 y0 x1 y1
            | otherwise          = print x1 y1 x0 y0
            where
                print = printf "x%ix%ito%ix%i"

        paths :: (Int, Int) -> (Int, Int) -> HashSet (Int,Int) -> HashSet ((Int, Int), (Int, Int)) -> HashSet (HashSet ((Int, Int), (Int, Int)))
        paths last cur@(x,y) visited path
            | x == n-1 && y == n-1               = Set.singleton extendedPath
            | x < 0 || y < 0 || x >= n || y >= n = Set.empty
            | Set.member cur visited             = Set.empty
            | otherwise = foldr
                (\newCur result -> Set.union result $ paths cur newCur extendedVisited extendedPath)
                Set.empty
                [(x-1,y),(x,y-1),(x+1,y),(x,y+1)]
            where
                extendedPath
                    | cur == (0,0) = path
                    | otherwise    = Set.insert (last, cur) path
                extendedVisited = Set.insert cur visited

