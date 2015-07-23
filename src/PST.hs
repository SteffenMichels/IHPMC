-----------------------------------------------------------------------------
--
-- Module      :  PST
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

module PST
    ( PST(..)
    , empty
    , bounds
    , maxError
    , exportAsDot
    ) where
import BasicTypes
import qualified NNF
import qualified AST
import BasicTypes
import Data.Set (Set)
import qualified Data.Set as Set
import Exception
import System.IO
import Text.Printf (printf)
import Control.Monad (foldM)
import Numeric (fromRat)

-- Probabilistic Sematic Tree
data PST = Finished Bool
         | Unfinished NNF.NodeLabel
         | Choice RFuncLabel Probability PST PST
         | Decomposition NNF.NodeType (Set PST)
         deriving (Show, Eq, Ord)

empty :: NNF.NodeLabel -> PST
empty query = Unfinished query

bounds :: PST -> ProbabilityBounds
bounds (Finished b)                = if b then (1.0, 1.0) else (0.0, 0.0)
bounds (Unfinished _)              = (0.0, 1.0)
bounds (Choice _ p left right)     = (p*leftLower+(1-p)*rightLower, p*leftUpper+(1-p)*rightUpper) where
    (leftLower,  leftUpper)  = bounds left
    (rightLower, rightUpper) = bounds right
bounds (Decomposition NNF.And dec) = Set.fold (\pst (l,u) -> let (l',u') = bounds pst in (l'*l,u'*u)) (1.0, 1.0) dec
bounds (Decomposition NNF.Or dec)  = (1-nl, 1-nu)
    where
        (nl, nu) = Set.fold (\pst (l,u) -> let (l',u') = bounds pst in (l*(1.0-l'), u*(1.0-u'))) (1.0, 1.0) dec

maxError :: PST -> Probability
maxError pst = let (l,u) = bounds pst in u-l

exportAsDot :: FilePath -> PST -> ExceptionalT String IO ()
exportAsDot path pst = do
    file <- doIO (openFile path WriteMode)
    doIO (hPutStrLn file "digraph NNF {")
    printNode Nothing Nothing pst 0 file
    doIO (hPutStrLn file "}")
    doIO (hClose file)
    where
        printNode :: (Maybe String) -> (Maybe String)-> PST -> Int -> Handle -> ExceptionalT String IO Int
        printNode mbParent mbEdgeLabel pst counter file = case pst of
            Finished val -> do
                doIO (hPutStrLn file $ printf "%i[label=\"%s\\n%s\"];" counter (show val) (printBounds pst))
                print mbParent (show counter) mbEdgeLabel
                return (counter+1)
            Choice label prob left right -> let nodeLabel = label ++ (show $ PST.bounds pst) in do
                doIO (hPutStrLn file $ printf "%i[label=\"%s\"];" counter (printBounds pst))
                print mbParent (show counter) mbEdgeLabel
                counter' <- printNode (Just $ show counter) (Just $ printf "%s=true" label) left (counter+1) file
                printNode (Just $ show counter) (Just $ printf "%s=false" label) right counter' file
            Decomposition op psts -> do
                doIO (hPutStrLn file $ printf "%i[label=\"%s\\n%s\"];" counter (show op) (printBounds pst))
                print mbParent (show counter) mbEdgeLabel
                foldM (\counter' child -> printNode (Just $ show counter) Nothing child counter' file) (counter+1) (Set.toList psts)
            where
                print mbParent current mbEdgeLabel = case mbParent of
                    Nothing -> return ()
                    Just parent -> doIO (hPutStrLn file (printf "%s->%s%s;" parent current (case mbEdgeLabel of
                            Nothing -> ""
                            Just el -> printf "[label=\"%s\"]" el
                        )))

                printBounds :: PST -> String
                printBounds pst = let (l,u) = PST.bounds pst in printf "[%f-%f]" (fromRat l::Float) (fromRat u::Float)
