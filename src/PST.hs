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
    , PSTNode(..)
    , initialNode
    , bounds
    , score
    , maxError
    , exportAsDot
    ) where
import BasicTypes
import qualified NNF
import qualified AST
import BasicTypes
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import qualified Data.HashMap.Lazy as Map
import Exception
import System.IO
import Text.Printf (printf)
import Control.Monad (foldM)
import Numeric (fromRat)
import GHC.Generics (Generic)
import Data.Hashable (Hashable)
import qualified Data.List as List

-- Probabilistic Sematic Tree
data PST     = Unfinished PSTNode ProbabilityBounds Double
             | Finished Probability
             deriving (Show, Eq, Generic)
instance Hashable PST
data PSTNode = Leaf NNF.NodeRef
             | ChoiceBool RFuncLabel Probability PST PST
             | ChoiceReal RFuncLabel Probability Rational PST PST
             | Decomposition NNF.NodeType [PST]
             deriving (Show, Eq, Generic)
instance Hashable PSTNode

initialNode :: NNF.NodeRef -> PSTNode
initialNode query = Leaf query

bounds :: PST -> ProbabilityBounds
bounds (Unfinished _ b _) = b
bounds (Finished p)       = (p, p)

score :: PST -> Double
score (Unfinished _ _ s) = s
score _                  = 0.0

maxError :: PST -> Probability
maxError (Unfinished _ (l,u) _) = u-l
maxError _                      = 0.0

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
            Finished prob -> do
                doIO (hPutStrLn file $ printf "%i[label=\"%f\"];" counter (fromRat prob::Float))
                print mbParent (show counter) mbEdgeLabel
                return (counter+1)
            Unfinished (ChoiceBool label prob left right) _ score -> do
                doIO (hPutStrLn file $ printf "%i[label=\"%s\n(%f)\"];" counter (printBounds pst) score)
                print mbParent (show counter) mbEdgeLabel
                counter' <- printNode (Just $ show counter) (Just $ printf "%f: %s=true" (fromRat prob::Float) label) left (counter+1) file
                printNode (Just $ show counter) (Just $ printf "%f: %s=false" (fromRat (1-prob)::Float) label) right counter' file
            Unfinished (ChoiceReal label prob splitPoint left right) _ score -> do
                doIO (hPutStrLn file $ printf "%i[label=\"%s\n(%f)\"];" counter (printBounds pst) score)
                print mbParent (show counter) mbEdgeLabel
                counter' <- printNode (Just $ show counter) (Just $ printf "%f: %s<%f" (fromRat prob::Float) label (fromRat splitPoint::Float)) left (counter+1) file
                printNode (Just $ show counter) (Just $ printf "%f: %s>%f" (fromRat (1-prob)::Float) label (fromRat splitPoint::Float)) right counter' file
            Unfinished (Decomposition op psts) _ score -> do
                doIO (hPutStrLn file $ printf "%i[label=\"%s\\n%s\n(%f)\"];" counter (show op) (printBounds pst) score)
                print mbParent (show counter) mbEdgeLabel
                foldM (\counter' child -> printNode (Just $ show counter) Nothing child counter' file) (counter+1) psts
            Unfinished (Leaf label) _ score -> do
                doIO (hPutStrLn file $ printf "%i[label=\"%s\n(%f)\"];" counter (nodeLabelToReadableString label) score)
                print mbParent (show counter) mbEdgeLabel
                return (counter+1)
            where
                print mbParent current mbEdgeLabel = case mbParent of
                    Nothing -> return ()
                    Just parent -> doIO (hPutStrLn file (printf "%s->%s%s;" parent current (case mbEdgeLabel of
                            Nothing -> ""
                            Just el -> printf "[label=\"%s\"]" el
                        )))

                printBounds :: PST -> String
                printBounds pst = let (l,u) = PST.bounds pst in printf "[%f-%f]" (fromRat l::Float) (fromRat u::Float)

                nodeLabelToReadableString :: NNF.NodeRef -> String
                nodeLabelToReadableString (NNF.RefComposed sign (NNF.ComposedLabel label bConds rConds _)) = printf
                        "%s%s\n  |%s"
                        label
                        (List.intercalate "\n  ," ((fmap showCondBool $ Map.toList bConds) ++ (fmap showCondReal $ Map.toList rConds)))
                        (if sign then "" else "-")
                        where
                            showCondBool (rf, val)   = printf "%s=%s"    rf $ show val
                            showCondReal (rf, (l,u)) = printf "%s in (%s,%s)" rf (show l) (show u)
                nodeLabelToReadableString ref = show ref

