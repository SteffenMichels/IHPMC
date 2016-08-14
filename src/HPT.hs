--The MIT License (MIT)
--
--Copyright (c) 2016 Steffen Michels (mail@steffen-michels.de)
--
--Permission is hereby granted, free of charge, to any person obtaining a copy of
--this software and associated documentation files (the "Software"), to deal in
--the Software without restriction, including without limitation the rights to use,
--copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the
--Software, and to permit persons to whom the Software is furnished to do so,
--subject to the following conditions:
--
--The above copyright notice and this permission notice shall be included in all
--copies or substantial portions of the Software.
--
--THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
--IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
--FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
--COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
--IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
--CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

module HPT
    ( HPT(..)
    , HPTNode(..)
    , initialNode
    , bounds
    , score
    , maxError
    , exportAsDot
    ) where
import BasicTypes
import qualified Formula
import Exception
import System.IO
import Text.Printf (printf)
import Control.Monad (foldM)
import Numeric (fromRat)
import GHC.Generics (Generic)
import Data.Hashable (Hashable)

-- Hybrid Probability Tree
data HPT     = Unfinished HPTNode ProbabilityBounds Double
             | Finished Probability
             deriving (Show, Eq, Generic)
instance Hashable HPT
data HPTNode = Leaf Formula.NodeRef
             | ChoiceBool Formula.PropRFunc Probability HPT HPT
             | ChoiceReal Formula.PropRFunc Probability Rational HPT HPT
             | Decomposition Formula.NodeType [HPT]
             deriving (Show, Eq, Generic)
instance Hashable HPTNode

initialNode :: Formula.NodeRef -> HPTNode
initialNode = Leaf

bounds :: HPT -> ProbabilityBounds
bounds (Unfinished _ b _) = b
bounds (Finished p)       = ProbabilityBounds p p

score :: HPT -> Double
score (Unfinished _ _ s) = s
score _                  = 0.0

maxError :: HPT -> Probability
maxError (Unfinished _ (ProbabilityBounds l u) _) = u-l
maxError _                                        = 0.0

exportAsDot :: FilePath -> HPT -> ExceptionalT String IO ()
exportAsDot path hpt = do
    file <- doIO (openFile path WriteMode)
    doIO (hPutStrLn file "digraph Formula {")
    _ <- printNode Nothing Nothing hpt 0 file
    doIO (hPutStrLn file "}")
    doIO (hClose file)
    where
    printNode :: Maybe String -> Maybe String-> HPT -> Int -> Handle -> ExceptionalT String IO Int
    printNode mbParent mbEdgeLabel hpt' counter file = case hpt' of
        Finished prob -> do
            doIO (hPutStrLn file $ printf "%i[label=\"%f\"];" counter (probToDouble prob))
            printEdge mbParent (show counter) mbEdgeLabel
            return (counter+1)
        Unfinished (ChoiceBool rf  prob left right) _ scr -> do
            doIO (hPutStrLn file $ printf "%i[label=\"%s\n(%f)\"];" counter (printBounds hpt') scr)
            printEdge mbParent (show counter) mbEdgeLabel
            counter' <- printNode (Just $ show counter) (Just $ printf "%f: %s=true" (probToDouble prob) (show rf)) left (counter+1) file
            printNode (Just $ show counter) (Just $ printf "%f: %s=false" (probToDouble (1-prob)) (show rf)) right counter' file
        Unfinished (ChoiceReal rf prob splitPoint left right) _ scr -> do
            doIO (hPutStrLn file $ printf "%i[label=\"%s\n(%f)\"];" counter (printBounds hpt') scr)
            printEdge mbParent (show counter) mbEdgeLabel
            counter' <- printNode (Just $ show counter) (Just $ printf "%f: %s<%f" (probToDouble prob) (show rf) (fromRat splitPoint::Float)) left (counter+1) file
            printNode (Just $ show counter) (Just $ printf "%f: %s>%f" (probToDouble (1-prob)) (show rf) (fromRat splitPoint::Float)) right counter' file
        Unfinished (Decomposition op psts) _ scr -> do
            doIO (hPutStrLn file $ printf "%i[label=\"%s\\n%s\n(%f)\"];" counter (show op) (printBounds hpt') scr)
            printEdge mbParent (show counter) mbEdgeLabel
            foldM (\counter' child -> printNode (Just $ show counter) Nothing child counter' file) (counter+1) psts
        Unfinished (Leaf label) _ scr -> do
            doIO (hPutStrLn file $ printf "%i[label=\"%s\n(%f)\"];" counter (nodeRefToReadableString label) scr)
            printEdge mbParent (show counter) mbEdgeLabel
            return (counter+1)
        where
        printEdge mbParent' current mbEdgeLabel' = case mbParent' of
            Nothing -> return ()
            Just parent -> doIO (hPutStrLn file (printf "%s->%s%s;" parent current (case mbEdgeLabel' of
                    Nothing -> ""
                    Just el -> printf "[label=\"%s\"]" el
                )))

        printBounds :: HPT -> String
        printBounds pst = let ProbabilityBounds l u = HPT.bounds pst in printf "[%f-%f]" (probToDouble l) (probToDouble u)

        nodeRefToReadableString :: Formula.NodeRef -> String
        nodeRefToReadableString (Formula.RefComposed sign (Formula.ComposedId i)) = printf
            "%s%s\n"
            (if sign then "" else "-")
            (show i)
        nodeRefToReadableString ref = show ref
        {-nodeLabelToReadableString :: Formula.NodeRef -> String
        nodeLabelToReadableString (Formula.RefComposed sign (Formula.ComposedLabel label bConds rConds _)) = printf
                "%s%s\n  |%s"
                label
                (List.intercalate "\n  ," (fmap showCondBool (Map.toList bConds) ++ showCondReal <$> (Map.toList rConds)))
                (if sign then "" else "-")
                where
                    showCondBool (rf, val)   = printf "%s=%s"    rf $ show val
                    showCondReal (rf, (l,u)) = printf "%s in (%s,%s)" rf (show l) (show u)
        nodeLabelToReadableString ref = show ref-}
