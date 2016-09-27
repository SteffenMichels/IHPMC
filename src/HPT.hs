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

{-# LANGUAGE Strict #-}

module HPT
    ( HPT(..)
    , HPTNode(..)
    , ProbabilityTriple(..)
    , initialNode
    , bounds
    , triple
    , score
    , trueTriple
    , falseTriple
    , unknownTriple
    , outsideEvidenceTriple
    , outsideEvidence
    , exportAsDot
    ) where
import qualified Formula
import Exception
import System.IO
import Text.Printf (printf)
import Numeric (fromRat)
import qualified GroundedAST
import Probability

-- Hybrid Probability Tree
data HPT     = Unfinished HPTNode ProbabilityTriple Double
             | Finished Probability Probability -- true prob, false prob (within evidence)

data HPTNode = Leaf           Formula.NodeRef Formula.NodeRef -- query and evidence
             | WithinEvidence Formula.NodeRef                 -- only query
             | ChoiceBool     GroundedAST.PFunc Probability HPT HPT
             | ChoiceReal     GroundedAST.PFunc Probability Rational HPT HPT

initialNode :: Formula.NodeRef -> Formula.NodeRef -> HPTNode
initialNode = Leaf

-- Nothing if evidence is inconsistent
bounds :: HPT -> Maybe ProbabilityBounds
bounds (Unfinished _ (ProbabilityTriple t f u) _)
    | z > 0.0   = Just $ ProbabilityBounds (t / (z + u)) $ min 1.0 ((t + u) / z)
    | otherwise = Just $ ProbabilityBounds 0.0 1.0
    where
    z = t + f
bounds (Finished t f)
    | z > 0.0   = Just $ ProbabilityBounds p p
    | otherwise = Nothing
    where
    z = t + f
    p = t / (t + f)

triple :: HPT -> ProbabilityTriple
triple (Unfinished _ t _) = t
triple (Finished t f)     = ProbabilityTriple t f 0.0

score :: HPT -> Double
score (Unfinished _ _ s) = s
score _                  = 0.0

outsideEvidence :: HPT
outsideEvidence = HPT.Finished 0.0 0.0

data ProbabilityTriple = ProbabilityTriple Probability Probability Probability -- true prob, false prob (within evidence), unknown prob
instance Show ProbabilityTriple
    where
    show (ProbabilityTriple t f u) = printf "(%s, %s, %s)" (show t) (show f) (show u)


trueTriple :: ProbabilityTriple
trueTriple = HPT.ProbabilityTriple 1.0 0.0 0.0

falseTriple :: ProbabilityTriple
falseTriple = HPT.ProbabilityTriple 0.0 1.0 0.0

unknownTriple :: ProbabilityTriple
unknownTriple = HPT.ProbabilityTriple 0.0 0.0 1.0

outsideEvidenceTriple :: ProbabilityTriple
outsideEvidenceTriple = HPT.ProbabilityTriple 0.0 0.0 0.0

exportAsDot :: FilePath -> HPT -> ExceptionalT IOException IO ()
exportAsDot path hpt = do
    file <- doIO (openFile path WriteMode)
    doIO (hPutStrLn file "digraph Formula {")
    _ <- printNode Nothing Nothing hpt 0 file
    doIO (hPutStrLn file "}")
    doIO (hClose file)
    where
    printNode :: Maybe String -> Maybe String-> HPT -> Int -> Handle -> ExceptionalT IOException IO Int
    printNode mbParent mbEdgeLabel hpt' counter file = case hpt' of
        Finished t f -> do
            doIO (hPutStrLn file $ printf "%i[label=\"%s %s\"];" counter (show t) (show f))
            printEdge mbParent (show counter) mbEdgeLabel
            return (counter+1)
        Unfinished (ChoiceBool pf  prob left right) _ scr -> do
            doIO (hPutStrLn file $ printf "%i[label=\"%s\n%s\n(%f)\"];" counter (printBounds hpt') (show $ triple hpt') scr)
            printEdge mbParent (show counter) mbEdgeLabel
            counter' <- printNode (Just $ show counter) (Just $ printf "%s: %s=true" (show prob) (show pf)) left (counter+1) file
            printNode (Just $ show counter) (Just $ printf "%s: %s=false" (show (1 - prob)) (show pf)) right counter' file
        Unfinished (ChoiceReal pf prob splitPoint left right) _ scr -> do
            doIO (hPutStrLn file $ printf "%i[label=\"%s\n%s\n(%f)\"];" counter (printBounds hpt') (show $ triple hpt') scr)
            printEdge mbParent (show counter) mbEdgeLabel
            counter' <- printNode (Just $ show counter) (Just $ printf "%s: %s<%f" (show prob) (show pf) (fromRat splitPoint::Float)) left (counter+1) file
            printNode (Just $ show counter) (Just $ printf "%s: %s>%f" (show (1 - prob)) (show pf) (fromRat splitPoint::Float)) right counter' file
        Unfinished (Leaf qRef eRef) _ scr -> do
            doIO (hPutStrLn file $ printf "%i[label=\"%s\n||%s\n(%f)\"];" counter (show qRef) (show eRef) scr)
            printEdge mbParent (show counter) mbEdgeLabel
            return (counter+1)
        Unfinished (WithinEvidence qRef) _ scr -> do
            doIO (hPutStrLn file $ printf "%i[label=\"%s\n||T\n(%f)\"];" counter (show qRef) scr)
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
        printBounds pst = case HPT.bounds pst of
            Just (ProbabilityBounds l u) -> printf "[%s-%s]" (show l) (show u)
            Nothing                      -> "inconsistent evidence"

        {-nodeLabelToReadableString :: Formula.NodeRef -> String
        nodeLabelToReadableString (Formula.RefComposed sign (Formula.ComposedLabel label bConds rConds _)) = printf
                "%s%s\n  |%s"
                label
                (List.intercalate "\n  ," (fmap showCondBool (Map.toList bConds) ++ showCondReal <$> (Map.toList rConds)))
                (if sign then "" else "-")
                where
                    showCondBool (pf, val)   = printf "%s=%s"    pf $ show val
                    showCondReal (pf, (l,u)) = printf "%s in (%s,%s)" pf (show l) (show u)
        nodeLabelToReadableString ref = show ref-}
