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

{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE Strict #-}
#endif

module HPT
    ( HPT(..)
    , HPTNode(..)
    , Choice(..)
    , ProbabilityQuadruple(..)
    , initialNode
    , bounds
    , quadruple
    , score
    , trueQuadruple
    , falseQuadruple
    , unknownQuadruple
    , withinEvidenceQuadruple
    , outsideEvidenceQuadruple
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
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Util
import Data.Text (replace, pack, unpack)

-- Hybrid Probability Tree
data HPT     = Unfinished HPTNode ProbabilityQuadruple Double
             | Finished Probability Probability -- true prob, false prob (within evidence)

data HPTNode = Leaf           Formula.NodeRef Formula.NodeRef -- query and evidence
             | WithinEvidence Formula.NodeRef                 -- only query
             | Choice         Choice GroundedAST.PFuncLabel Probability HPT HPT

data Choice = ChoiceBool
            | ChoiceString (HashSet String)
            | ChoiceReal   Rational

initialNode :: Formula.NodeRef -> Formula.NodeRef -> HPTNode
initialNode = Leaf

-- Nothing if evidence is inconsistent
bounds :: HPT -> Maybe ProbabilityBounds
bounds (Unfinished _ (ProbabilityQuadruple t f e u) _) =
    Just $ ProbabilityBounds lo up
    where
    lo = t / (t + f + e + u)
    up | zu > 0.0 = (t + e + u) / zu
       | otherwise  = 1.0
    zu= t + f + e
bounds (Finished t f)
    | z > 0.0   = Just $ ProbabilityBounds p p
    | otherwise = Nothing
    where
    z = t + f
    p = t / (t + f)

quadruple :: HPT -> ProbabilityQuadruple
quadruple (Unfinished _ t _) = t
quadruple (Finished t f)     = ProbabilityQuadruple t f 0.0 0.0

score :: HPT -> Double
score (Unfinished _ _ s) = s
score _                  = 0.0

outsideEvidence :: HPT
outsideEvidence = HPT.Finished 0.0 0.0

data ProbabilityQuadruple = ProbabilityQuadruple Probability Probability Probability Probability-- true prob, false prob (within evidence), within evidence, unknown prob
instance Show ProbabilityQuadruple
    where
    show (ProbabilityQuadruple t f e u) = printf "(%s, %s, %s, %s)" (show t) (show f) (show e) (show u)


trueQuadruple:: ProbabilityQuadruple
trueQuadruple = HPT.ProbabilityQuadruple 1.0 0.0 0.0 0.0

falseQuadruple :: ProbabilityQuadruple
falseQuadruple = HPT.ProbabilityQuadruple 0.0 1.0 0.0 0.0

withinEvidenceQuadruple :: ProbabilityQuadruple
withinEvidenceQuadruple = HPT.ProbabilityQuadruple 0.0 0.0 1.0 0.0

unknownQuadruple :: ProbabilityQuadruple
unknownQuadruple = HPT.ProbabilityQuadruple 0.0 0.0 0.0 1.0

outsideEvidenceQuadruple :: ProbabilityQuadruple
outsideEvidenceQuadruple = HPT.ProbabilityQuadruple 0.0 0.0 0.0 0.0

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
        Unfinished (Choice choice pf prob left right) _ scr -> do
            doIO (hPutStrLn file $ printf "%i[label=\"%s\n%s\n(%f)\"];" counter (printBounds hpt') (show $ quadruple hpt') scr)
            printEdge mbParent (show counter) mbEdgeLabel
            counter' <- printNode (Just $ show counter) (Just $ printf "%s: %s %s" (show prob) (show pf) (printChoiceRight choice)) left (counter+1) file
            printNode (Just $ show counter) (Just $ printf "%s: %s %s" (show (1 - prob)) (show pf) (printChoiceLeft choice)) right counter' file
            where
            printChoiceRight  ChoiceBool                = "= true"
            printChoiceRight (ChoiceString rightBranch) = printf "in {%s}" $ unpack $ replace (pack "\"") (pack "") $ pack $ showLst $ Set.toList rightBranch
            printChoiceRight (ChoiceReal splitPoint)    = printf "< %f" (fromRat splitPoint::Float)
            printChoiceLeft   ChoiceBool                = "= false"
            printChoiceLeft  (ChoiceString rightBranch) = printf "not in {%s}" $ unpack $ replace (pack "\"") (pack "") $ pack $ showLst $ Set.toList rightBranch
            printChoiceLeft  (ChoiceReal splitPoint)    = printf "> %f" (fromRat splitPoint::Float)
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
