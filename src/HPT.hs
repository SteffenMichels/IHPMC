-----------------------------------------------------------------------------
--
-- Module      :  HPT
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
             | ChoiceBool RFuncLabel Probability HPT HPT
             | ChoiceReal RFuncLabel Probability Rational HPT HPT
             | Decomposition Formula.NodeType [HPT]
             deriving (Show, Eq, Generic)
instance Hashable HPTNode

initialNode :: Formula.NodeRef -> HPTNode
initialNode = Leaf

bounds :: HPT -> ProbabilityBounds
bounds (Unfinished _ b _) = b
bounds (Finished p)       = (p, p)

score :: HPT -> Double
score (Unfinished _ _ s) = s
score _                  = 0.0

maxError :: HPT -> Probability
maxError (Unfinished _ (l,u) _) = u-l
maxError _                      = 0.0

exportAsDot :: FilePath -> HPT -> ExceptionalT String IO ()
exportAsDot path pst = do
    file <- doIO (openFile path WriteMode)
    doIO (hPutStrLn file "digraph Formula {")
    printNode Nothing Nothing pst 0 file
    doIO (hPutStrLn file "}")
    doIO (hClose file)
    where
        printNode :: Maybe String -> Maybe String-> HPT -> Int -> Handle -> ExceptionalT String IO Int
        printNode mbParent mbEdgeLabel pst counter file = case pst of
            Finished prob -> do
                doIO (hPutStrLn file $ printf "%i[label=\"%f\"];" counter (probToDouble prob))
                print mbParent (show counter) mbEdgeLabel
                return (counter+1)
            Unfinished (ChoiceBool label prob left right) _ score -> do
                doIO (hPutStrLn file $ printf "%i[label=\"%s\n(%f)\"];" counter (printBounds pst) score)
                print mbParent (show counter) mbEdgeLabel
                counter' <- printNode (Just $ show counter) (Just $ printf "%f: %s=true" (probToDouble prob) label) left (counter+1) file
                printNode (Just $ show counter) (Just $ printf "%f: %s=false" (probToDouble (1-prob)) label) right counter' file
            Unfinished (ChoiceReal label prob splitPoint left right) _ score -> do
                doIO (hPutStrLn file $ printf "%i[label=\"%s\n(%f)\"];" counter (printBounds pst) score)
                print mbParent (show counter) mbEdgeLabel
                counter' <- printNode (Just $ show counter) (Just $ printf "%f: %s<%f" (probToDouble prob) label (fromRat splitPoint::Float)) left (counter+1) file
                printNode (Just $ show counter) (Just $ printf "%f: %s>%f" (probToDouble (1-prob)) label (fromRat splitPoint::Float)) right counter' file
            Unfinished (Decomposition op psts) _ score -> do
                doIO (hPutStrLn file $ printf "%i[label=\"%s\\n%s\n(%f)\"];" counter (show op) (printBounds pst) score)
                print mbParent (show counter) mbEdgeLabel
                foldM (\counter' child -> printNode (Just $ show counter) Nothing child counter' file) (counter+1) psts
            Unfinished (Leaf label) _ score -> do
                doIO (hPutStrLn file $ printf "%i[label=\"%s\n(%f)\"];" counter (nodeRefToReadableString label) score)
                print mbParent (show counter) mbEdgeLabel
                return (counter+1)
            where
                print mbParent current mbEdgeLabel = case mbParent of
                    Nothing -> return ()
                    Just parent -> doIO (hPutStrLn file (printf "%s->%s%s;" parent current (case mbEdgeLabel of
                            Nothing -> ""
                            Just el -> printf "[label=\"%s\"]" el
                        )))

                printBounds :: HPT -> String
                printBounds pst = let (l,u) = HPT.bounds pst in printf "[%f-%f]" (probToDouble l) (probToDouble u)

                nodeRefToReadableString :: Formula.NodeRef -> String
                nodeRefToReadableString (Formula.RefComposed sign id) = printf
                        "%s%s\n"
                        (if sign then "" else "-")
                        (show id)
                        where
                            showCondBool (rf, val)   = printf "%s=%s"    rf $ show val
                            showCondReal (rf, (l,u)) = printf "%s in (%s,%s)" rf (show l) (show u)
                nodeRefToReadableString ref = show ref
                {-nodeLabelToReadableString :: Formula.NodeRef -> String
                nodeLabelToReadableString (Formula.RefComposed sign (Formula.ComposedLabel label bConds rConds _)) = printf
                        "%s%s\n  |%s"
                        label
                        (List.intercalate "\n  ," (fmap showCondBool (Map.toList bConds) ++ fmap showCondReal (Map.toList rConds)))
                        (if sign then "" else "-")
                        where
                            showCondBool (rf, val)   = printf "%s=%s"    rf $ show val
                            showCondReal (rf, (l,u)) = printf "%s in (%s,%s)" rf (show l) (show u)
                nodeLabelToReadableString ref = show ref-}

