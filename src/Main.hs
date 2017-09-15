--The MIT License (MIT)
--
--Copyright (c) 2016-2017 Steffen Michels (mail@steffen-michels.de)
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

module Main (main, Exception(..), exceptionToText) where
import System.Environment (getArgs)
import qualified Parser
import qualified GrounderPhase1
import qualified GrounderPhase2
import qualified KnowledgeBaseConverter as KBConverter
import qualified GroundedAST
import Exception
import qualified IHPMC
import Options (Options(..))
import qualified Options
import Control.Monad.Exception.Synchronous
import Control.Monad (forM_, when)
import Control.Monad.Trans.Class (lift)
import System.Exit (exitFailure)
import Data.Maybe (isJust)
import qualified KnowledgeBase as KB
import Probability
import Data.HashMap (Map)
import qualified Data.HashMap as Map
import qualified IdNrMap
import qualified AST
import TextShow
import qualified Data.Text.Lazy.IO as LTIO
import Data.Monoid ((<>))
import Data.Text (Text)

data Exception = GrounderException        GrounderPhase1.Exception
               | ParameterException       Builder
               | CommandLineArgsException Builder
               | ParserException          Parser.Exception
               | IOException              IOException
               | TestException            Builder

exceptionToText :: Exception -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder
exceptionToText (GrounderException e)        ids2str ids2label = "Invalid model: " <> GrounderPhase1.exceptionToText e ids2str ids2label
exceptionToText (ParameterException e)       _       _         = "Invalid parameter: " <> e
exceptionToText (CommandLineArgsException e) _       _         = e
exceptionToText (ParserException e)          _       _         = "Invalid model syntax: " <> showb e
exceptionToText (IOException e)              _       _         = showb e
exceptionToText (TestException e)            _       _         = "Invalid test: " <> e

main :: IO ()
main = do
    result <- runExceptionalT main'
    case result of
        Exception (e, ids2str, ids2label) -> LTIO.putStrLn (toLazyText $ exceptionToText e ids2str ids2label) >> exitFailure
        Success _                         -> return ()

main' :: ExceptionalT (Exception, Map Int Text, Map Int (Int, [AST.ConstantExpr])) IO ()
main' = do
    args <- doIOException getArgs
    Options{modelFile, nIterations, errBound, timeout, repInterval, formExpPath} <-
        mapExceptionT ((,Map.empty, Map.empty) . CommandLineArgsException) $ Options.parseConsoleArgs args
    assertT
        (ParameterException "Error bound has to be between 0.0 and 0.5.", Map.empty, Map.empty)
        (case errBound of
            Nothing -> True
            Just b  -> b >= 0.0 && b <= 0.5
        )
    assertT
        (ParameterException "You have to specify at least one stop condition.", Map.empty, Map.empty)
        (isJust nIterations || isJust errBound || isJust timeout)
    printIfSet (\n -> "Stopping after " <> showb n <> " iterations.") nIterations
    printIfSet (\e -> "Stopping if error bound is at most " <> showb e <> ".") $ showb <$> errBound
    printIfSet (\t -> "Stopping after " <> showb t <> "ms.") timeout
    src <- doIOException $ readFile modelFile
    (ast, identIds) <- returnExceptional $ mapException ((,Map.empty, Map.empty) . ParserException) $ Parser.parsePclp src
    let ids2str = IdNrMap.fromIdNrMap identIds
    (groundedAst1, labelIds) <- returnExceptional $ mapException ((,ids2str, Map.empty) . GrounderException) $ GrounderPhase1.ground ast
    let ids2label = IdNrMap.fromIdNrMap labelIds
    let groundedAst = GrounderPhase2.substitutePfsWithPfArgs groundedAst1
    mapExceptionT ((,Map.empty, Map.empty) . IOException) $ KB.runKBState IHPMC.heuristicsCacheComputations $ do
        ((queries, evidence), predIds) <- KBConverter.convert groundedAst
        let ids2predlbl = IdNrMap.fromIdNrMap predIds
        whenJust formExpPath $ \path -> KB.exportAsDot path ids2str ids2label ids2predlbl
        let stopPred n (ProbabilityBounds l u) t =  maybe False (<= n)       nIterations
                                                 || maybe False (>= (u-l)/2) errBound
                                                 || maybe False (<= t)       timeout
        let reportingIO = case repInterval of
                Just rInterv -> \qLabel n bounds t lastRep -> if   t - lastRep >= rInterv
                                                              then Just $ printResult qLabel n t (Just bounds) ids2str ids2label
                                                              else Nothing
                _            -> \_      _ _      _ _       -> Nothing
        forM_
            queries
            ( \(qLabel, qRef) -> do
                  (n, t, mbBounds) <- IHPMC.ihpmc qRef evidence stopPred (reportingIO qLabel)
                  lift $ printResult qLabel n t mbBounds ids2str ids2label
                  when (isJust repInterval) $ lift $ doIO $ putStrLn ""
            )
    where
    printResult :: GroundedAST.RuleBodyElementPhase2
                -> Int
                -> Int
                -> Maybe ProbabilityBounds
                -> Map Int Text
                -> Map Int (Int, [AST.ConstantExpr])
                -> ExceptionalT IOException IO ()
    printResult qLabel n t mbBounds ids2str ids2label = doIO $ LTIO.putStrLn $ toLazyText $
        GroundedAST.ruleBodyElementToText qLabel ids2str ids2label <>
        " (iteration " <> showb n <>
        ", after " <> showb t <> "ms): " <>
        case mbBounds of
            Just (ProbabilityBounds l u) ->
                showb ((u + l) / 2.0) <>
                " (error bound: " <> showb ((u - l) / 2.0) <> ")"
            Nothing -> "inconsistent evidence"

doIOException :: IO a -> ExceptionalT (Exception, Map Int Text, Map Int (Int, [AST.ConstantExpr])) IO a
doIOException io = mapExceptionT ((,Map.empty, Map.empty) . IOException) $ doIO io

printIfSet :: (a -> Builder) -> Maybe a -> ExceptionalT (Exception, Map Int Text, Map Int (Int, [AST.ConstantExpr])) IO ()
printIfSet fstr = maybe (return ()) $ doIOException . LTIO.putStrLn . toLazyText . fstr

whenJust :: Monad m => Maybe a -> (a -> m ()) -> m ()
whenJust Nothing _   = return ()
whenJust (Just x) fx = fx x

