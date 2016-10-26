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

module Integration (tests, IntegrationTest(..)) where
import Distribution.TestSuite
import qualified Parser
import qualified Grounder
import qualified FormulaConverter
import Exception
import Text.Printf (printf)
import qualified IHPMC
import Control.Monad.Exception.Synchronous
import IntegrationTest (IntegrationTest (..))
import qualified IntegrationGrounding
import qualified IntegrationExactProbabilities
import Control.Monad (forM)
import Data.Foldable (foldl')
import Main (Exception(..), exceptionToText)
import qualified AST
import Control.Monad.Trans.Class (lift)
import Probability
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import qualified IdNrMap

allTests :: [(String, [IntegrationTest])]
allTests = [IntegrationGrounding.tests, IntegrationExactProbabilities.tests]

tests :: IO [Test]
tests = return $ map toTestGroup allTests

toTestGroup :: (String, [IntegrationTest]) -> Test
toTestGroup (label, tsts) = testGroup label $ map toTests tsts

toTests :: IntegrationTest -> Test
toTests IntegrationTest{label, model, expectedResults} = Test inst
    where
    inst = TestInstance
         { run  = checkResults model expectedResults
         , name = printf "\"%s\"" label
         , tags = []
         , options = []
         , setOption = \_ _ -> Right inst
         }

checkResults :: String
             -> [(HashMap String Int -> AST.RuleBodyElement, Exceptional Exception (Maybe ProbabilityBounds) -> HashMap String Int -> Bool)]
             -> IO Progress
checkResults src expRes = do
    result <- runExceptionalT checkResults'
    return $ Finished $ case result of
        Exception (e, ids2Str, ids2label) -> Error $ exceptionToText e ids2Str ids2label
        Success res                       -> res
    where
    checkResults' :: ExceptionalT (Exception, HashMap Int String, HashMap Int (Int, [AST.ConstantExpr])) IO Result
    checkResults' = do
        (ast, identIds) <- returnExceptional $ mapException ((,Map.empty, Map.empty) . ParserException) $ Parser.parsePclp src
        let ids2str = IdNrMap.fromIdNrMap identIds
        let strs2id = IdNrMap.toIdNrMap   identIds
        assertT (((,ids2str, Map.empty) . TestException) "No queries in source expected.") $ null $ AST.queries ast
        assertT (((,ids2str, Map.empty) . TestException) "No evidence expected.")          $ null $ AST.evidence ast
        results <- forM expRes $ \(query, isExp) -> do
            let query' = query strs2id
            res <- lift $ runExceptionalT $ do
                let ast' = ast{AST.queries = [query']}
                (groundedAst, _) <- returnExceptional $ mapException ((,Map.empty) . GrounderException) $ Grounder.ground ast'
                let (([(_, qRef)], _), f) = FormulaConverter.convert groundedAst IHPMC.heuristicsCacheComputations
                (_, _, bounds) <- mapExceptionT ((,Map.empty) . IOException) $ IHPMC.ihpmc qRef [] stopPred (\_ _ _ _ -> Nothing) f
                return bounds
            return (query', isExp (mapException fst res) strs2id, res)
        return $ maybe Pass Fail $ foldl' (\mbErr res -> combineResults mbErr res ids2str) Nothing results

    stopPred _ (ProbabilityBounds l u) _ = l == u

combineResults :: Maybe String
               -> (AST.RuleBodyElement, Bool, Exceptional (Exception, HashMap Int (Int, [AST.ConstantExpr])) (Maybe ProbabilityBounds))
               -> HashMap Int String
               -> Maybe String
combineResults mbErr (query, isExp, res) ids2str
    | isExp = mbErr
    | otherwise = Just $ printf
        "%sunexpected result '%s' for query '%s'"
        (maybe "" (printf "%s; ") mbErr)
        (show $ mapException (\(e, ids2label) -> exceptionToText e ids2str ids2label) res)
        (AST.ruleBodyElementToText query ids2str)
