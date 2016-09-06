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
import BasicTypes
import qualified Parser
import qualified Grounder
import qualified FormulaConverter
import Exception
import Text.Printf (printf)
import qualified IHPMC
import Control.Monad.Exception.Synchronous
import IntegrationTest
import qualified IntegrationGrounding
import Control.Monad (forM)
import Data.Foldable (foldl')
import Main (Exception(..))
import qualified AST
import Control.Monad.Trans.Class (lift)

allTests :: [(String, [IntegrationTest])]
allTests = [IntegrationGrounding.tests]

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

checkResults :: String -> [((AST.PredicateLabel, [AST.Expr]), Exceptional Exception (Probability, Probability) -> Bool)] ->  IO Progress
checkResults src expRes = do
    result <- runExceptionalT checkResults'
    return $ Finished $ case result of
        Exception e -> Error $ show e
        Success res -> res
    where
    checkResults' :: ExceptionalT Exception IO Result
    checkResults' = do
        ast <- returnExceptional $ mapException ParserException $ Parser.parsePclp src
        assertT (TestException "No queries in source expected.") $ null $ AST.queries ast
        assertT (TestException "No evidence expected.")          $ null $ AST.evidence ast
        let stopPred _ (ProbabilityBounds l u) _ = l == u
        results <- forM expRes $ \(query, isExp) -> do
            res <- lift $ runExceptionalT $ do
                let ast' = ast{AST.queries = [query]}
                groundedAst <- returnExceptional $ mapException GrounderException $ Grounder.ground ast'
                let (([(_, qRef)], _), f) = FormulaConverter.convert groundedAst IHPMC.heuristicsCacheComputations
                [(_, _, ProbabilityBounds l u)] <- mapExceptionT IOException $ IHPMC.ihpmc qRef [] stopPred Nothing f
                return (l, u)
            return (query, isExp res, res)
        return $ maybe Pass Fail $ foldl' combineResults Nothing results

combineResults :: Maybe String
               -> ((AST.PredicateLabel, [AST.Expr]), Bool, Exceptional Exception (Probability, Probability))
               -> Maybe String
combineResults mbErr (query, isExp, res)
    | isExp = mbErr
    | otherwise = Just $ printf
        "%sunexpected result '%s' for query '%s'"
        (maybe "" (printf "%s; ") mbErr)
        (show res)
        (showQuery query)
    where
        showQuery :: (AST.PredicateLabel, [AST.Expr]) -> String
        showQuery (l, args) = printf "%s(%s)" (show l) (showLst args)
