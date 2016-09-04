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
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import IntegrationTest
import qualified IntegrationGrounding
import Control.Monad (forM)
import Data.Foldable (foldl')

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
        , name = label
        , tags = []
        , options = []
        , setOption = \_ _ -> Right inst
        }

checkResults :: String -> HashMap String Probability ->  IO Progress
checkResults src expRes = do
    result <- runExceptionalT checkResults'
    return $ Finished $ case result of
        Exception e -> Error e
        Success res -> res
    where
    checkResults' = do
        ast <- returnExceptional $ Parser.parsePclp src
        let groundedAst = Grounder.ground ast
        let ((queries, evidence), f) = FormulaConverter.convert groundedAst IHPMC.heuristicsCacheComputations
        assertT "No evidence expected." $ null evidence
        let stopPred _ (ProbabilityBounds l u) _ = l == u
        results <- forM queries $ \(qLabel, qRef) -> do
            [(_, _, ProbabilityBounds l u)] <- IHPMC.ihpmc qRef [] stopPred Nothing f
            expP <- case Map.lookup (show qLabel) expRes of
                Just p  -> return p
                Nothing -> throwT $ printf "no expected result for query '%s'" $ show qLabel
            return (l, u, expP)
        return $ maybe Pass Fail $ foldl' combineResults Nothing results

combineResults :: Maybe String -> (Probability, Probability, Probability) -> Maybe String
combineResults mbErr (l, u, expP)
    | l == u && l == expP = mbErr
    | otherwise = Just $ printf
        "%sexpected P_min = P_max = %s, but P_min = %s and P_max = %s"
        (maybe "" (printf "%s; ") mbErr)
        (show expP)
        (show l)
        (show u)
