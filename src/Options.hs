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

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Options
    ( parseConsoleArgs
    , Options(..)
    ) where
import System.Console.ArgParser
import Control.Monad.Exception.Synchronous
import Exception
import Probability
import System.Console.ArgParser.Params
import Util
import Text.Printf (printf)
import TextShow
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as TB
import qualified Parser
import Text.Parsec (parse)

data Options = Options
    { modelFile   :: String
    , nIterations :: Maybe Int
    , errBound    :: Maybe Probability
    , timeout     :: Maybe Int
    , repInterval :: Maybe Int
    , formExpPath :: Maybe String
    }

parseConsoleArgs :: Args -> ExceptionalT Builder IO Options
parseConsoleArgs args = do
    interf <- mapExceptionT showb $ doIO $ mkApp spec
    let interf' = setAppDescr interf "Interative Hybrid Probabilistic Model Counting (IHPMC) 0.0.1\nCopyright (c) 2016 Steffen Michels\nLicense: MIT"
    returnExceptional $ mapException TB.fromString $ fromEither $ parseArgs args interf'
    where
    spec :: ParserSpec Options
    spec = Options
        `parsedBy` reqPos    "modelfile"           `Descr` "file containing the probabilistic model"
        `andBy`    maybeFlag "iterations"          `Descr` "maximal number of iterations"
        `andBy`    maybeFlag "errorbound"          `Descr` "maximal result error bound"
        `andBy`    maybeFlag "timeout"             `Descr` "maximal inference runtime (ms)"
        `andBy`    maybeFlag "reporting_interval"  `Descr` "interval in which intermediate results are reported (ms)"
        `andBy`    maybeFlag "formula_export_path" `Descr` "path to file to which the initial formula is exported (as dot file)"

maybeFlag :: ReadArg a => Key -> StdArgParam (Maybe a)
maybeFlag key = StdArgParam (Optional Nothing) Flag key (SingleArgParser $ readArg' key)
    where
    readArg' key' arg = case readArg arg of
      Just val -> Right $ Just val
      Nothing  -> Left $ printf "Invalid value '%s' for parameter %s." arg key'

class ReadArg a where
    readArg :: String -> Maybe a

instance ReadArg Int where
    readArg = maybeRead

instance ReadArg Probability where
    readArg str = ratToProb <$> toMaybe (fromEither (parse Parser.rational "argument" str))

instance ReadArg String where
    readArg = Just
