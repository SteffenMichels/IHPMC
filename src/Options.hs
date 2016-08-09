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

module Options
    ( parseConsoleArgs
    , Options(..)
    ) where
import System.Console.ArgParser
import Control.Monad.Exception.Synchronous
import Exception
import BasicTypes
import GHC.Float (float2Double)

data Options = Options
    { nIterations :: Maybe Int
    , modelFile   :: String
    , errBound    :: Maybe Probability
    , timeout     :: Maybe Int
    , repInterval :: Maybe Int
    }

-- this type is used, because argparse package does not support parsing Maybe values
data ParsedOptions = ParsedOptions
    { pModelFile   :: String
    , pNIterations :: Int
    , pErrBound    :: Float
    , pTimeout     :: Int
    , pRepInterval :: Int
    }

popts2opts :: ParsedOptions -> Options
popts2opts ParsedOptions{pModelFile,pNIterations,pErrBound,pTimeout,pRepInterval} = Options
    { modelFile   = pModelFile
    , nIterations = justIf (>  0)                               pNIterations
    , errBound    = justIf (>= 0) $ doubleToProb $ float2Double pErrBound
    , timeout     = justIf (>  0)                               pTimeout
    , repInterval = justIf (>= 0)                               pRepInterval
    }
    where
    justIf pred v = if pred v then Just v else Nothing

parseConsoleArgs :: Args -> ExceptionalT String IO Options
parseConsoleArgs args = do
    interf <- doIO $ mkApp spec
    popts <- returnExceptional $ fromEither $ parseArgs args interf
    return $ popts2opts popts
    where
    spec :: ParserSpec ParsedOptions
    spec = ParsedOptions
        `parsedBy` reqPos       "modelfile"          `Descr` "file containing the probabilistic model"
        `andBy`    optFlag 0    "iterations"         `Descr` "maximal number of iterations"
        `andBy`    optFlag (-1) "errorbound"         `Descr` "maximal result error bound"
        `andBy`    optFlag 0    "timeout"            `Descr` "maximal inference runtime (ms)"
        `andBy`    optFlag (-1) "reporting_interval" `Descr` "interval in which intermediate results are reported (ms)"
