-----------------------------------------------------------------------------
--
-- Module      :  Options
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
    }

-- this type is used, because argparse package does not support parsing Maybe values
data ParsedOptions = ParsedOptions
    { pModelFile   :: String
    , pNIterations :: Int
    , pErrBound    :: Float
    , pTimeout     :: Int
    }

popts2opts :: ParsedOptions -> Options
popts2opts ParsedOptions{pModelFile,pNIterations,pErrBound,pTimeout} = Options
    { modelFile   = pModelFile
    , nIterations = justIf (>  0)                               pNIterations
    , errBound    = justIf (>= 0) $ doubleToProb $ float2Double pErrBound
    , timeout     = justIf (>  0)                               pTimeout
    } where
    justIf pred v = if pred v then Just v else Nothing

parseConsoleArgs :: Args -> ExceptionalT String IO Options
parseConsoleArgs args = do
    interf <- doIO $ mkApp spec
    popts <- returnExceptional $ fromEither $ parseArgs args interf
    return $ popts2opts popts
    where
        spec :: ParserSpec ParsedOptions
        spec = ParsedOptions
            `parsedBy` reqPos       "modelfile"  `Descr` "file containing the probabilistic model"
            `andBy`    optFlag 0    "iterations" `Descr` "maximal number of iterations"
            `andBy`    optFlag (-1) "errorbound" `Descr` "maximal result error bound"
            `andBy`    optFlag 0    "timeout"    `Descr` "maximal inference runtime (ms)"
