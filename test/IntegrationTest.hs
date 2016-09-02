-----------------------------------------------------------------------------
--
-- Module      :  IntegrationTest
-- Copyright   :
-- License     :  MIT
--
-- Maintainer  :
-- Stability   :
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

module IntegrationTest (IntegrationTest(..))
where
import Data.HashMap.Strict (HashMap)
import BasicTypes (Probability)

data IntegrationTest = IntegrationTest { label           :: String
                                       , model           :: String
                                       , expectedResults :: HashMap String Probability
                                       }

