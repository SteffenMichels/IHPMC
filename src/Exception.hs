-----------------------------------------------------------------------------
--
-- Module      :  Exception
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

module Exception
    ( doIO
    , returnExceptional
    , ExceptionalT
    , Exceptional
    , mapException
    , fromEither
    , runExceptionalT
    ) where
import qualified System.IO.Error as IOError
import Control.Monad.Exception.Synchronous

doIO :: IO a -> ExceptionalT String IO a
doIO action = mapExceptionT show (fromEitherT (IOError.tryIOError action))

returnExceptional :: Monad m => Exceptional e a -> ExceptionalT e m a
returnExceptional func = ExceptionalT $ return func

