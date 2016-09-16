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

module Exception
    ( doIO
    , returnExceptional
    , ExceptionalT
    , Exceptional(..)
    , IOException
    , mapException
    , fromEither
    , runExceptionalT
    , throwT
    , throw
    , exceptionalFromMaybe
    ) where
import qualified System.IO.Error as IOError
import Control.Monad.Exception.Synchronous

newtype IOException = IOException String

instance Show IOException
    where
    show (IOException e) = e

doIO :: IO a -> ExceptionalT IOException IO a
doIO action = mapExceptionT (IOException . show) (fromEitherT (IOError.tryIOError action))

returnExceptional :: Monad m => Exceptional e a -> ExceptionalT e m a
returnExceptional exc = ExceptionalT $ return exc

exceptionalFromMaybe :: e -> Maybe a -> Exceptional e a
exceptionalFromMaybe = fromMaybe
