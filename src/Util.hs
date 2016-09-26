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

module Util
    ( getFirst
    , showLst
    , showLstEnc
    , doState
    , doMaybe
    ) where
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Data.List (intercalate)
import Control.Monad.State.Strict
import Control.Monad.Identity
import Control.Monad.Trans.Maybe (MaybeT)

getFirst :: HashSet a -> a
getFirst set = head $ Set.toList set

showLst :: Show a => [a] -> String
showLst l = intercalate ", " $ show <$> l

showLstEnc :: Show a => String -> String -> [a] -> String
showLstEnc open close l = intercalate ", " $ (\el -> open ++ show el ++ close) <$> l

doState :: Monad m => State s a -> StateT s m a
doState = mapStateT (\(Identity x) -> return x)

doMaybe :: Monad m => Maybe a -> MaybeT m a
doMaybe Nothing  = mzero
doMaybe (Just x) = return x
