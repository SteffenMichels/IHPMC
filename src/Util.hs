--The MIT License (MIT)
--
--Copyright (c) 2016-2017 Steffen Michels (mail@steffen-michels.de)
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

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Util
    ( getFirst
    , showbLst
    , showbLstEnc
    , toTextLst
    , toTextLstEnc
    , doState
    , doMaybe
    , Bool3(..)
    , maybeRead
    ) where
import Data.HashMap (Map)
import qualified Data.HashMap as Map
import Data.HashSet (Set)
import qualified Data.HashSet as Set
import Control.Monad.State.Strict
import Control.Monad.Identity
import Control.Monad.Trans.Maybe (MaybeT)
import Data.Boolean
import Data.Maybe (listToMaybe)
import TextShow
import Data.Monoid ((<>))
import Data.Hashable (Hashable)
import qualified Data.Hashable as Hashable
import Data.Foldable (foldl')

instance Hashable a => Hashable (Set a) where
    hashWithSalt = Set.fold (flip Hashable.hashWithSalt)

instance (Hashable a, Hashable b) => Hashable (Map a b) where
    hashWithSalt s m = foldl' (\s' (k, a) -> Hashable.hashWithSalt (Hashable.hashWithSalt s' k) a) s $ Map.toList m

getFirst :: Set a -> a
getFirst set = head $ Set.toList set

showbLst :: TextShow a => [a] -> Builder
showbLst = (`toTextLst` showb)

showbLstEnc :: TextShow a => Builder -> Builder -> [a] -> Builder
showbLstEnc open close lst = toTextLstEnc open close lst showb

toTextLst :: [a] -> (a -> Builder) -> Builder
toTextLst []     _     = ""
toTextLst [a]    toTxt = toTxt a
toTextLst (a:as) toTxt = toTxt a <> ", " <> toTextLst as toTxt

toTextLstEnc :: Builder -> Builder -> [a] -> (a -> Builder) -> Builder
toTextLstEnc _ _ [] _            = ""
toTextLstEnc open close [a] toTxt   = open <> toTxt a <> close
toTextLstEnc open close (a:as) toTxt = open <> toTxt a <> close <> ", " <> toTextLstEnc open close as toTxt

doState :: Monad m => State s a -> StateT s m a
doState = mapStateT (\(Identity x) -> return x)

doMaybe :: Monad m => Maybe a -> MaybeT m a
doMaybe Nothing  = mzero
doMaybe (Just x) = return x

data Bool3 = True3 | False3 | Unknown3 deriving Eq

instance Boolean Bool3 where
    true  = True3
    false = False3

    notB True3    = False3
    notB False3   = True3
    notB Unknown3 = Unknown3

    False3   &&* _        = False3
    _        &&* False3   = False3
    Unknown3 &&* _        = Unknown3
    _        &&* Unknown3 = Unknown3
    _        &&* _        = True3

    True3    ||* _        = True3
    _        ||* True3    = True3
    Unknown3 ||* _        = Unknown3
    _        ||* Unknown3 = Unknown3
    _        ||* _        = False3

maybeRead :: Read a => String -> Maybe a
maybeRead = (fst <$>) . listToMaybe . reads
