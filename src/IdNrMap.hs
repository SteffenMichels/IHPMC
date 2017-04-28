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

module IdNrMap
    ( IdNrMap
    , empty
    , getIdNr
    , fromIdNrMap
    , toIdNrMap
    ) where
import Data.HashMap (Map)
import qualified Data.HashMap as Map
import Data.Hashable (Hashable)

data IdNrMap a = IdNrMap (Map a Int) (Map Int a) Int

empty :: IdNrMap a
empty = IdNrMap Map.empty Map.empty 0

getIdNr :: (Ord a, Hashable a) => a -> IdNrMap a -> (Int, IdNrMap a)
getIdNr x m@(IdNrMap to from count) = case Map.lookup x to of
    Just idNr -> (idNr, m)
    Nothing   -> (count, IdNrMap (Map.insert x count to) (Map.insert count x from) (succ count))

fromIdNrMap :: IdNrMap a -> Map Int a
fromIdNrMap (IdNrMap _ from _) = from

toIdNrMap :: IdNrMap a -> Map a Int
toIdNrMap (IdNrMap to _ _) = to
