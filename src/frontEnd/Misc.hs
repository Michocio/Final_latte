{-
Nothing interesting, just some helping functions.
-}

module Misc where


import Data.List


type Debug = (Maybe (Int, Int))

repeated :: Ord a => [a] -> [a]
repeated = repeatedBy (>1)
sg :: Ord a => [a] -> [[a]]
sg = group . sort
repeatedBy :: Ord a => (Int -> Bool) -> [a] -> [a]
repeatedBy p = map head . filterByLength p
filterByLength :: Ord a => (Int -> Bool) -> [a] -> [[a]]
filterByLength p = filter (p . length) . sg
insertElement :: Int ->a -> [a] -> [a]
insertElement  z y xs = as ++ (y:bs)
    where (as,bs) = splitAt z xs
