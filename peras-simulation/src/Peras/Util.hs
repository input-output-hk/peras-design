module Peras.Util where

maximumBy :: a -> (a -> a -> Ordering) -> [a] -> a
maximumBy candidate _ [] = candidate
maximumBy candidate f (x : xs) =
  case f candidate x of
    GT -> maximumBy x f xs
    _ -> maximumBy candidate f xs

comparing :: Ord b => (a -> b) -> a -> a -> Ordering
comparing f x y = compare (f x) (f y)
