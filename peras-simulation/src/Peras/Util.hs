module Peras.Util where

isJust :: Maybe a -> Bool
isJust Nothing = False
isJust (Just _) = True

maybeToList :: Maybe a -> [a]
maybeToList Nothing = []
maybeToList (Just x) = [x]

listToMaybe :: [a] -> Maybe a
listToMaybe [] = Nothing
listToMaybe (x : _) = Just x

maximumBy :: a -> (a -> a -> Ordering) -> [a] -> a
maximumBy candidate _ [] = candidate
maximumBy candidate f (x : xs) =
  case f candidate x of
    GT -> maximumBy candidate f xs
    _ -> maximumBy x f xs

comparing :: Ord b => (a -> b) -> a -> a -> Ordering
comparing f x y = compare (f x) (f y)
