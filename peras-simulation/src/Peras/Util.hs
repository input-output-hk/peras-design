module Peras.Util where

isJust :: Maybe a -> Bool
isJust Nothing = False
isJust (Just _) = True

mapMaybe :: (a -> Maybe b) -> [a] -> [b]
mapMaybe p [] = []
mapMaybe p (x : xs) =
  case p x of
    Just y -> y : mapMaybe p xs
    Nothing -> mapMaybe p xs

catMaybes :: [Maybe a] -> [a]
catMaybes [] = []
catMaybes (Nothing : xs) = catMaybes xs
catMaybes (Just x : xs) = x : catMaybes xs

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
