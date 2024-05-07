module Peras.QCD.Util where

import Numeric.Natural (Natural)
import Peras.QCD.Crypto (ByteString, eqBS)

zero :: Natural
zero = 0

eqBy :: Eq b => (a -> b) -> a -> a -> Bool
eqBy f x y = f x == f y

eqByBS :: (a -> ByteString) -> a -> a -> Bool
eqByBS f x y = eqBS (f x) (f y)

(⇉) :: Functor f => f a -> (a -> b) -> f b
x ⇉ f = fmap f x

addOne :: Natural -> Natural
addOne = (1 +)

checkDescending :: (a -> a -> Ordering) -> [a] -> Bool
checkDescending _ [] = True
checkDescending _ [_] = True
checkDescending f (x : (y : zs)) =
  f x y == GT && checkDescending f (y : zs)

insertDescending :: (a -> a -> Ordering) -> a -> [a] -> [a]
insertDescending _ x [] = [x]
insertDescending f x (y : ys) =
  case f x y of
    LT -> y : insertDescending f x ys
    EQ -> y : ys
    GT -> x : (y : ys)

unionDescending :: Ord b => (a -> b) -> [a] -> [a] -> [a]
unionDescending f xs ys =
  foldr (insertDescending (\x y -> compare (f x) (f y))) ys xs

groupBy :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy _ [] = []
groupBy f (x : xs) =
  (x : fst (span (f x) xs)) : groupBy f (snd (span (f x) xs))

count :: [a] -> Natural
count _ = 0

(↞) :: Applicative f => f [a] -> a -> f [a]
m ↞ x = fmap (\xs -> xs ++ [x]) m

infixl 5 ↞
