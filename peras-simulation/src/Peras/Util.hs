{-# OPTIONS_GHC -fno-warn-missing-pattern-synonym-signatures #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module Peras.Util where

import Numeric.Natural (Natural)

import GHC.Integer

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

isYes :: Bool -> Bool
isYes True = True
isYes False = False

decP :: Bool -> Bool -> Bool
decP va vb = va && vb

decS :: Bool -> Bool -> Bool
decS va vb = va || vb

eqDec :: Natural -> Natural -> Bool
eqDec x y = x == y

eq :: Integer -> Integer -> Bool
eq = (==)

gt :: Integer -> Integer -> Bool
gt = gtInteger

ge :: Integer -> Integer -> Bool
ge = geInteger
