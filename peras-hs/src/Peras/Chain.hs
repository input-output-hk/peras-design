{-# LANGUAGE ScopedTypeVariables #-}

module Peras.Chain where

import Peras.Block (Block)

data Chain t = Genesis
             | Cons (Block t) (Chain t)
                 deriving (Eq)

asList :: Chain t -> [Block t]
asList Genesis = []
asList (Cons x c) = x : asList c

asChain :: [Block t] -> Chain t
asChain [] = Genesis
asChain (x : bs) = Cons x (asChain bs)

foldl1Maybe :: (a -> a -> a) -> [a] -> Maybe a
foldl1Maybe f xs
  = foldl
      (\ m y ->
         Just
           (case m of
                Nothing -> y
                Just x -> f x y))
      Nothing
      xs

prefix :: Eq t => [Block t] -> [Block t] -> [Block t]
prefix (x : xs) (y : ys) = if x == y then x : prefix xs ys else []
prefix _ _ = []

commonPrefix :: Eq t => [Chain t] -> Chain t
commonPrefix chains
  = case foldl1Maybe prefix (reverse (map asList chains)) of
        Nothing -> Genesis
        Just bs -> asChain bs

