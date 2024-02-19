{-# LANGUAGE ScopedTypeVariables #-}
module Peras.Chain where

import Peras.Block (Block)

data Chain t = Genesis
             | Cons (Block t) (Chain t)
                 deriving (Eq)

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

asList :: forall t . Eq t => Chain t -> [Block t]
asList Genesis = []
asList (Cons x c) = x : asList c

asChain :: forall t . Eq t => [Block t] -> Chain t
asChain [] = Genesis
asChain (x : bs) = Cons x (asChain bs)

prefix ::
       forall t . Eq t => [Block t] -> [Block t] -> [Block t] -> [Block t]
prefix acc (x : xs) (y : ys)
  = if x == y then prefix (x : acc) xs ys else reverse acc
prefix acc _ _ = reverse acc

commonPrefix :: forall t . Eq t => [Chain t] -> Chain t
commonPrefix chains
  = case listPrefix of
        Nothing -> Genesis
        Just bs -> asChain (reverse bs)
  where
    listPrefix :: Maybe [Block t]
    listPrefix
      = foldl1Maybe (prefix []) (map (\ l -> reverse (asList l)) chains)

