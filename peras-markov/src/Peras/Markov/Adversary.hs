{-# LANGUAGE NoImplicitPrelude #-}

module Peras.Markov.Adversary (
  transitions,
) where

import NumericPrelude.Base
import NumericPrelude.Numeric

transitions :: a -> a -> Int -> (a -> a -> t a -> t a) -> t a -> t a
transitions p q n transition' initial = foldr id initial . replicate n $ transition' p q
