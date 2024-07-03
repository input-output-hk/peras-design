-- | Utility functions
module Peras.Util where

open import Haskell.Prelude

maximumBy : {a : Set} → a → (a → a → Ordering) → List a → a
maximumBy candidate _ [] = candidate
maximumBy {a} candidate f (x ∷ xs) =
  case f candidate x of λ where
    GT → maximumBy x f xs
    _ → maximumBy candidate f xs
{-# COMPILE AGDA2HS maximumBy #-}

comparing : ⦃ Ord b ⦄ → (a → b) → a → a → Ordering
comparing f x y = compare (f x) (f y)
{-# COMPILE AGDA2HS comparing #-}
