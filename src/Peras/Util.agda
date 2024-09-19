-- | Utility functions
module Peras.Util where

open import Haskell.Prelude
open import Data.Nat using (NonZero)

uneraseNonZero : ∀ {n} → @0 NonZero n → NonZero n
uneraseNonZero {zero} ()
uneraseNonZero {suc n} _ = _

maybeToList : Maybe a → List a
maybeToList Nothing = []
maybeToList (Just x) = x ∷ []

{-# COMPILE AGDA2HS maybeToList #-}

listToMaybe : List a → Maybe a
listToMaybe [] = Nothing
listToMaybe (x ∷ _) = Just x

{-# COMPILE AGDA2HS listToMaybe #-}

maximumBy : {a : Set} → a → (a → a → Ordering) → List a → a
maximumBy candidate _ [] = candidate
maximumBy {a} candidate f (x ∷ xs) =
  case f candidate x of λ where
    GT → maximumBy candidate f xs
    _ → maximumBy x f xs
{-# COMPILE AGDA2HS maximumBy #-}

comparing : ⦃ Ord b ⦄ → (a → b) → a → a → Ordering
comparing f x y = compare (f x) (f y)
{-# COMPILE AGDA2HS comparing #-}

mapMaybe : ∀ {a b : Set} → (a → Maybe b) → List a → List b
mapMaybe p []       = []
mapMaybe p (x ∷ xs) =
  case p x of λ where
    (Just y) → y ∷ mapMaybe p xs
    Nothing → mapMaybe p xs
{-# COMPILE AGDA2HS mapMaybe #-}
