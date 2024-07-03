-- | Utility functions
module Peras.Util where

open import Haskell.Prelude
open import Data.Nat using (NonZero)

uneraseNonZero : ∀ {n} → @0 NonZero n → NonZero n
uneraseNonZero {zero} ()
uneraseNonZero {suc n} _ = _

isJust : Maybe a → Maybe Bool
isJust = pure ∘ maybe False (const True)

{-# COMPILE AGDA2HS isJust #-}

catMaybes : List (Maybe a) → List a
catMaybes [] = []
catMaybes (Nothing ∷ xs) = catMaybes xs
catMaybes (Just x ∷ xs) = x ∷ catMaybes xs

{-# COMPILE AGDA2HS catMaybes #-}

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
    GT → maximumBy x f xs
    _ → maximumBy candidate f xs
{-# COMPILE AGDA2HS maximumBy #-}

comparing : ⦃ Ord b ⦄ → (a → b) → a → a → Ordering
comparing f x y = compare (f x) (f y)
{-# COMPILE AGDA2HS comparing #-}
