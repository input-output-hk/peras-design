module Peras.QCD.Util where

open import Data.Nat using (ℕ)
open import Haskell.Prelude
open import Peras.QCD.Crypto using (ByteString; eqBS)

{-# FOREIGN AGDA2HS
zero :: Natural
zero = 0
#-}

-- Boolean functions.

eqBy : ⦃ _ : Eq b ⦄ → (a → b) → a → a → Bool
eqBy f x y = f x == f y
{-# COMPILE AGDA2HS eqBy #-}

eqByBS : (a → ByteString) → a → a → Bool
eqByBS f x y = eqBS (f x) (f y)
{-# COMPILE AGDA2HS eqByBS #-}

-- Control functions.

_⇉_ : ⦃ _ : Functor f ⦄ → f a → (a → b) → f b
_⇉_ x f = fmap f x
infixl 1 _⇉_
{-# COMPILE AGDA2HS _⇉_ #-}

-- Arithmetic functions.

addOne : ℕ → ℕ
addOne = 1 +_
{-# COMPILE AGDA2HS addOne #-}

-- List operations.

checkDescending : (a → a → Ordering) → List a → Bool
checkDescending _ [] = True
checkDescending _ (_ ∷ []) = True
checkDescending f (x ∷ y ∷ zs) = f x y == GT && checkDescending f (y ∷ zs)
{-# COMPILE AGDA2HS checkDescending #-}

insertDescending : (a → a → Ordering) → a → List a → List a
insertDescending _ x [] = x ∷ []
insertDescending f x (y ∷ ys) = case f x y of λ where
                                  LT → y ∷ insertDescending f x ys
                                  EQ → y ∷ ys -- Is it safe to ignore equivocations?
                                  GT → x ∷ y ∷ ys
{-# COMPILE AGDA2HS insertDescending #-}

unionDescending : ⦃ _ : Ord b ⦄ → (a → b) → List a → List a → List a
unionDescending f xs ys = foldr (insertDescending (λ x y → compare (f x) (f y))) ys xs
{-# COMPILE AGDA2HS unionDescending #-}

{-# TERMINATING #-}
groupBy : (a → a → Bool) → List a → List (List a)
groupBy _ [] = []
groupBy f (x ∷ xs) = let (ys , zs) = span (f x) xs
                     in (x ∷ ys) ∷ groupBy f zs
{-# COMPILE AGDA2HS groupBy #-}   

count : List a → ℕ
count _ = 0
{-# COMPILE AGDA2HS count #-}

firstWithDefault : a → List a → a
firstWithDefault x [] = x
firstWithDefault _ (x ∷ _) = x
{-# COMPILE AGDA2HS firstWithDefault #-}

_↞_ : ⦃ _ : Applicative f ⦄ → f (List a) → a → f (List a)
_↞_ m x = fmap (λ xs → xs ++ (x ∷ [])) m
infixl 30 _↞_
{-# COMPILE AGDA2HS _↞_ #-}
{-# FOREIGN AGDA2HS
infixl 5 ↞
#-}

integerDivide : ℕ → ℕ → ℕ
integerDivide x y = _
{-# COMPILE AGDA2HS integerDivide #-}
