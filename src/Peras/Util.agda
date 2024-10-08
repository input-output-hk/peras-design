-- | Utility functions
module Peras.Util where

open import Haskell.Prelude hiding (_<_; _>_)
open import Haskell.Extra.Dec
open import Haskell.Extra.Refinement
open import Haskell.Law.Eq.Def
open import Haskell.Law.Eq.Instances

import Data.Bool
open import Data.Nat using (ℕ; NonZero; _≤_; _<_; _≥_; _>_; z≤n; s≤s; z<s; s<s)

{-# FOREIGN AGDA2HS
  {-# OPTIONS_GHC -fno-warn-missing-pattern-synonym-signatures #-}
  {-# OPTIONS_GHC -fno-warn-missing-signatures #-}
  {-# OPTIONS_GHC -fno-warn-name-shadowing #-}
  {-# OPTIONS_GHC -fno-warn-type-defaults #-}
  {-# OPTIONS_GHC -fno-warn-unused-imports #-}
  {-# OPTIONS_GHC -fno-warn-unused-matches #-}
  import GHC.Integer
#-}

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

mapMaybe : {a b : Set} → (a → Maybe b) → List a → List b
mapMaybe p []       = []
mapMaybe p (x ∷ xs) with p x
... | Just y  = y ∷ mapMaybe p xs
... | Nothing =     mapMaybe p xs

-- mapMaybe is exported in rewrites.yaml

isYes : ∀ {A : Set} → Dec A → Bool
isYes (True ⟨ _ ⟩) = True
isYes (False ⟨ _ ⟩) = False

{-# COMPILE AGDA2HS isYes #-}

TTrue : ∀ {A : Set} → Dec A → Set
TTrue a = Data.Bool.T (isYes a)

toTT : ∀ {A : Set} → {a : Dec A} → value a ≡ True → TTrue {A} a
toTT refl = tt

@0 isYes≡True⇒TTrue : ∀ {A : Set} → {a : Dec A} → isYes a ≡ True → TTrue {A} a
isYes≡True⇒TTrue x = toTT (isYes≡True⇒value≡True x)
  where
    isYes≡True⇒value≡True : ∀ {A : Set} → {a : Dec A} → isYes a ≡ True → value a ≡ True
    isYes≡True⇒value≡True {a = True ⟨ _ ⟩} _ = refl

@0 toWitness : ∀ {A : Set} {a : Dec A} → TTrue a → A
toWitness {a = True ⟨ prf ⟩} _ = prf

_×-reflects_ : ∀ {a b} {A B : Set} → Reflects A a → Reflects B b → Reflects (A × B) (a && b)
_×-reflects_ {True} {True} x y = x , y
_×-reflects_ {True} {False} _ y = y ∘ snd
_×-reflects_ {False} {True} x _ = x ∘ fst
_×-reflects_ {False} {False} x _ = x ∘ fst

decP : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
decP (va ⟨ pa ⟩) (vb ⟨ pb ⟩) = (va && vb ) ⟨ pa ×-reflects pb ⟩

{-# COMPILE AGDA2HS decP #-}

_⊎-reflects_ : ∀ {a b} {A B : Set} → Reflects A a → Reflects B b → Reflects (Either A B) (a || b)
_⊎-reflects_ {True} {True} x _ = Left x
_⊎-reflects_ {True} {False} x _ = Left x
_⊎-reflects_ {False} {True} _ y = Right y
_⊎-reflects_ {False} {False} x y = either x y

decS : ∀ {A B : Set} → Dec A → Dec B → Dec (Either A B)
decS (va ⟨ pa ⟩) (vb ⟨ pb ⟩) = (va || vb ) ⟨ pa ⊎-reflects pb ⟩

{-# COMPILE AGDA2HS decS #-}

eqDec : ∀ (x y : Nat) → Dec (x ≡ y)
eqDec x y = (x == y) ⟨ isEquality x y ⟩

{-# COMPILE AGDA2HS eqDec #-}

postulate
  eq : ∀ (x y : ℕ) → Dec (x ≡ y)
  ge : ∀ (x y : ℕ) → Dec (x ≥ y)
  gt : ∀ (x y : ℕ) → Dec (x > y)

{-# FOREIGN AGDA2HS
  eq :: Integer -> Integer -> Bool
  eq = (==)

  gt :: Integer -> Integer -> Bool
  gt = gtInteger

  ge :: Integer -> Integer -> Bool
  ge = geInteger
#-}
