
module ProofPrelude where

open import Haskell.Prelude renaming (_<_ to _<ʰ_)
open import Data.Nat.Base
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

it : {A : Set} → ⦃ A ⦄ → A
it ⦃ x ⦄ = x

-- Boolean shenanigans

&&ˡ : ∀ {a b : Bool} → (a && b) ≡ True → a ≡ True
&&ˡ {True} _ = refl

&&ʳ : ∀ {a b : Bool} → (a && b) ≡ True → b ≡ True
&&ʳ {True} {True} _ = refl

!&& : ∀ {a b : Bool} → (a && b) ≡ False → a ≡ False ⊎ b ≡ False
!&& {False}        _ = inj₁ refl
!&& {True} {False} _ = inj₂ refl

not-elim : ∀ {a} → not a ≡ True → a ≡ False
not-elim {False} _ = refl

-- Natural numbers

eqℕ-sound : {n m : ℕ} → (n == m) ≡ True → n ≡ m
eqℕ-sound {zero}  {zero}   _   = refl
eqℕ-sound {suc n} {suc m} prf = cong suc (eqℕ-sound prf)

eqℕ-complete : {n m : ℕ} → (n == m) ≡ False → n ≢ m
eqℕ-complete {suc n} isF refl = eqℕ-complete {n} isF refl

ltℕ-sound : ∀ {n m} → (n <ʰ m) ≡ True → n < m
ltℕ-sound {zero}  {suc m} h = s≤s z≤n
ltℕ-sound {suc n} {suc m} h = s≤s (ltℕ-sound h)

ltℕ-complete : ∀ {n m} → (n <ʰ m) ≡ False → ¬ (n < m)
ltℕ-complete {suc n} {suc m} h (s≤s lt) = ltℕ-complete {n} {m} h lt
