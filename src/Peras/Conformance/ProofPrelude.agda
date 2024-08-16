
module Peras.Conformance.ProofPrelude where

open import Haskell.Prelude
open import Haskell.Prim.Tuple
open import Haskell.Law.Equality

open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (NonZero; ℕ; _≡ᵇ_)
open import Data.Nat.Properties using (_≟_; suc-injective)
open import Data.Nat.DivMod
open import Data.Maybe using (maybe′; nothing; just)
open import Data.Product as P using (∃; Σ-syntax; ∃-syntax; proj₁; proj₂)
open import Data.Sum as S using (inj₁; inj₂; _⊎_; [_,_])

open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary.Decidable using (Dec; yes; no)

open import Peras.Crypto
open import Peras.Util


mod : ℕ → (n : ℕ) → @0 ⦃ NonZero n ⦄ → ℕ
mod a b ⦃ prf ⦄ = _%_ a b ⦃ uneraseNonZero prf ⦄

div : ℕ → (n : ℕ) → @0 ⦃ NonZero n ⦄ → ℕ
div a b ⦃ prf ⦄ = _/_ a b ⦃ uneraseNonZero prf ⦄

eqℕ-sound : {n m : Nat} → (n == m) ≡ True → n ≡ m
eqℕ-sound {zero}  {zero}   _  = refl
eqℕ-sound {suc n} {suc m} prf = cong suc (eqℕ-sound prf)

not-eqℕ-sound : ∀ {n m : Nat} → not (n == m) ≡ True → n ≢ m
not-eqℕ-sound = not-eqℕ-sound' ∘ not_b≡True→b≡False
  where
    not-eqℕ-sound' : ∀ {n m : Nat} → (n == m) ≡ False → n ≢ m
    not-eqℕ-sound' {zero} {zero} ()
    not-eqℕ-sound' {zero} {suc m} x ()
    not-eqℕ-sound' {suc n} {zero} x ()
    not-eqℕ-sound' {suc n} {suc m} x x₁ = not-eqℕ-sound' {n} {m} x (suc-injective x₁)

    not_b≡True→b≡False : ∀ {b : Bool} → not b ≡ True → b ≡ False
    not_b≡True→b≡False {False} x = refl

lem-divMod : ∀ a b ⦃ _ : NonZero b ⦄ → mod a b ≡ 0 → a ≡ div a b * b
lem-divMod a b eq with lem ← m≡m%n+[m/n]*n a b rewrite eq = lem

suc-definition : ∀ {n} → suc n ≡ n + 1
suc-definition {zero} = refl
suc-definition {suc n} = cong suc (suc-definition {n})
