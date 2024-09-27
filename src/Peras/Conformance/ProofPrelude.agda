
module Peras.Conformance.ProofPrelude where

open import Haskell.Prelude

open import Haskell.Extra.Dec
open import Haskell.Extra.Refinement
open import Haskell.Prim
open import Haskell.Prim.Tuple
open import Haskell.Prim.Eq
open import Haskell.Law.Bool
open import Haskell.Law.Equality
open import Haskell.Law.Eq.Def
open import Haskell.Law.Eq.Instances

open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (NonZero; ℕ; _≡ᵇ_)
open import Data.Nat.Properties using (_≟_; suc-injective)
open import Data.Nat.DivMod
open import Data.Maybe using (maybe′; nothing; just)
open import Data.Product as P using (∃; Σ-syntax; ∃-syntax; proj₁; proj₂)
open import Data.Sum as S using (inj₁; inj₂; _⊎_; [_,_])
open import Level using (Level)

open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary.Decidable using (Dec; yes; no)

open import Peras.Crypto
open import Peras.Util

mod : ℕ → (n : ℕ) → @0 ⦃ NonZero n ⦄ → ℕ
mod a b ⦃ prf ⦄ = _%_ a b ⦃ uneraseNonZero prf ⦄

div : ℕ → (n : ℕ) → @0 ⦃ NonZero n ⦄ → ℕ
div a b ⦃ prf ⦄ = _/_ a b ⦃ uneraseNonZero prf ⦄

private
  variable
    w : Level
    A B : Set
    Whatever : Set w

  infix 3 ¬_
  ¬_ : Set → Set
  ¬ A = A → ⊥

⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
⊥-elim ()

contradiction : A → ¬ A → Whatever
contradiction a ¬a = ⊥-elim (¬a a)

contraposition : (A → B) → ¬ B → ¬ A
contraposition f ¬b a = contradiction (f a) ¬b

-- TODO: Use IsLawfulEq instances

eqℕ-sound : {n m : Nat} → (n == m) ≡ True → n ≡ m
eqℕ-sound {zero}  {zero}   _  = refl
eqℕ-sound {suc n} {suc m} prf = cong suc (eqℕ-sound prf)

eq𝔹-sound : {n m : Bool} → (n == m) ≡ True → n ≡ m
eq𝔹-sound {False} {False} _ = refl
eq𝔹-sound {True} {True} _ = refl

not-eqℕ-sound' : ∀ {n m : Nat} → (n == m) ≡ False → n ≢ m
not-eqℕ-sound' {zero} {zero} ()
not-eqℕ-sound' {zero} {suc m} x ()
not-eqℕ-sound' {suc n} {zero} x ()
not-eqℕ-sound' {suc n} {suc m} x x₁ = not-eqℕ-sound' {n} {m} x (suc-injective x₁)

not_b≡True→b≡False : ∀ {b : Bool} → not b ≡ True → b ≡ False
not_b≡True→b≡False {False} x = refl

not-eqℕ-sound : ∀ {n m : Nat} → not (n == m) ≡ True → n ≢ m
not-eqℕ-sound = not-eqℕ-sound' ∘ not_b≡True→b≡False

eqBS-sound : ∀ {n m : ByteString} → eqBS n m ≡ True → n ≡ m
eqBS-sound = lem-eqBS

not-eqBS-sound : {n m : ByteString} → eqBS n m ≡ False → n ≡ m → ⊥
not-eqBS-sound = contraposition lem-eqBS' ∘ flip exFalso

eqList-sound : ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄ → {l₁ l₂ : List a} → (l₁ == l₂) ≡ True → l₁ ≡ l₂
eqList-sound {l₁ = l₁} {l₂ = l₂} = equality l₁ l₂

lem-divMod : ∀ a b ⦃ _ : NonZero b ⦄ → mod a b ≡ 0 → a ≡ div a b * b
lem-divMod a b eq with lem ← m≡m%n+[m/n]*n a b rewrite eq = lem

¬any-[] : ∀ {a : Set} {f : a → Bool} → any f [] ≡ False
¬any-[] = refl

¬Any-[] : ∀ {a : Set} {f : a → Set} → Any f [] → ⊥
¬Any-[] ()

any-prf : ∀ {A : Set} {f : A → Set} {g : A → Bool} (as : List A)
  → (∀ x → Reflects (f x) (g x)) → Reflects (Any f as) (any g as)
any-prf [] x = ¬Any-[]
any-prf {g = g} (a ∷ as) f～g
  with g a in eq
any-prf (a ∷ as) f～g | True =
  let t = extractTrue ⦃ eq ⦄ (f～g a)
  in anyHere ⦃ t ⦄
any-prf {g = g} (a ∷ as) f～g | False
  with any g as in eq₁
any-prf (a ∷ as) f～g | False | True =
  let t = extractTrue ⦃ eq₁ ⦄ (any-prf as f～g)
  in anyThere ⦃ t ⦄
any-prf (a ∷ as) f～g | False | False =
  let f₁ = extractFalse ⦃ eq ⦄ (f～g a)
      f₂ = extractFalse ⦃ eq₁ ⦄ (any-prf as f～g)
  in λ where
       (anyHere ⦃ i ⦄) → f₁ i
       (anyThere ⦃ is ⦄) → f₂ is
