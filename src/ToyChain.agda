module ToyChain where

open import Data.Nat using (ℕ)
open import Haskell.Prelude
open import Haskell.Law

Slot = ℕ

record Block : Set where
    constructor MkBlock
    field
        slot : ℕ

open Block public
{-# COMPILE AGDA2HS Block #-}

Chain = List Block
{-# COMPILE AGDA2HS Chain #-}

data ValidChain : Chain → Set where
  Genesis : ValidChain (MkBlock 0 ∷ [])
  Cons : ∀ {c : Chain} → (b : Block) → (v : ValidChain c) → ValidChain (b ∷ c)

open ValidChain public

-- from agda2hs examples
record Equal (a : Set) : Set where
    constructor MkEqual
    field
        pair : a × a
        @0 proof : fst pair ≡ snd pair
open Equal public

{-# COMPILE AGDA2HS Equal newtype #-}

open NonEmpty public

instance
  itsNonEmptyChain : ∀ {c : Chain} → {v : ValidChain c} → NonEmpty c
  itsNonEmptyChain {.(MkBlock 0 ∷ [])} {Genesis} = itsNonEmpty
  itsNonEmptyChain {.(b ∷ _)} {Cons b v} = itsNonEmpty

-- Example property: the slot of the genesis block is 0

prop-genesis-in-slot0 : ∀ {c : Chain} → (v : ValidChain c) → slot (last c) ≡ 0
prop-genesis-in-slot0 {.(MkBlock 0) ∷ .[]} Genesis = refl
prop-genesis-in-slot0 {x ∷ c} (Cons .x v) =
  trans
     (cong slot (drop-head c x ⦃ itsNonEmptyChain {c} {v} ⦄))
     (prop-genesis-in-slot0 v)
  where
    drop-head : ∀ {A : Set} → (c : List A) → (b : A) → ⦃ _ : NonEmpty c ⦄ → last (b ∷ c) ≡ last c
    drop-head (_ ∷ _) _ ⦃ itsNonEmpty ⦄ = refl

-- Expressing the property for exporting to Haskell

propGenesisInSlot0 : ∀ (c : Chain) → (@0 v : ValidChain c) → Equal ℕ
propGenesisInSlot0 c v = MkEqual (slot (last c) , 0) (prop-genesis-in-slot0 v)

{-# COMPILE AGDA2HS propGenesisInSlot0 #-}
