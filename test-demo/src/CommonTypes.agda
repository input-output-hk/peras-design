
module CommonTypes where

open import Haskell.Prelude
open import Data.Nat.Base
open import Relation.Binary.PropositionalEquality

open import ProofPrelude

{-# FOREIGN AGDA2HS import GHC.Generics #-}

data Party : Set where
  Alice Bob : Party

{-# COMPILE AGDA2HS Party deriving (Eq, Ord, Show, Generic) #-}

BlockIndex = ℕ
Slot       = ℕ

{-# FOREIGN AGDA2HS
type BlockIndex = Integer
type Slot       = Integer
#-}

record Block : Set where
  constructor Blk
  field
    blockIndex : BlockIndex

open Block public

{-# COMPILE AGDA2HS Block deriving (Eq, Ord, Show, Generic) #-}

instance
  EqParty : Eq Party
  EqParty ._==_ Alice Alice = True
  EqParty ._==_ Alice Bob   = False
  EqParty ._==_ Bob   Alice = False
  EqParty ._==_ Bob   Bob   = True

  EqBlock : Eq Block
  EqBlock ._==_ (Blk i) (Blk j) = i == j

eqParty-sound : ∀ {p q : Party} → (p == q) ≡ True → p ≡ q
eqParty-sound {Alice} {Alice} _ = refl
eqParty-sound {Bob}   {Bob}   _ = refl

eqParty-complete : {p q : Party} → (p == q) ≡ False → p ≢ q
eqParty-complete {Alice} {Bob}   h ()
eqParty-complete {Bob}   {Alice} h ()

eqBlock-sound : ∀ {b b₁ : Block} → (b == b₁) ≡ True → b ≡ b₁
eqBlock-sound {Blk i} {Blk j} h = cong Blk (eqℕ-sound h)

eqBlock-complete : ∀ {b b₁ : Block} → (b == b₁) ≡ False → b ≢ b₁
eqBlock-complete {Blk i} isF refl = eqℕ-complete {i} isF refl
