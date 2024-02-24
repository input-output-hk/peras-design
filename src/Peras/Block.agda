module Peras.Block where

open import Level
open import Data.Nat using (ℕ)
open import Data.Bool
open import Data.List

open import Data.Tree.AVL.Sets renaming (⟨Set⟩ to set)
open import Relation.Binary using (DecidableEquality; StrictTotalOrder)

open import Haskell.Prelude using (Eq)

open import Peras.Crypto hiding (ByteString; emptyBS; _isInfixOf_)

-- TODO: ByteString is not exported from Peras.Crypto in Haskell
postulate
  ByteString : Set
  emptyBS : ByteString
  _isInfixOf_ : ByteString → ByteString → Bool

{-# FOREIGN AGDA2HS import Data.ByteString as BS #-}
{-# FOREIGN GHC import qualified Data.ByteString as BS #-}
{-# COMPILE GHC ByteString = type BS.ByteString #-}

record PartyId : Set where
  constructor MkPartyId
  field vkey : VerificationKey

open PartyId public

{-# COMPILE AGDA2HS PartyId deriving (Eq) #-}

postulate
  paEq : Relation.Binary.Rel PartyId 0ℓ
  paLt : Relation.Binary.Rel PartyId 0ℓ
  paIs : Relation.Binary.IsStrictTotalOrder paEq paLt

PartyIdO : StrictTotalOrder 0ℓ 0ℓ 0ℓ
PartyIdO = record {
  Carrier            = PartyId ;
  _≈_                = paEq ;
  _<_                = paLt ;
  isStrictTotalOrder = paIs }

data Honesty : PartyId → Set where

  Honest : ∀ {p : PartyId}
    → Honesty p

  Corrupt : ∀ {p : PartyId}
    → Honesty p

-- Transactions

record Tx : Set where
  field tx : ByteString

open Tx public

{-# COMPILE AGDA2HS Tx newtype deriving Eq #-}

Slot = ℕ

{-# COMPILE AGDA2HS Slot #-}

record Block : Set where
  field slotNumber : Slot
        creatorId : PartyId
        parentBlock : Hash
        includedVotes : List Hash
        leadershipProof : LeadershipProof
        payload : List Tx
        signature : Signature

open Block public

{-# COMPILE AGDA2HS Block #-}
