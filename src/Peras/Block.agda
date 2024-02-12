module Peras.Block where

open import Level
open import Agda.Builtin.Nat
open import Data.Bool
open import Data.List
open import Data.Tree.AVL.Sets renaming (⟨Set⟩ to set)
open import Relation.Binary using (StrictTotalOrder)

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

{-# COMPILE AGDA2HS PartyId #-}

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

record Tx : Set where
  field tx : ByteString

open Tx public

{-# COMPILE AGDA2HS Tx #-}

Slot = Nat

{-# COMPILE AGDA2HS Slot #-}

record Block (t : Set) : Set where
  field slotNumber : Slot
        -- blockHeight : Word64
        creatorId : PartyId
        parentBlock : Hash
        includedVotes : t -- set HashO
        leadershipProof : LeadershipProof
        payload : List Tx
        signature : Signature

open Block public

{-# COMPILE AGDA2HS Block #-}

Block⋆ = Block (set HashO)

postulate
  toHash : Block⋆ → Hash

postulate
  blEq : Relation.Binary.Rel Block⋆ 0ℓ
  blLt : Relation.Binary.Rel Block⋆ 0ℓ
  blIs : Relation.Binary.IsStrictTotalOrder blEq blLt

BlockO : StrictTotalOrder 0ℓ 0ℓ 0ℓ
BlockO = record {
  Carrier            = Block⋆ ;
  _≈_                = blEq ;
  _<_                = blLt ;
  isStrictTotalOrder = blIs }

postulate
  isValidBlock : Block⋆ -> Bool
