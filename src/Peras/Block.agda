module Peras.Block where

open import Level
open import Agda.Builtin.Word
open import Data.Bool
open import Data.List
open import Data.Tree.AVL.Sets renaming (⟨Set⟩ to set)
open import Relation.Binary using (StrictTotalOrder)

open import Peras.Crypto

record PartyId : Set where
  constructor mkPartyId
  field vkey : VerificationKey

record Tx : Set where
  field tx : ByteString

Slot = Word64

record Block : Set where
  field slotNumber : Slot
        -- blockHeight : Word64
        creatorId : PartyId
        parentBlock : Hash
        includedVotes : set HashO
        leadershipProof : LeadershipProof
        payload : List Tx
        signature : Signature  

postulate
  blEq : Relation.Binary.Rel Block zero
  blLt : Relation.Binary.Rel Block zero
  blIs : Relation.Binary.IsStrictTotalOrder blEq blLt

BlockO : StrictTotalOrder zero zero zero
BlockO = record {
  Carrier            = Block ;
  _≈_                = blEq ;
  _<_                = blLt ;
  isStrictTotalOrder = blIs }

postulate
  isValidBlock : Block -> Bool

