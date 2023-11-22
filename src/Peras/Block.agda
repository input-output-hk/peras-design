module Peras.Block where
{-
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Peras.Block where

import Data.Word (Word64)
import Peras.Crypto (Hash, LeadershipProof, Signature, VerificationKey)
import Data.Set (Set)
import Data.ByteString (ByteString)
-}

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
--   deriving newtype (Eq, Show, Ord)

record Tx : Set where
  field tx : ByteString
--  deriving newtype (Eq, Show)


record Block : Set where
  field slotNumber : Word64
        blockHeight : Word64
        creatorId : PartyId
        parentBlock : Hash
        includedVotes : set HashO
        leadershipProof : LeadershipProof
        payload : List Tx
        signature : Signature  
-- deriving stock (Eq, Show)

postulate blEq : Relation.Binary.Rel Block zero
          blLt : Relation.Binary.Rel Block zero
          blIs : Relation.Binary.IsStrictTotalOrder blEq blLt

BlockO : StrictTotalOrder zero zero zero
BlockO = record {
  Carrier            = Block ;
  _≈_                = blEq ;
  _<_                = blLt ;
  isStrictTotalOrder = blIs }

postulate isValidBlock : Block -> Bool

