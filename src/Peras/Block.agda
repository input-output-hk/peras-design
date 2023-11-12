module Peras.Block where
{-# FOREIGN AGDA2HS
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
#-}
{-# FOREIGN AGDA2HS
import Data.Word (Word64)
import qualified Data.Set as S (Set)
import Data.ByteString (ByteString)
type SET = S.Set
#-}

postulate SET : Set → Set

open import Agda.Builtin.Word
open import Data.Bool
open import Data.List

open import Peras.Crypto
-- import Peras.Crypto (Hash, LeadershipProof, Signature, VerificationKey)

record PartyId : Set where
  field vkey : VerificationKey
open PartyId public
{-# COMPILE AGDA2HS PartyId newtype deriving (Eq, Show, Ord) #-}
-- newtype strategy not supported

record Tx : Set where
  field tx : ByteString
open Tx public
{-# COMPILE AGDA2HS Tx newtype deriving (Eq, Show) #-}
-- newtype strategy not supported

record Block : Set where
  field slotNumber : Word64
        blockHeight : Word64
        creatorId : PartyId
        parentBlock : Hash
        includedVotes : SET Hash
        leadershipProof : LeadershipProof
        payload : List Tx
        signature : Signature
open Block public      
{-# COMPILE AGDA2HS Block deriving (Eq, Show) #-}
-- stock strategy not supported

postulate isValidBlock : Block -> Bool
{-# COMPILE AGDA2HS isValidBlock #-}
