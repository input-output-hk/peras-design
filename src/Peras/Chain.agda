{-

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-} 


module Peras.Chain where

{-
import Data.ByteString (ByteString)
import Data.Set (Set)
import Data.Word (Word64)
import Peras.Block (Block, PartyId (..))
import Peras.Crypto (MembershipProof, Signature, isCommitteeMember, verify)
-}

open import Agda.Builtin.Word
open import Data.Bool
open import Level
open import Data.Tree.AVL.Sets renaming (⟨Set⟩ to set)
open import Relation.Binary using (StrictTotalOrder)

open import Peras.Crypto
open import Peras.Block

record RoundNumber : Set where
  field roundNumber : Word64
--   deriving newtype (Eq, Show, Ord)


record Vote msg : Set where
  constructor vote
  field roundNumber              : RoundNumber
        creatorId                : PartyId
        committeeMembershipProof : MembershipProof
        blockHash                : msg
        signature                : Signature
--  deriving stock (Eq, Show, Ord)

postulate vblEq : Relation.Binary.Rel (Vote Block) zero
          vblLt : Relation.Binary.Rel (Vote Block) zero
          vblIs : Relation.Binary.IsStrictTotalOrder vblEq vblLt

VoteBlockO : StrictTotalOrder zero zero zero
VoteBlockO = record {
  Carrier            = (Vote Block) ;
  _≈_                = vblEq ;
  _<_                = vblLt ;
  isStrictTotalOrder = vblIs }

toSignable : ∀{msg} → Vote msg -> ByteString
toSignable _ = emptyBS -- const ""

postulate makeVote : ∀{msg} → RoundNumber -> PartyId -> msg -> Vote msg

-- | A vote is valid if the committee-membership proof and the signature are valid.

isValid : ∀{msg} → Vote msg -> Bool
isValid v@(vote _ (mkPartyId vkey) committeeMembershipProof _ signature) =
  isCommitteeMember vkey committeeMembershipProof
    ∧ verify vkey signature (toSignable v)

record Chain : Set where
  constructor chain
  field blocks : set BlockO
        tip : Block
  -- ^ The tip of this chain, must be a member of `blocks`.
        votes : set VoteBlockO
  -- ^ The set of "pending" votes, eg. which have not been included in
  --   a `Block`.

  -- deriving stock (Eq, Show)

-- | Chain validity
--
-- A chain is valid iff:
-- * the blocks (ignoring the vote hashes) form a valid Praos chain,
-- * all votes:
--      * are referenced by a unique block with a slot number $s$
--        strictly larger than the slot number corresponding to the
--        vote’s round number r (i.e., r*T < s),
--      * point to a block on the chain at least L slots in the past
--        (i.e., to a block with slot number s < r*T - L), and
-- * it contains no vote equivocations (i.e., multiple votes by the
--   same party for the same round).
--
-- TODO: expressing those conditions directly would be very expensive,
-- it's more efficient to enforce them whenever the chain is extended.

postulate isValidChain : Chain -> Bool

