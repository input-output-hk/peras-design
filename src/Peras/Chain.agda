module Peras.Chain where

open import Agda.Builtin.Word
open import Data.Bool
open import Data.Nat using (ℕ)
open import Level
open import Data.Tree.AVL.Sets renaming (⟨Set⟩ to set) hiding (foldr)
open import Relation.Binary using (StrictTotalOrder)

open import Peras.Crypto
open import Peras.Block hiding (ByteString; emptyBS)

record RoundNumber : Set where
  field roundNumber : ℕ

record Vote msg : Set where
  constructor vote
  field roundNumber              : RoundNumber
        creatorId                : PartyId
        committeeMembershipProof : MembershipProof
        blockHash                : msg
        signature                : Signature

postulate
  vblEq : Relation.Binary.Rel (Vote Block⋆) 0ℓ
  vblLt : Relation.Binary.Rel (Vote Block⋆) 0ℓ
  vblIs : Relation.Binary.IsStrictTotalOrder vblEq vblLt

VoteBlockO : StrictTotalOrder 0ℓ 0ℓ 0ℓ
VoteBlockO = record {
  Carrier            = Vote Block⋆ ;
  _≈_                = vblEq ;
  _<_                = vblLt ;
  isStrictTotalOrder = vblIs }

toSignable : ∀{msg} → Vote msg -> ByteString
toSignable _ = emptyBS -- const ""

postulate
  makeVote : ∀{msg} → RoundNumber -> PartyId -> msg -> Vote msg

-- | A vote is valid if the committee-membership proof and the signature are valid.

isValid : ∀{msg} → Vote msg -> Bool
isValid v@(vote _ (MkPartyId vkey) committeeMembershipProof _ signature) =
  isCommitteeMember vkey committeeMembershipProof
    ∧ verify vkey signature (toSignable v)

record Chain⋆ : Set where
  constructor MkChain
  field blocks : set BlockO
        tip : Block⋆ -- The tip of this chain, must be a member of `blocks`
        votes : set VoteBlockO -- The set of "pending" votes, eg. which have not been included in a `Block`.

data Chain t : Set where
  Genesis : Chain t
  Cons : Block t → Chain t → Chain t

open Chain public

{-# COMPILE AGDA2HS Chain #-}

-- Chain⋆ = Chain (set BlockO)

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


postulate
  verifyLeadershipProof : Block⋆ → Bool

  properlyLinked : Chain⋆ → Bool
  decreasingSlots : Chain⋆ → Bool

{-
correctBlocks : Chain → Bool
correctBlocks (MkChain blocks _ _) =
  let bs = toList BlockO blocks
  in all verifyLeadershipProof bs
-}

data ValidChain : Chain⋆ → Set where

  -- FIXME: constructors

{-
postulate
  isValidChain : Chain⋆ -> Bool
-}
