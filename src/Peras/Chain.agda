module Peras.Chain where

open import Agda.Builtin.Word
open import Data.Bool
open import Data.List as List using (List; all; foldr)
open import Level
open import Data.Tree.AVL.Sets renaming (⟨Set⟩ to set)
open import Relation.Unary using (Pred)
open import Relation.Binary using (StrictTotalOrder)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)

open import Peras.Crypto
open import Peras.Block

record RoundNumber : Set where
  field roundNumber : Word64

record Vote msg : Set where
  constructor vote
  field roundNumber              : RoundNumber
        creatorId                : PartyId
        committeeMembershipProof : MembershipProof
        blockHash                : msg
        signature                : Signature

postulate
  vblEq : Relation.Binary.Rel (Vote Block) zero
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

postulate
  makeVote : ∀{msg} → RoundNumber -> PartyId -> msg -> Vote msg

-- | A vote is valid if the committee-membership proof and the signature are valid.

isValid : ∀{msg} → Vote msg -> Bool
isValid v@(vote _ (mkPartyId vkey) committeeMembershipProof _ signature) =
  isCommitteeMember vkey committeeMembershipProof
    ∧ verify vkey signature (toSignable v)

record Chain : Set where
  constructor chain
  field blocks : set BlockO
        tip : Block -- The tip of this chain, must be a member of `blocks`
        votes : set VoteBlockO -- The set of "pending" votes, eg. which have not been included in a `Block`.




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
  verifyLeadershipProof : Block → Bool
  
  properlyLinked : Chain → Bool
  decreasingSlots : Chain → Bool

correctBlocks : Chain → Bool
correctBlocks (chain blocks _ _) =
  let bs = toList BlockO blocks
  in all verifyLeadershipProof bs

postulate
  isValidChain : Chain -> Bool


{-
  Formalizing Nakamoto-Style Proof of Stake
  Søren Eller Thomsen and Bas Spitters
-}

-- progress

data Progress : Set where

  Ready : Progress
  Delivered : Progress
  Baked : Progress

record Message : Set where
  constructor mkMessage
  field
    msg : ByteString

-- global state

record GlobalState : Set where
  constructor ⟪_,_,_,_⟫ 
  field
    slot : Slot
    progress : Progress
    messages : List Message
    execution-order : List PartyId

open GlobalState

postulate
  party_bake_step_world : PartyId → GlobalState → GlobalState
  party_rcv_step_world : PartyId → GlobalState → GlobalState
  incrementSlot : Slot → Slot
  permParties : List PartyId → List PartyId
  permMessages : List Message → List Message

data _↝_ : GlobalState → GlobalState → Set where

  Deliver : ∀ {s ms ps}
    → ⟪ s , Ready , ms , ps ⟫ ↝
      let gs = List.foldr party_rcv_step_world ⟪ s , Ready , ms , ps ⟫ ps
       in record gs { progress = Delivered }

  Bake : ∀ {s ms ps}
    → ⟪ s , Delivered , ms , ps ⟫ ↝
      let gs = List.foldr party_bake_step_world ⟪ s , Delivered , ms , ps ⟫ ps
       in record gs { progress = Delivered }

  NextRound : ∀ {s ms ps}
    → ⟪ s , Baked , ms , ps ⟫ ↝ ⟪ incrementSlot s , Ready , ms , ps ⟫
    
  PermParties : ∀ {s p ms ps}
    → ⟪ s , p , ms , ps ⟫ ↝ ⟪ s , p , ms , permParties ps ⟫
    
  PermMsgs : ∀ {s p ms ps}
    → ⟪ s , p , ms , ps ⟫ ↝ ⟪ s , p , permMessages ms , ps ⟫

-- reflexive, transitive closure (which is big-step in the paper)

infix  2 _↝⋆_
infixr 2 _↝⟨_⟩_
infix  3 _∎

data _↝⋆_ : GlobalState → GlobalState → Set where

  _∎ : ∀ M
      -------
    → M ↝⋆ M

  _↝⟨_⟩_ : ∀ L {M N}
    → L ↝ M
    → M ↝⋆ N
      ------
    → L ↝⋆ N

{-
-- knowledge propagation
lemma_1 : ∀ (N₀ N₁ N₂ : GlobalState)
  → (p₁ p₂ : PartyId)
  → Nₒ ↝⋆ N₁
  → N₁ ↝⋆ N₂
  → progress N₁ ≡ Ready
  → progress N₂ ≡ Delivered
  → allBlocks t₁ ⊂ allBlocks t₂
-}
