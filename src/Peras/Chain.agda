module Peras.Chain where

open import Agda.Builtin.Word
open import Data.Bool
open import Data.List as List using (List; all; foldr)
open import Data.Maybe
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



module _ {T : Set} where

  open import Data.List.Relation.Binary.Sublist.Propositional

  record TreeType : Set where

    field
      tree0 : T
      extendTree : T → Block → T
      allBlocks : T → List Block
      bestChain : Slot → T → Chain

  open TreeType

  record LocalState : Set where
    constructor ⟨_,_⟩
    field
      id : PartyId
      tt : T

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
    constructor ⟪_,_,_,_,_⟫
    field
      slot : Slot
      progress : Progress
      stateMap : PartyId → Maybe LocalState
      messages : List Message
      execution-order : List PartyId

  open GlobalState

  postulate
    N₀ : GlobalState

    party_bake_step_world : PartyId → GlobalState → GlobalState
    party_rcv_step_world : PartyId → GlobalState → GlobalState
    incrementSlot : Slot → Slot
    permParties : List PartyId → List PartyId
    permMessages : List Message → List Message

  data _↝_ : GlobalState → GlobalState → Set where

    Deliver : ∀ {s sm ms ps}
      → ⟪ s , Ready , sm , ms , ps ⟫ ↝
        let gs = List.foldr party_rcv_step_world ⟪ s , Ready , sm , ms , ps ⟫ ps
         in record gs { progress = Delivered }

    Bake : ∀ {s sm ms ps}
      → ⟪ s , Delivered , sm , ms , ps ⟫ ↝
        let gs = List.foldr party_bake_step_world ⟪ s , Delivered , sm , ms , ps ⟫ ps
         in record gs { progress = Delivered }

    NextRound : ∀ {s sm ms ps}
      → ⟪ s , Baked , sm , ms , ps ⟫ ↝ ⟪ incrementSlot s , Ready , sm , ms , ps ⟫

    PermParties : ∀ {s p sm ms ps}
      → ⟪ s , p , sm , ms , ps ⟫ ↝ ⟪ s , p , sm , ms , permParties ps ⟫

    PermMsgs : ∀ {s p sm ms ps}
      → ⟪ s , p , sm , ms , ps ⟫ ↝ ⟪ s , p , sm , permMessages ms , ps ⟫

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

  -- knowledge propagation
  lemma1 : ∀ {N₁ N₂ : GlobalState}
    → {p₁ p₂ : PartyId}
    → {tt₁ tt₂ : TreeType}
    → {t₁ t₂ : T}
    → N₀ ↝⋆ N₁
    → N₁ ↝⋆ N₂
    → progress N₁ ≡ Ready
    → progress N₂ ≡ Delivered
    → stateMap N₁ p₁ ≡ just ⟨ p₁ , t₁ ⟩
    → stateMap N₂ p₂ ≡ just ⟨ p₂ , t₂ ⟩
    → slot N₁ ≡ slot N₂
    → allBlocks tt₁ t₁ ⊆ allBlocks tt₁ t₂

  {- From the paper:

  Proof sketch. Our main observation is that at any point in time a block is in the tree of p1, it is
  either also already in p2’s tree or to be delivered at the next delivery transition.

  Blocks can be added when an honest party wins the right to bake a block, in which case they will immediately
  send the block to all other parties and thus fulfill the invariant, or they can be added by an
  adversary and thereby delivered to an honest party by a delivery event, in which case it will be
  delivered to all other honest parties in the following delivery slot (by our network assumption).

  This is in particular true when p1 and p2 is at Ready, which means that after the delivery
  transition p2 will know all the blocks that p1 knew before.

  -}

  lemma1 x (⟪ _ , Ready , _ , _ , _ ⟫ ↝⟨ Deliver ⟩ x₂) refl refl x₃ x₄ refl = {!!}
  lemma1 x (⟪ _ , Ready , _ , _ , _ ⟫ ↝⟨ PermParties ⟩ x₂) refl refl x₃ x₄ refl = {!!}
  lemma1 x (⟪ _ , Ready , _ , _ , _ ⟫ ↝⟨ PermMsgs ⟩ x₂) refl refl x₃ x₄ refl = {!!}
