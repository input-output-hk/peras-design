
module Peras.Conformance.Soundness where

open import Haskell.Prelude
open import Haskell.Prim.Tuple
open import Haskell.Law.Equality

open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (NonZero; ℕ; _≡ᵇ_; _≥_; _≥?_; _>?_)
open import Data.Nat.Properties using (_≟_)
open import Data.Nat.DivMod
open import Data.Maybe using (maybe′; nothing; just)
open import Data.Product as P using (∃; Σ-syntax; ∃-syntax; proj₁; proj₂)
open import Data.Sum as S using (inj₁; inj₂; _⊎_; [_,_])
open import Relation.Nullary.Decidable using (Dec; yes; no)

open import Peras.Block
open import Peras.Chain
open import Peras.Crypto
open import Peras.Foreign using (checkSignedVote)
open import Peras.Numbering
open import Peras.Params
open import Peras.Util
open import Prelude.AssocList
open import Prelude.DecEq using (DecEq)
import Peras.SmallStep as SmallStep

import Peras.Conformance.Model as Model
open import Peras.Conformance.Params
open import Peras.Conformance.ProofPrelude

module _ ⦃ _ : Hashable (List Tx) ⦄
         ⦃ params     : Params ⦄
         ⦃ network    : Network ⦄
         ⦃ postulates : Postulates ⦄
         {S : Set} {adversarialState₀ : S}
         {txSelection : SlotNumber → PartyId → List Tx}
         {parties : Parties} -- TODO: use parties from blockTrees
    where

  open Params ⦃...⦄
  open Network ⦃...⦄

  open Model -- using (NodeModel; sutId)
  open Model.TreeInstance using (NodeModelTree)

  open SmallStep.Semantics {NodeModel} {NodeModelTree} {S} {adversarialState₀} {txSelection} {parties}
  open SmallStep.TreeType NodeModelTree renaming (allChains to chains; preferredChain to prefChain)

  open SmallStep.Message

  module Assumptions
           (let open Postulates postulates)

           -- Currently we allow anyone to vote
           (axiom-everyoneIsOnTheCommittee : ∀ {p slot prf} → IsCommitteeMember p slot prf)

           (axiom-checkVoteSignature : ∀ {vote} → checkSignedVote vote ≡ True → IsVoteSignature vote (signature vote))
         where

    modelParams : PerasParams
    modelParams = record
      { perasU = U
      ; perasA = A
      ; perasR = R
      ; perasL = L
      ; perasτ = τ
      ; perasB = B
      ; perasK = K
      ; perasT = 0 -- TODO: Missing from Params
      ; perasΔ = Δ
      }

    modelState : State → ℕ → NodeModel
    modelState s p = record
      { clock        = State.clock s
      ; protocol     = modelParams
      ; allChains    = maybe′ chains [] (State.blockTrees s ⁉ p)
      ; allVotes     = maybe′ votes  [] (State.blockTrees s ⁉ p)
      ; allSeenCerts = maybe′ certs  [] (State.blockTrees s ⁉ p)
      }

    sutVotesInStep : ∀ {s₀ s₁} → s₀ ↝ s₁ → List (SlotNumber × Vote)
    sutVotesInStep (Fetch _) = []
    sutVotesInStep {s₀ = s₀} (CreateVote _ (honest {p} {t} {M} {π} {σ} {b} _ _ _ _ _ _)) =
      case p ≟ sutId of λ where
        (yes _) → (State.clock s₀ , createVote (State.clock M) p π σ (Hashable.hash hashBlock b)) ∷ []
        (no _)  → []
    sutVotesInStep (CreateBlock _ _) = []
    sutVotesInStep (NextSlot _ _) = []
    sutVotesInStep (NextSlotNewRound _ _ _) = []

    sutVotesInTrace : ∀ {s₀ s₁} → s₀ ↝⋆ s₁ → List (SlotNumber × Vote)
    sutVotesInTrace ∎              = []
    sutVotesInTrace (step ↣ trace) = sutVotesInStep step ++ sutVotesInTrace trace

    params-equ : ∀ (s : State) (p : ℕ) (∃tree : ∃[ t ] (State.blockTrees s ⁉ p ≡ just t))
      → Params.B params ≡ perasB (protocol (proj₁ ∃tree))
    params-equ s p ∃tree = {!!}

    pref-equ : ∀ (s : State) (p : ℕ) (∃tree : ∃[ t ] (State.blockTrees s ⁉ p ≡ just t))
      → pref (modelState s p) ≡ prefChain (proj₁ ∃tree)
    pref-equ s p ∃tree rewrite params-equ s p ∃tree = {!refl!}

    certS-equ : ∀ (s : State) (p : ℕ) (∃tree : ∃[ t ] (State.blockTrees s ⁉ p ≡ just t))
      → certS (modelState s p) ≡ latestCertOnChain (proj₁ ∃tree)
    certS-equ s p ∃tree rewrite pref-equ s p ∃tree = {!!}

    vr-1a⇒VotingRule-1A : ∀ (s : State) (p : ℕ) (∃tree : ∃[ t ] (State.blockTrees s ⁉ p ≡ just t))
      → let
          m = modelState s p
          cert' = maximumBy cert₀ (comparing round) (allSeenCerts m)
        in
          nextRound (round cert') ≡ rFromSlot m
      → VotingRule-1A (v-round (clock m)) (proj₁ ∃tree)
    vr-1a⇒VotingRule-1A s p ∃tree x
        rewrite suc-definition {n = getRoundNumber (round (latestCert cert₀ (allSeenCerts (modelState s p))))}
        rewrite (proj₂ ∃tree)
      = cong getRoundNumber (sym x)

    vr-1b⇒VotingRule-1B : ∀ (s : State) (p : ℕ) (∃tree : ∃[ t ] (State.blockTrees s ⁉ p ≡ just t))
      → let m = modelState s p
        in Vr1B m
      → VotingRule-1B (clock m) (proj₁ ∃tree)
    vr-1b⇒VotingRule-1B s p ∃tree x = {!!}

    vr-2a⇒VotingRule-2A : ∀ (s : State) (p : ℕ) (∃tree : ∃[ t ] (State.blockTrees s ⁉ p ≡ just t))
      → let
          m = modelState s p
          cert' = maximumBy cert₀ (comparing round) (allSeenCerts m)
        in
          getRoundNumber (rFromSlot m) ≥ getRoundNumber (round cert') + perasR (protocol m)
      → VotingRule-2A (v-round (clock m)) (proj₁ ∃tree)
    vr-2a⇒VotingRule-2A _ _ ∃tree x rewrite (proj₂ ∃tree) = x

    vr-2b⇒VotingRule-2B : ∀ (s : State) (p : ℕ) (∃tree : ∃[ t ] (State.blockTrees s ⁉ p ≡ just t))
      → let
          m = modelState s p
        in
            (getRoundNumber (rFromSlot m) Data.Nat.> getRoundNumber (round (certS m)))
          P.× (mod (getRoundNumber (rFromSlot m)) (perasK (protocol m)) ≡ mod (getRoundNumber (round (certS m))) (perasK (protocol m)))
      → VotingRule-2B (v-round (clock m)) (proj₁ ∃tree)
    vr-2b⇒VotingRule-2B s p ∃tree ( x P., y )
      rewrite sym (certS-equ s p ∃tree)
      = x P., y

    -- Preconditions ---

    record NewChainPreconditions (s : State) (block : Block) (rest : Chain) : Set where
      slot = State.clock s
      r    = v-round slot
      field
        {tree}         : NodeModel
        creatorExists  : State.blockTrees s ⁉ (creatorId block) ≡ just tree
        blockExists    : BlockSelection (State.clock s) tree ≡ just block
        validHead      : block ≡ createBlock slot (creatorId block) (leadershipProof block) (signature block) tree
        validRest      : rest ≡ prefChain tree
        validChain     : ValidChain (block ∷ rest)

    record NewVotePreconditions (s : State) (vote : Vote) : Set where
      slot = State.clock s
      r    = v-round slot
      σ    = signature vote
      field
        {tree}         : NodeModel
        {block}        : Block
        creatorExists  : State.blockTrees s ⁉ (creatorId vote) ≡ just tree
        blockExists    : BlockSelection (State.clock s) tree ≡ just block
        blockVote      : blockHash vote ≡ Hashable.hash hashBlock block
        startOfRound   : StartOfRound slot r
        validSignature : IsVoteSignature vote σ
        correctVote    : vote ≡ createVote slot (creatorId vote) (proofM vote) σ (blockHash vote)
        validVote      : VotingRule slot tree

      validSignature' : IsVoteSignature (createVote slot (creatorId vote) (proofM vote) σ (blockHash vote)) σ
      validSignature' with valid ← validSignature rewrite correctVote = valid

      blockExists' : BlockSelection (State.clock s) tree ≡ just
          record block { signature = MkSignature (hashBytes (blockHash vote)) }
      blockExists' with b ← blockExists rewrite blockVote = b

    record Invariant (s : State) : Set where
      field
        invFetched : Fetched s
        hasTree : ∀ (p : ℕ) → ∃[ t ] (State.blockTrees s ⁉ p ≡ just t)

    open Invariant

    @0 newChain-preconditions : ∀ {vs ms₁} s tip rest
                          → Invariant s
                          → transition (modelState s sutId) (NewChain (tip ∷ rest)) ≡ Just (vs , ms₁)
                          → NewChainPreconditions s tip rest
    newChain-preconditions s chain inv prf = {!!}

    @0 newVote-preconditions : ∀ {vs ms₁} s vote
                          → Invariant s
                          → transition (modelState s sutId) (NewVote vote) ≡ Just (vs , ms₁)
                          → NewVotePreconditions s vote
    newVote-preconditions s vote inv prf
      with mod (getSlotNumber (State.clock s)) (Params.U params) == 0 in isSlotZero
         | checkSignedVote vote in checkedSig
         -- | isYes (checkVotingRules (modelState s (creatorId vote))) in checkedVRs
    newVote-preconditions s vote inv refl | True | True =
      record
      { tree            = proj₁ (hasTree inv (creatorId vote)) -- we don't track the block trees for the environment nodes in the test model!
      ; block           = {!!}
      ; creatorExists   = proj₂ (hasTree inv (creatorId vote)) -- maybe invariant that everyone has the same blockTree?
      ; blockExists     = {!!}
      ; blockVote       = refl
      ; startOfRound    = lem-divMod _ _ (eqℕ-sound isSlotZero)
      ; validSignature  = axiom-checkVoteSignature checkedSig
      ; correctVote     = {!!}    -- this needs to go in the `transition` (checking preferred chains and L etc)
      ; validVote       = {!!}
      {-
        let
          witness = toWitness (isYes≡True⇒TTrue checkedVRs )
          f₁ = vr-1a⇒VotingRule-1A  s (creatorId vote) (hasTree inv (creatorId vote))
          f₂ = vr-1b⇒VotingRule-1B  s (creatorId vote) (hasTree inv (creatorId vote))
          f₃ = vr-2a⇒VotingRule-2A  s (creatorId vote) (hasTree inv (creatorId vote))
          f₄ = vr-2b⇒VotingRule-2B  s (creatorId vote) (hasTree inv (creatorId vote))
        in
          S.map (P.map f₁ f₂) (P.map f₃ f₄) witness -- need to check the VR logic also for environment votes
       -}
      }

    -- Soundness --

    -- Soundness states that transitions in the test specification relate to traces
    -- in the the small step semantics as follows:
    --
    --
    -- test specification:    (ms₀ : NodeModel)    transition    (ms₁ : NodeModel)
    --
    --                          ↑                                  ↑
    --
    -- small step semantics:  (s₀ : State)             ↝⋆        (s₁ : State)
    --
    --
    -- The small step semantics are instantiated with a block-tree provided by the
    -- test specification

    record Soundness (s₀ : State) (ms₁ : NodeModel) (vs : List (SlotNumber × Vote)) : Set where
      field
        s₁          : State
        invariant₀  : Invariant s₀
        invariant₁  : Invariant s₁
        trace       : s₀ ↝⋆ s₁
        s₁-agrees   : modelState s₁ sutId ≡ ms₁
        votes-agree : sutVotesInTrace trace ≡ vs

    @0 soundness : ∀ {ms₁ vs} (s₀ : State) (a : EnvAction)
              → Invariant s₀
              → transition (modelState s₀ sutId) a ≡ Just (vs , ms₁)
              → Soundness s₀ ms₁ (map (State.clock s₀ ,_) vs)
    soundness s₀ Tick inv prf =
      record
        { s₁ = {!!}
        ; invariant₀ = inv
        ; invariant₁ = {!!}
        ; trace = {!!}
        ; s₁-agrees = {!!}
        ; votes-agree = {!!}
        }
    soundness s₀ (NewChain []) inv prf =
      record
        { s₁ = {!!}
        ; invariant₀ = inv
        ; invariant₁ = {!!}
        ; trace = {!!}
        ; s₁-agrees = {!!}
        ; votes-agree = {!!}
        }
    soundness s₀ (NewChain chain@(b ∷ bs)) inv prf =
      let
        pre = newChain-preconditions s₀ b bs inv prf
        open NewChainPreconditions pre
      in
        record
          { s₁ = {!!} -- ChainMsg chain , fzero , {!!} , newChain tree chain ⇑ s₀
          ; invariant₀ = inv
          ; invariant₁ = {!!}
          ; trace = {!!} -- CreateBlock (invFetched inv) (honest creatorExists {!validChain!}) ↣ ∎
          ; s₁-agrees = {!!}
          ; votes-agree = {!!} -- refl
          }
    soundness s₀ (NewVote vote) inv prf =
      let
        pre = newVote-preconditions s₀ vote inv prf
        open NewVotePreconditions pre
      in
        record
          { s₁          = let v = record vote { votingRound = v-round slot } -- TODO: is this necessary? See correctVote
                          in VoteMsg v , fzero , creatorId v , addVote tree v ⇑ s₀
          ; invariant₀  = inv
          ; invariant₁  = {!!}
          ; trace       = CreateVote (invFetched inv)
                            (honest {σ = Vote.signature vote}
                              blockExists'
                              creatorExists
                              validSignature'
                              startOfRound
                              axiom-everyoneIsOnTheCommittee
                              validVote
                            )
                          -- TODO: also deliver the vote message to establish Fetched s₁
                          ↣ ∎
          ; s₁-agrees   = {!!}
          ; votes-agree = {!!}
          }
