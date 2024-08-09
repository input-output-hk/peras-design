
module Peras.Conformance.Soundness where

open import Haskell.Prelude
open import Haskell.Prim.Tuple
open import Haskell.Law.Equality

open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (NonZero; ℕ; _≡ᵇ_; _≥_; _≥?_; _>?_)
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Maybe using (maybe′; nothing; just)
open import Data.Product as P using (∃; Σ-syntax; ∃-syntax; proj₁; proj₂)
open import Data.Sum as S using (inj₁; inj₂; _⊎_; [_,_])
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≢_)

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
         {parties : Parties}
    where

  open Params ⦃...⦄
  open Network ⦃...⦄

  open Model
  open Model.TreeInstance using (NodeModelTree'; isTreeType)

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

  Tree = NodeModelTree' modelParams

  open SmallStep.Semantics {NodeModel} {Tree} {S} {adversarialState₀} {txSelection} {parties}
  open SmallStep.TreeType Tree renaming (allChains to chains; preferredChain to prefChain)
  open SmallStep.IsTreeType

  open SmallStep.Message

  module Assumptions
           (let open Postulates postulates)

           -- Currently we allow anyone to vote
           (axiom-everyoneIsOnTheCommittee : ∀ {p slot prf} → IsCommitteeMember p slot prf)

           (axiom-checkVoteSignature : ∀ {vote} → checkSignedVote vote ≡ True → IsVoteSignature vote (signature vote))
         where

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
        (yes _) → (State.clock s₀ , createVote (State.clock M) p π σ b) ∷ []
        (no _)  → []
    sutVotesInStep (CreateBlock _ _) = []
    sutVotesInStep (NextSlot _ _) = []
    sutVotesInStep (NextSlotNewRound _ _ _) = []

    sutVotesInTrace : ∀ {s₀ s₁} → s₀ ↝⋆ s₁ → List (SlotNumber × Vote)
    sutVotesInTrace ∎              = []
    sutVotesInTrace (step ↣ trace) = sutVotesInStep step ++ sutVotesInTrace trace

    -- TODO: isomorphism of Maybe and Data.Maybe.Maybe
    from-maybe : ∀ {x : Set} → Maybe x → Data.Maybe.Maybe x
    from-maybe (Just x) = just x
    from-maybe Nothing = nothing

{-
    modelState-tree-eq : ∀ (s : State) (p : ℕ) (∃tree : ∃[ t ] (State.blockTrees s ⁉ p ≡ just t) P.× State.clock s ≡ clock t)
      → modelState s p ≡ proj₁ ∃tree
    modelState-tree-eq s p (tree P., (prf P., refl)) rewrite prf = {!refl!}
-}

    cert⋆-equ : ∀ (s : State) (p : ℕ) (∃tree : ∃[ t ] (State.blockTrees s ⁉ p ≡ just t))
      → certS (modelState s p) ≡ latestCertOnChain (proj₁ ∃tree)
    cert⋆-equ s p ∃tree = {!!} -- TODO: agda2hs vs. stdlib, otherwise refl

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
      rewrite sym (cert⋆-equ s p ∃tree)
      = x P., y

    -- Preconditions ---

    record TickPreconditions (s : State) : Set where
      slot = State.clock s

      field
        {tree}         : NodeModel
        {block}        : Block
        blockExists    : BlockSelection slot tree ≡ just block
        validVote      : VotingRule slot tree

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

        validHashes    : tipHash (is-TreeType .valid tree) ≡ parentBlock block

      validChain' : ValidChain (createBlock slot (creatorId block) (leadershipProof block) (signature block) tree ∷ prefChain tree)
      validChain' with c ← validChain rewrite validHead rewrite validRest = c

    record NewVotePreconditions (s : State) (vote : Vote) (ms : NodeModel) : Set where
      slot = State.clock s
      r    = v-round slot
      σ    = signature vote
      field
        {tree}         : NodeModel
        creatorExists  : State.blockTrees s ⁉ (creatorId vote) ≡ just tree
        validBlockHash : hash' (BlockSelection (State.clock s) tree) ≡ blockHash vote
        startOfRound   : StartOfRound slot r
        validSignature : IsVoteSignature vote σ
        correctVote    : vote ≡ createVote slot (creatorId vote) (proofM vote) σ (blockHash vote)
        validVote      : VotingRule slot tree
        clocksAgree    : State.clock s ≡ clock ms
        notFromSut     : creatorId vote ≢ sutId

      validSignature' : IsVoteSignature (createVote slot (creatorId vote) (proofM vote) σ (blockHash vote)) σ
      validSignature' with v ← validSignature rewrite correctVote = v

    record Invariant (s : State) : Set where
      field
        invFetched : Fetched s
        sutTree : ∃[ t ] (State.blockTrees s ⁉ sutId ≡ just t)
        equalTree : ∀ (p : ℕ) → State.blockTrees s ⁉ sutId ≡ State.blockTrees s ⁉ p
        -- eqt : Any (λ { bt → (just (proj₂ bt)) ≡ State.blockTrees s ⁉ sutId }) (State.blockTrees s)

    open Invariant

    @0 tick-preconditions : ∀ {vs ms₁} s
                          → Invariant s
                          → transition (modelState s sutId) Tick ≡ Just (vs , ms₁)
                          → TickPreconditions s
    tick-preconditions s inv refl
      with isYes (checkVotingRules (modelState s sutId)) in checkedVRs
    ... | True = record
      { tree        = proj₁ (sutTree inv)
      ; block       = {!!}
      ; blockExists = {!!}
      ; validVote   =
        let
          witness = toWitness (isYes≡True⇒TTrue checkedVRs)
          f₁ = vr-1a⇒VotingRule-1A s sutId (sutTree inv)
          f₂ = vr-1b⇒VotingRule-1B s sutId (sutTree inv)
          f₃ = vr-2a⇒VotingRule-2A s sutId (sutTree inv)
          f₄ = vr-2b⇒VotingRule-2B s sutId (sutTree inv)
        in
          S.map (P.map f₁ f₂) (P.map f₃ f₄) witness
      }

    @0 newChain-preconditions : ∀ {vs ms₁} s tip rest
                          → Invariant s
                          → transition (modelState s sutId) (NewChain (tip ∷ rest)) ≡ Just (vs , ms₁)
                          → NewChainPreconditions s tip rest
    newChain-preconditions s tip rest inv prf = {!!}

    @0 newVote-preconditions : ∀ {vs ms₁} s vote
                          → Invariant s
                          → transition (modelState s sutId) (NewVote vote) ≡ Just (vs , ms₁)
                          → NewVotePreconditions s vote ms₁
    newVote-preconditions s vote inv prf
      with mod (getSlotNumber (State.clock s)) (Params.U params) == 0 in isSlotZero
         | checkSignedVote vote in checkedSig
         | checkVoteNotFromSut vote in checkedSut
         | isYes (checkVotingRules (modelState s sutId)) in checkedVRs
         | hashMaybeBlock (votingBlock (modelState s sutId)) == blockHash vote in isValidBlockHash
    newVote-preconditions s vote inv refl | True | True | True | True | True =
      let
        slot = State.clock s
        treeₛ = sutTree inv
        eqt = equalTree inv (creatorId vote)
      in
        record
          { tree            = proj₁ treeₛ -- we don't track the block trees for the environment nodes in the test model!
          ; creatorExists   = trans (sym eqt) (proj₂ treeₛ)    -- maybe invariant that everyone has the same blockTree?
          ; validBlockHash  = {!!} -- this needs to go in the `transition` (checking preferred chains and L etc)
          ; startOfRound    = lem-divMod _ _ (eqℕ-sound isSlotZero)
          ; validSignature  = axiom-checkVoteSignature checkedSig
          ; correctVote     = {!refl!}
          ; validVote       =             -- need to check the VR logic also for environment votes
            let
              witness = toWitness (isYes≡True⇒TTrue checkedVRs)
              f₁ = vr-1a⇒VotingRule-1A s sutId treeₛ
              f₂ = vr-1b⇒VotingRule-1B s sutId treeₛ
              f₃ = vr-2a⇒VotingRule-2A s sutId treeₛ
              f₄ = vr-2b⇒VotingRule-2B s sutId treeₛ
            in
              S.map (P.map f₁ f₂) (P.map f₃ f₄) witness
            ; clocksAgree = refl
            ; notFromSut = not-eqℕ-sound checkedSut
          }

        where
          eq-hash : ∀ {x} → hashMaybeBlock x ≡ hash' (from-maybe x)
          eq-hash {Nothing} = refl
          eq-hash {Just _} = refl

          checkBlockSelection : from-maybe (votingBlock (modelState s sutId)) ≡ BlockSelection (State.clock s) (proj₁ (sutTree inv))
          checkBlockSelection = {!!}

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
    soundness s₀ (NewChain chain@(block ∷ bs)) inv prf =
      let
        pre = newChain-preconditions s₀ block bs inv prf
        open NewChainPreconditions pre
      in
        record
          { s₁          = let b = createBlock (State.clock s₀) (creatorId block) (leadershipProof block) (signature block) tree
                          in ChainMsg (b ∷ prefChain tree) , fzero , creatorId b , newChain tree (b ∷ prefChain tree) ⇑ s₀
          ; invariant₀  = inv
          ; invariant₁  = {!!}
          ; trace       = CreateBlock
                            (invFetched inv)
                            (honest
                              creatorExists
                              validChain'
                            )
                          ↣ ∎
          ; s₁-agrees   = {!!} -- refl
          ; votes-agree = {!!} -- refl
          }

    soundness {ms₁} {vs} s₀ (NewVote vote) inv prf =
        record
          { s₁          = s₁
          ; invariant₀  = inv
          ; invariant₁  = {!!}
          ; trace       = trace
          ; s₁-agrees   = s₁-agrees
          ; votes-agree = votes-agree
          }
      where
        pre = newVote-preconditions s₀ vote inv prf
        open NewVotePreconditions pre

        v : Vote
        v = record vote { votingRound = v-round slot }
        -- TODO: rewrite rather than overwrite
        -- v with v' ← vote rewrite startOfRound = v'

        s₁ : State
        s₁ = VoteMsg v , fzero , creatorId vote , addVote tree v ⇑ s₀

        trace : s₀ ↝⋆ s₁
        trace = CreateVote (invFetched inv)
                            (honest {σ = Vote.signature vote}
                              validBlockHash
                              creatorExists
                              validSignature'
                              startOfRound
                              axiom-everyoneIsOnTheCommittee
                              validVote
                            )
                          -- TODO: also deliver the vote message to establish Fetched s₁
                          ↣ ∎

        s₁-agrees : modelState s₁ sutId ≡ ms₁
        s₁-agrees = {!refl!} -- TODO: rewrite clocksAgree

        votes-agree : sutVotesInTrace trace ≡ map (State.clock s₀ ,_) vs
        votes-agree = {!!} {- with creatorId vote ≟ sutId
        ... | yes p = {!!}
        ... | no ¬p = {!!} -}

    -- soundness s₀ Tick inv prf
    --   with StartOfRound? (State.clock s₀) (v-round (State.clock s₀))
    -- soundness s₀ Tick inv prf | yes p =
    --   let
    --     pre = tick-preconditions s₀ inv prf
    --     open TickPreconditions pre
    --   in
    --     record
    --       { s₁          = {!!}
    --       ; invariant₀  = inv
    --       ; invariant₁  = {!!}
    --       ; trace       = CreateVote (invFetched inv)
    --                         (honest {p = sutId} {t = tree}
    --                           validBlockHash
    --                           {!!}
    --                           {!!}
    --                           p
    --                           axiom-everyoneIsOnTheCommittee
    --                           validVote
    --                         )
    --                       ↣ ∎
    --       ; s₁-agrees   = {!!}
    --       ; votes-agree = {!!}
    --       }

    -- soundness s₀ Tick inv prf | no ¬p
    --   with NextSlotInSameRound? s₀
    -- soundness s₀ Tick inv prf | no ¬p | yes q =
    --   let
    --     pre = tick-preconditions s₀ inv prf
    --     open TickPreconditions pre
    --   in
    --     record
    --       { s₁          = tick s₀
    --       ; invariant₀  = inv
    --       ; invariant₁  = {!!}
    --       ; trace       = NextSlot (invFetched inv) q ↣ ∎
    --       ; s₁-agrees   = {!refl!}
    --       ; votes-agree = {!refl!}
    --       }
    -- soundness s₀ Tick inv prf | no ¬p | no ¬q =
    --   record
    --     { s₁          = tick s₀
    --     ; invariant₀  = inv
    --     ; invariant₁  = {!!}
    --     ; trace       = NextSlotNewRound (invFetched inv) {!!} {!!} ↣ ∎
    --     ; s₁-agrees   = {!refl!}
    --     ; votes-agree = {!refl!}
    --     }
