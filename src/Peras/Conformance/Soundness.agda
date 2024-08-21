
module Peras.Conformance.Soundness where

open import Haskell.Prelude
open import Haskell.Prim.Tuple
open import Haskell.Law.Equality

open import Data.Empty using (⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any.Properties
open import Data.Nat using (NonZero; ℕ; _≡ᵇ_; _≥_; _≥?_; _>?_)
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Maybe using (maybe′; nothing; just)
open import Data.Product as P using (∃; Σ-syntax; ∃-syntax; proj₁; proj₂)
open import Data.Sum as S using (inj₁; inj₂; _⊎_; [_,_])
open import Relation.Nullary.Decidable using (Dec; yes; no; ¬?)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Peras.Block
open import Peras.Chain
open import Peras.Crypto
open import Peras.Foreign using (checkSignedVote)
open import Peras.Numbering
open import Peras.Params
open import Peras.Util
open import Prelude.AssocList
open import Prelude.DecEq hiding (_==_; _≟_)
import Peras.SmallStep as SmallStep

open import Peras.Conformance.Model as Model
open import Peras.Conformance.Params
open import Peras.Conformance.ProofPrelude

module _ ⦃ _ : Hashable (List Tx) ⦄
         ⦃ params     : Params ⦄
         ⦃ network    : Network ⦄
         ⦃ postulates : Postulates ⦄
         {S : Set} {adversarialState₀ : S}
         {txSelection : SlotNumber → PartyId → List Tx}
         {parties : Parties}
         {sut∈parties : (sutId P., Honest {sutId}) ∈ parties}
    where


  -- TODO: how to defined honesty?
  honesty-sut : Honesty sutId
  honesty-sut = Honest {sutId}

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
    ; perasT = T
    ; perasΔ = Δ
    }
    where
      open Params params
      open Network network

  Tree = NodeModelTree' modelParams

  open SmallStep.Message
  open SmallStep.Semantics {NodeModel} {Tree} {S} {adversarialState₀} {txSelection} {parties}

  open SmallStep.IsTreeType
  open SmallStep.TreeType Tree renaming (allChains to chains; preferredChain to prefChain)

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
    sutVotesInStep (CreateBlock _ _) = []
    sutVotesInStep (NextSlot _ _) = []
    sutVotesInStep (NextSlotNewRound _ _ _) = []
    sutVotesInStep {s₀} (CreateVote _ (honest {p} {t} {M} {π} {σ} {b} _ _ _ _ _ _))
      with p ≟ sutId
    ... | (yes _) = (State.clock s₀ , createVote (State.clock M) p π σ b) ∷ []
    ... | (no _)  = []

    sutVotesInTrace : ∀ {s₀ s₁} → s₀ ↝⋆ s₁ → List (SlotNumber × Vote)
    sutVotesInTrace ∎              = []
    sutVotesInTrace (step ↣ trace) = sutVotesInStep step ++ sutVotesInTrace trace

    vr-1a⇒VotingRule-1A : ∀ (s : State) (p : ℕ)
      → let
          m = modelState s p
          cert' = maximumBy cert₀ (comparing round) (allSeenCerts m)
        in
          nextRound (round cert') ≡ rFromSlot m
      → VotingRule-1A (v-round (clock m)) m
    vr-1a⇒VotingRule-1A s p x
      rewrite
        suc-definition
          {n = getRoundNumber (round (latestCert cert₀ (allSeenCerts (modelState s p))))}
      = cong getRoundNumber (sym x)

    opaque
      unfolding votingBlockHash

      vr-1b⇒VotingRule-1B : ∀ (s : State) (p : ℕ)
        → let m = modelState s p
          in Vr1B m
        → VotingRule-1B (clock m) m
      vr-1b⇒VotingRule-1B s p x
        rewrite
          filter-eq'
            {prefChain (modelState s p)}
            {λ {a → getSlotNumber (slotNumber a) + (Params.L params)}}
            {getSlotNumber (clock (modelState s p))}
        = x

    vr-2a⇒VotingRule-2A : ∀ (s : State) (p : ℕ)
      → let
          m = modelState s p
          cert' = maximumBy cert₀ (comparing round) (allSeenCerts m)
        in
          getRoundNumber (rFromSlot m) ≥ getRoundNumber (round cert') + perasR (protocol m)
      → VotingRule-2A (v-round (clock m)) m
    vr-2a⇒VotingRule-2A _ _ x = x

    vr-2b⇒VotingRule-2B : ∀ (s : State) (p : ℕ)
      → let
          m = modelState s p
        in
              (getRoundNumber (rFromSlot m) Data.Nat.> getRoundNumber (round (certS m)))
          P.× (mod (getRoundNumber (rFromSlot m)) (perasK (protocol m)) ≡ mod (getRoundNumber (round (certS m))) (perasK (protocol m)))
      → VotingRule-2B (v-round (clock m)) m
    vr-2b⇒VotingRule-2B _ _ x = x

    opaque
      unfolding checkVoteNotFromSut

      creatorId≢sutId : ∀ {vote : Vote} → checkVoteNotFromSut vote ≡ True → creatorId vote ≢ sutId
      creatorId≢sutId x = not-eqℕ-sound x

    record Invariant (s : State) : Set where
      field
        invFetched : Fetched s
        -- allTreesAreEqual : All (λ { bt → (just (proj₂ bt)) ≡ State.blockTrees s ⁉ sutId }) (State.blockTrees s)

    open Invariant

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

    @0 newVote-soundness : ∀ {vs ms₁} s₀ vote
                          → Invariant s₀
                          → transition (modelState s₀ sutId) (NewVote vote) ≡ Just (vs , ms₁)
                          → Soundness s₀ ms₁ (map (State.clock s₀ ,_) vs)

    newVote-soundness s₀ vote inv prf
      with mod (getSlotNumber (State.clock s₀)) (Params.U params) == 0 in isSlotZero
         | checkSignedVote vote in checkedSig
         | checkVoteNotFromSut vote in checkedSut
         | isYes (checkVotingRules (modelState s₀ sutId)) in checkedVRs
         | votingBlockHash (modelState s₀ sutId) == blockHash vote in isValidBlockHash
    newVote-soundness {vs} {ms₁} s₀ vote inv refl | True | True | True | True | True =
      record
        { s₁          = s₁
        ; invariant₀  = inv
        ; invariant₁  = inv₁
        ; trace       = trace
        ; s₁-agrees   = s₁-agrees
        ; votes-agree = votes-agree
        }

      where
        slot : SlotNumber
        slot = State.clock s₀

        r : RoundNumber
        r = v-round slot

        tree : NodeModel
        tree = modelState s₀ sutId -- we don't track the block trees for the environment nodes in the test model!

        -- trees-eq : All (λ { bt → (just (proj₂ bt)) ≡ State.blockTrees s₀ ⁉ sutId }) (State.blockTrees s₀)
        -- trees-eq = allTreesAreEqual inv

        startOfRound : StartOfRound slot r
        startOfRound = lem-divMod _ _ (eqℕ-sound isSlotZero)

        σ : Signature
        σ = signature vote

        v : Vote
        v = createVote slot (creatorId vote) (proofM vote) σ (blockHash vote)

        validVote : VotingRule slot tree
        validVote = -- need to check the VR logic also for environment votes
          let
            witness = toWitness (isYes≡True⇒TTrue checkedVRs)
            f₁ = vr-1a⇒VotingRule-1A s₀ sutId
            f₂ = vr-1b⇒VotingRule-1B s₀ sutId
            f₃ = vr-2a⇒VotingRule-2A s₀ sutId
            f₄ = vr-2b⇒VotingRule-2B s₀ sutId
          in
            S.map (P.map f₁ f₂) (P.map f₃ f₄) witness

        postulate -- TODO
          vote-round : getRoundNumber (votingRound vote) ≡ rnd (getSlotNumber slot)

        correctVote : vote ≡ v
        correctVote = cong (λ {r → record vote { votingRound = MkRoundNumber r}}) vote-round

        notFromSut : creatorId vote ≢ sutId
        notFromSut = creatorId≢sutId checkedSut

        msg : List SmallStep.Envelope
        msg =
          Data.List.map
            (P.uncurry SmallStep.⦅_,_, (VoteMsg v) , fzero ⦆)
            (Data.List.filter (λ x → ¬? (creatorId vote ≟ proj₁ x)) parties)

        sut∈messages' : SmallStep.⦅ sutId , Honest , VoteMsg v , fzero ⦆ ∈ msg
        sut∈messages' = {!!}

        sut∈messages : SmallStep.⦅ sutId , Honest , VoteMsg v , fzero ⦆ ∈ msg Data.List.++ State.messages s₀
        sut∈messages = ++⁺ˡ sut∈messages'

        s₁ : State
        s₁ = record s₀
               { blockTrees = set sutId (addVote tree v) (set (creatorId vote) (addVote tree v) blockTrees)
               ; messages = (msg Data.List.++ messages) ─ sut∈messages
               ; history = (VoteMsg v) ∷ history
               }
             where
               open State s₀

        creatorExists  : State.blockTrees s₀ ⁉ (creatorId vote) ≡ just tree -- TODO: always the same tree?
        creatorExists = {!!}

        sutExists'  : State.blockTrees s₀ ⁉ sutId ≡ just tree
        sutExists' = {!!}

        sutExists : set (creatorId vote) (addVote tree v) (State.blockTrees s₀) ⁉ sutId ≡ just tree
        sutExists with creatorId vote ≟ sutId
        ... | yes p = ⊥-elim (notFromSut p)
        ... | no q =
          trans
            (k≢k'-get∘set {k = sutId} {k' = creatorId vote} {v = addVote tree v} {m = State.blockTrees s₀} q)
            sutExists'

        postulate -- TODO
          filter-eq : ∀ {l : Chain} {f : Block → ℕ} {b : ℕ} →
            filter (λ { a → (f a) <= b }) l ≡ Data.List.filter (λ { a → (f a) Data.Nat.≤? b }) l

        opaque
          unfolding votingBlockHash

          blockSelection-eq : BlockSelection slot tree ≡ votingBlockHash tree
          blockSelection-eq
            rewrite
              filter-eq
                {prefChain tree}
                {λ {s → getSlotNumber (slotNumber s) + (Params.L params)}}
                {getSlotNumber slot}
             = refl

        validBlockHash : BlockSelection (State.clock s₀) tree ≡ blockHash vote
        validBlockHash = MkHash-inj $ trans (cong hashBytes blockSelection-eq) (lem-eqBS isValidBlockHash)

        validSignature : IsVoteSignature v σ
        validSignature with v ← axiom-checkVoteSignature checkedSig rewrite correctVote = v

        trace : s₀ ↝⋆ s₁
        trace = CreateVote (invFetched inv)
                  (honest {σ = Vote.signature vote}
                    validBlockHash
                    creatorExists
                    validSignature
                    startOfRound
                    axiom-everyoneIsOnTheCommittee
                    validVote
                  )
              ↣ Fetch {h = honesty-sut} {m = VoteMsg v}
                  (honest {p = sutId}
                    sutExists
                    sut∈messages
                    VoteReceived
                  )
              ↣ ∎

        lem-s₁-agrees :
          modelState
            (record s₀
              { blockTrees =
                  set sutId
                    (record (modelState s₀ sutId)
                      { allVotes = v ∷ (allVotes (modelState s₀ sutId)) }
                    )
                    (set
                      (creatorId vote)
                      (record (modelState s₀ sutId)
                        { allVotes = v ∷ (allVotes (modelState s₀ sutId)) }
                      )
                      (State.blockTrees s₀)
                    )
              }
            )
            sutId
          ≡
          record (modelState s₀ sutId)
            { allVotes =
                vote ∷ (allVotes (modelState s₀ sutId))
            }

        lem-s₁-agrees with creatorId vote ≟ sutId
        ... | yes p = ⊥-elim (notFromSut p)
        ... | no q = {-
          rewrite get∘set≡id
            {k = sutId}
            {v = addVote' (modelState s₀ sutId) v}
            {m = State.blockTrees s₀}
            = {!refl!} -} {!!}

        s₁-agrees : modelState s₁ sutId ≡ ms₁
        s₁-agrees = lem-s₁-agrees

        votes-agree : sutVotesInTrace trace ≡ map (State.clock s₀ ,_) vs
        votes-agree with creatorId vote ≟ sutId
        ... | yes p = ⊥-elim (notFromSut p)
        ... | no _  = refl

        -- msg₀≡msg₁ : State.messages s₀ ≡ State.messages s₁
        -- msg₀≡msg₁ = {!refl!}

        inv₁ : Invariant s₁
        inv₁ = {!!}

    @0 newChain-soundness : ∀ {vs ms₁} s₀ chain
                          → Invariant s₀
                          → transition (modelState s₀ sutId) (NewChain chain) ≡ Just (vs , ms₁)
                          → Soundness s₀ ms₁ (map (State.clock s₀ ,_) vs)
    newChain-soundness s chain inv prf = {!!}

    @0 tick-soundness : ∀ {vs ms₁} s₀
                          → Invariant s₀
                          → transition (modelState s₀ sutId) Tick ≡ Just (vs , ms₁)
                          → Soundness s₀ ms₁ (map (State.clock s₀ ,_) vs)
    tick-soundness s inv prf = {!!}

    @0 soundness : ∀ {ms₁ vs} (s₀ : State) (a : EnvAction)
              → Invariant s₀
              → transition (modelState s₀ sutId) a ≡ Just (vs , ms₁)
              → Soundness s₀ ms₁ (map (State.clock s₀ ,_) vs)

    soundness s₀ (NewVote vote) = newVote-soundness s₀ vote
    soundness s₀ (NewChain chain) = newChain-soundness s₀ chain
    soundness s₀ Tick = tick-soundness s₀







    {-
    soundness s₀ (NewChain chain@(block ∷ bs)) inv prf
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
-}

{-
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
-}

{-
    @0 tick-preconditions : ∀ {vs ms₁} s
                          → Invariant s
                          → transition (modelState s sutId) Tick ≡ Just (vs , ms₁)
                          → TickPreconditions s
    tick-preconditions s inv refl
      with isYes (checkVotingRules (modelState s sutId)) in checkedVRs
    ... | True = record
      { tree        = modelState s sutId
      ; block       = {!!}
      ; blockExists = {!!}
      ; validVote   =
        let
          witness = toWitness (isYes≡True⇒TTrue checkedVRs)
          f₁ = vr-1a⇒VotingRule-1A s sutId
          f₂ = vr-1b⇒VotingRule-1B s sutId
          f₃ = vr-2a⇒VotingRule-2A s sutId
          f₄ = vr-2b⇒VotingRule-2B s sutId
        in
          S.map (P.map f₁ f₂) (P.map f₃ f₄) witness
      }
    ... | False = {!!}
-}

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
