
module Peras.Conformance.Soundness where

open import Haskell.Prelude as Haskell hiding (map; filter; _++_; maybe; _>_)

open import Data.Empty using (⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using (map; mapMaybe; filter; _++_)
open import Data.List.Membership.Propositional
open import Data.List.Properties
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any.Properties
open import Data.Nat using (NonZero; ℕ; _≡ᵇ_; _≥_; _>_; _≥?_; _>?_; _≤?_)
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Maybe using (maybe; maybe′; nothing; just)
open import Data.Product as P using (∃; Σ-syntax; ∃-syntax; proj₁; proj₂) renaming (_,_ to _⸴_)
open import Data.Sum as S using (inj₁; inj₂; _⊎_; [_,_])
open import Relation.Nullary.Decidable using (Dec; yes; no; ¬?)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)

open import Peras.Block
open import Peras.Chain
open import Peras.Crypto
open import Peras.Foreign using (checkSignedVote)
open import Peras.Numbering
open import Peras.Params
open import Peras.Util
open import Prelude.AssocList
open import Prelude.Default
open import Prelude.DecEq hiding (_==_; _≟_)

import Peras.SmallStep as SmallStep
open SmallStep using (⦅_,_,_,_⦆)

open import Peras.Conformance.Params
open import Peras.Conformance.ProofPrelude

open import Peras.Conformance.Model as Model
open Model.TreeInstance using (NodeModelTree)

module _ ⦃ _ : Hashable (List Tx) ⦄
         ⦃ postulates : Postulates ⦄
         {S : Set} {adversarialState₀ : S}
         {txSelection : SlotNumber → PartyId → List Tx}
    where

  uniqueIds : otherId ≢ sutId
  uniqueIds = λ ()

  uniqueIds' : sutId ≢ otherId
  uniqueIds' = λ ()

  parties : Parties
  parties = (sutId ⸴ Honest {sutId}) ∷ (otherId ⸴ Honest {otherId}) ∷ [] -- wlog

  sut∈parties : (sutId ⸴ Honest {sutId}) ∈ parties
  sut∈parties = Any.here refl

  sutHonesty : Honesty sutId
  sutHonesty = proj₂ (Any.lookup sut∈parties)

  other∈parties : (otherId ⸴ Honest {otherId}) ∈ parties
  other∈parties = Any.there (Any.here refl)

  otherHonesty : Honesty otherId
  otherHonesty = proj₂ (Any.lookup other∈parties)

  apply-filter : filter (λ x → ¬? (otherId ≟ proj₁ x)) parties ≡ (sutId ⸴ Honest {sutId}) ∷ []
  apply-filter =
    let
      f₁ = filter-accept (λ x → ¬? (otherId ≟ proj₁ x))
             {sutId ⸴ Honest {sutId}} {(otherId ⸴ Honest {otherId}) ∷ []} uniqueIds
      f₂ = filter-reject (λ x → (proj₁ x ≟ sutId)) {(otherId ⸴ Honest {otherId})} {[]} uniqueIds
    in
      trans f₁ (cong ((sutId ⸴ Honest {sutId}) ∷_) f₂)

  apply-filter' : filter (λ x → ¬? (sutId ≟ proj₁ x)) parties ≡ (otherId ⸴ Honest {otherId}) ∷ []
  apply-filter' = filter-reject (λ x → (proj₁ x ≟ otherId))
                    {sutId ⸴ Honest {sutId}} {(otherId ⸴ Honest {otherId}) ∷ []} uniqueIds'

  modelParams : PerasParams
  modelParams = testParams

  Tree = NodeModelTree

  instance
    network : Network
    network =
      record
        { Δ = perasΔ testParams }

    params : Params
    params =
      record
        { U = perasU testParams
        ; K = perasK testParams
        ; R = perasR testParams
        ; L = perasL testParams
        ; A = perasA testParams
        ; τ = perasτ testParams
        ; B = perasB testParams
        ; T = perasT testParams
        }

  open SmallStep.Message
  open SmallStep.Semantics {NodeModel} {Tree} {S} {adversarialState₀} {txSelection} {parties}

  open SmallStep.IsTreeType
  open SmallStep.TreeType Tree renaming (allChains to chains; preferredChain to prefChain)

  private
    instance
      Default-T : Default NodeModel
      Default-T .def = tree₀

  module Assumptions
           (let open Postulates postulates)

           -- Currently we allow anyone to vote
           (axiom-everyoneIsOnTheCommittee : ∀ {p slot prf} → IsCommitteeMember p slot prf)

           (axiom-checkVoteSignature : ∀ {vote} → checkSignedVote vote ≡ True → IsVoteSignature vote (signature vote))
         where

    modelState : State → NodeModel
    modelState s = record
      { clock        = State.clock s
      ; protocol     = modelParams
      ; allChains    = maybe′ chains [] (State.blockTrees s ⁉ sutId)
      ; allVotes     = maybe′ votes  [] (State.blockTrees s ⁉ sutId)
      ; allSeenCerts = maybe′ certs  [] (State.blockTrees s ⁉ sutId)
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

    vr-1a⇒VotingRule-1A : ∀ (s : State)
      → let
          m = modelState s
          cert' = maximumBy cert₀ (comparing round) (allSeenCerts m)
        in
          nextRound (round cert') ≡ rFromSlot m
      → VotingRule-1A (v-round (clock m)) m
    vr-1a⇒VotingRule-1A s x
      rewrite
        suc-definition
          {n = getRoundNumber (round (latestCert cert₀ (allSeenCerts (modelState s))))}
      = cong getRoundNumber (sym x)

    opaque
      unfolding votingBlockHash

      vr-1b⇒VotingRule-1B : ∀ (s : State)
        → let m = modelState s
          in Vr1B m
        → VotingRule-1B (clock m) m
      vr-1b⇒VotingRule-1B s x
        rewrite
          filter-eq'
            {prefChain (modelState s)}
            {λ {a → getSlotNumber (slotNumber a) + (Params.L params)}}
            {getSlotNumber (clock (modelState s))}
        = x

    vr-2a⇒VotingRule-2A : ∀ (s : State)
      → let
          m = modelState s
          cert' = maximumBy cert₀ (comparing round) (allSeenCerts m)
        in
          getRoundNumber (rFromSlot m) ≥ getRoundNumber (round cert') + perasR (protocol m)
      → VotingRule-2A (v-round (clock m)) m
    vr-2a⇒VotingRule-2A _ x = x

    vr-2b⇒VotingRule-2B : ∀ (s : State)
      → let
          m = modelState s
        in
              (getRoundNumber (rFromSlot m) > getRoundNumber (round (certS m)))
          P.× (mod (getRoundNumber (rFromSlot m)) (perasK (protocol m)) ≡ mod (getRoundNumber (round (certS m))) (perasK (protocol m)))
      → VotingRule-2B (v-round (clock m)) m
    vr-2b⇒VotingRule-2B _ x = x

    postulate -- TODO
      existsTrees : ∀ {p sᵢ sⱼ}
        → State.blockTrees sᵢ ⁉ p ≡ just (modelState sᵢ)
        → sᵢ ↝⋆ sⱼ
        → State.blockTrees sⱼ ⁉ p ≡ just (modelState sⱼ)

    record Invariant (s : State) : Set where
      field
        invFetched : Fetched s
        sutTree : State.blockTrees s ⁉ sutId ≡ just (modelState s)
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
        s₁-agrees   : modelState s₁ ≡ ms₁
        votes-agree : sutVotesInTrace trace ≡ vs

    @0 newVote-soundness : ∀ {vs ms₁} s₀ vote
                          → Invariant s₀
                          → transition (modelState s₀) (NewVote vote) ≡ Just (vs , ms₁)
                          → Soundness s₀ ms₁ (map (State.clock s₀ ,_) vs)

    newVote-soundness s₀ vote inv prf
      with mod (getSlotNumber (State.clock s₀)) (Params.U params) == 0 in isSlotZero
         | div (getSlotNumber (State.clock s₀)) (Params.U params) == getRoundNumber (votingRound vote) in isVotingRound
         | checkSignedVote vote in checkedSig
         | checkVoteFromOther vote in checkedOther
         | isYes (checkVotingRules (modelState s₀)) in checkedVRs
         | votingBlockHash (modelState s₀) == blockHash vote in isValidBlockHash
    newVote-soundness {vs} {ms₁} s₀ vote inv refl | True | True | True | True | True | True =
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

        notFromSut : creatorId vote ≢ sutId
        notFromSut x = uniqueIds (trans (sym (eqℕ-sound checkedOther)) x)

        tree : NodeModel
        tree = modelState s₀  -- we don't track the block trees for the environment nodes in the test model!

        startOfRound : StartOfRound slot r
        startOfRound = lem-divMod _ _ (eqℕ-sound isSlotZero)

        σ : Signature
        σ = signature vote

        creatorId≡otherId : creatorId vote ≡ otherId
        creatorId≡otherId = eqℕ-sound checkedOther

        v : Vote
        v = createVote slot (creatorId vote) (proofM vote) σ (blockHash vote)

        validVote : VotingRule slot tree
        validVote = -- need to check the VR logic also for environment votes
          let
            witness = toWitness (isYes≡True⇒TTrue checkedVRs)
            f₁ = vr-1a⇒VotingRule-1A s₀
            f₂ = vr-1b⇒VotingRule-1B s₀
            f₃ = vr-2a⇒VotingRule-2A s₀
            f₄ = vr-2b⇒VotingRule-2B s₀
          in
            S.map (P.map f₁ f₂) (P.map f₃ f₄) witness

        vote-round : getRoundNumber (votingRound vote) ≡ rnd (getSlotNumber slot)
        vote-round = sym (eqℕ-sound isVotingRound)

        correctVote : vote ≡ v
        correctVote = cong (λ {r → record vote { votingRound = MkRoundNumber r}}) vote-round

        msg : List SmallStep.Envelope
        msg =
          map
            (P.uncurry ⦅_,_, VoteMsg v , fzero ⦆)
            (filter (λ x → ¬? (creatorId vote ≟ proj₁ x)) parties)

        map∘apply-filter : msg ≡ ⦅ sutId , Honest { sutId } , VoteMsg v , fzero ⦆ ∷ []
        map∘apply-filter rewrite apply-filter rewrite creatorId≡otherId = refl

        sut∈messages' : ⦅ sutId , Honest , VoteMsg v , fzero ⦆ ∈ msg
        sut∈messages' rewrite map∘apply-filter = singleton⁺ refl

        sut∈messages : ⦅ sutId , Honest , VoteMsg v , fzero ⦆ ∈ msg ++ State.messages s₀
        sut∈messages = ++⁺ˡ sut∈messages'

        s₁ : State
        s₁ = record s₀
               { blockTrees =
                   set sutId (addVote tree v)
                     (set (creatorId vote) (addVote tree v)
                       blockTrees)
               ; messages = (msg ++ messages) ─ sut∈messages
               ; history = VoteMsg v ∷ history
               }
             where
               open State s₀

        creatorExists  : State.blockTrees s₀ ⁉ (creatorId vote) ≡ just tree -- TODO: always the same tree?
        creatorExists = {!!}

        sutExists : set (creatorId vote) (addVote tree v) (State.blockTrees s₀) ⁉ sutId ≡ just tree
        sutExists =
          trans
            (k'≢k-get∘set
              {k = sutId}
              {k' = creatorId vote}
              {v = addVote tree v}
              {m = State.blockTrees s₀}
              notFromSut)
            (sutTree inv)

        postulate -- TODO
          filter-eq : ∀ {l : Chain} {f : Block → ℕ} {b : ℕ} →
            Haskell.filter (λ { a → (f a) <= b }) l ≡ filter (λ { a → (f a) ≤? b }) l

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
              ↣ Fetch {h = sutHonesty} {m = VoteMsg v}
                  (honest {p = sutId}
                    sutExists
                    sut∈messages
                    VoteReceived
                  )
              ↣ ∎

        tree' : NodeModel
        tree' = addVote' tree v

        bt₀ : AssocList ℕ NodeModel
        bt₀ = State.blockTrees s₀

        set-irrelevant :
          let s = record s₀
                    { blockTrees =
                        set sutId tree'
                          (set (creatorId vote) tree' bt₀) }
          in
          record
            { clock        = State.clock s
            ; protocol     = modelParams
            ; allChains    = maybe′ chains [] (State.blockTrees s ⁉ sutId)
            ; allVotes     = maybe′ votes  [] (State.blockTrees s ⁉ sutId)
            ; allSeenCerts = maybe′ certs  [] (State.blockTrees s ⁉ sutId)
            }
          ≡
          let s = record s₀
                    { blockTrees =
                        set sutId tree' bt₀ }
          in
          record
            { clock        = State.clock s
            ; protocol     = modelParams
            ; allChains    = maybe′ chains [] (State.blockTrees s ⁉ sutId)
            ; allVotes     = maybe′ votes  [] (State.blockTrees s ⁉ sutId)
            ; allSeenCerts = maybe′ certs  [] (State.blockTrees s ⁉ sutId)
            }
        set-irrelevant
          rewrite k'≢k-get∘set∘set
            {k  = sutId}
            {k' = creatorId vote}
            {v  = tree'}
            {v' = tree'}
            {m  = State.blockTrees s₀}
            notFromSut = refl

        addVote-modelState :
          let s = record s₀
                    { blockTrees =
                        set sutId tree' bt₀ }
          in
          record
            { clock        = State.clock s
            ; protocol     = modelParams
            ; allChains    = maybe′ chains [] (State.blockTrees s ⁉ sutId)
            ; allVotes     = maybe′ votes  [] (State.blockTrees s ⁉ sutId)
            ; allSeenCerts = maybe′ certs  [] (State.blockTrees s ⁉ sutId)
            }
          ≡
          let s = record tree { allVotes = vote ∷ (maybe′ votes [] (State.blockTrees s₀ ⁉ sutId)) }
          in record s { allSeenCerts = foldr insertCert (allSeenCerts s) (certsFromQuorum s) }
        addVote-modelState
          rewrite get∘set≡id
            {k = sutId}
            {v = tree'}
            {m = State.blockTrees s₀}
          rewrite correctVote
          = refl

        s₁-agrees :
          let s = record tree { allVotes = v ∷ (allVotes tree) }
              s' = record s { allSeenCerts = foldr insertCert (allSeenCerts s) (certsFromQuorum s) }
          in
          modelState
            record s₀ { blockTrees = set sutId s' (set (creatorId vote) s' bt₀) }
          ≡
          let s = record tree { allVotes = vote ∷ (allVotes tree) }
          in
          record { allSeenCerts = foldr insertCert (allSeenCerts s) (certsFromQuorum s) }
        s₁-agrees with creatorId vote ≟ sutId
        ... | yes p = ⊥-elim (notFromSut p)
        ... | no _ = trans set-irrelevant addVote-modelState

        votes-agree : sutVotesInTrace trace ≡ map (State.clock s₀ ,_) vs
        votes-agree with creatorId vote ≟ sutId
        ... | yes p = ⊥-elim (notFromSut p)
        ... | no _  = refl

        msg₀≡msg₁ : State.messages s₀ ≡ (msg ++ State.messages s₀) ─ sut∈messages
        msg₀≡msg₁ rewrite map∘apply-filter = refl

        inv₁ : Invariant s₁
        inv₁ with i ← invFetched inv rewrite msg₀≡msg₁ =
          record
            { invFetched = i
            ; sutTree = existsTrees {sutId} {s₀} {s₁} (sutTree inv) trace
            }

    @0 newChain-soundness : ∀ {vs ms₁} s₀ chain
                          → Invariant s₀
                          → transition (modelState s₀) (NewChain chain) ≡ Just (vs , ms₁)
                          → Soundness s₀ ms₁ (map (State.clock s₀ ,_) vs)
    newChain-soundness s₀ [] inv refl =
      record
        { s₁ = s₀
        ; invariant₀ = inv
        ; invariant₁ = inv
        ; trace = ∎
        ; s₁-agrees = refl
        ; votes-agree = refl
        }
    newChain-soundness s₀ (block ∷ rest) inv prf
      with checkBlockFromOther block in checkedOther
    newChain-soundness {vs} {ms₁} s₀ (block ∷ rest) inv refl
      | True =
      record
        { s₁ = s₁
        ; invariant₀ = inv
        ; invariant₁ = inv₁
        ; trace = trace
        ; s₁-agrees = s₁-agrees
        ; votes-agree = votes-agree
        }
      where

        slot : SlotNumber
        slot = State.clock s₀

        notFromSut : creatorId block ≢ sutId
        notFromSut x =
          uniqueIds (trans (sym (eqℕ-sound checkedOther)) x)

        tree : NodeModel
        tree = modelState s₀

        β : Block
        β = createBlock (State.clock s₀) (creatorId block) (leadershipProof block) (signature block) tree

        chain : Chain
        chain = β ∷ prefChain tree

        validHead : block ≡ createBlock slot (creatorId block) (leadershipProof block) (signature block) tree
        validHead = {!!}

        validRest : rest ≡ prefChain tree
        validRest = {!!}

        validChain : ValidChain (block ∷ rest)
        validChain = {!!}

        validChain' : ValidChain
          (createBlock slot (creatorId block) (leadershipProof block) (signature block) tree
            ∷ prefChain tree)
        validChain' with c ← validChain rewrite validHead rewrite validRest = c

        creatorId≡otherId : creatorId block ≡ otherId
        creatorId≡otherId = eqℕ-sound checkedOther

        msg : List SmallStep.Envelope
        msg =
          map
            (P.uncurry ⦅_,_, ChainMsg chain , fzero ⦆)
            (filter (λ x → ¬? (creatorId block ≟ proj₁ x)) parties)

        map∘apply-filter : msg ≡ ⦅ sutId , Honest { sutId } , ChainMsg chain , fzero ⦆ ∷ []
        map∘apply-filter rewrite apply-filter rewrite creatorId≡otherId = refl

        sut∈messages' : ⦅ sutId , Honest , ChainMsg chain , fzero ⦆ ∈ msg
        sut∈messages' rewrite map∘apply-filter = singleton⁺ refl

        sut∈messages : ⦅ sutId , Honest , ChainMsg chain , fzero ⦆ ∈ msg ++ State.messages s₀
        sut∈messages = ++⁺ˡ sut∈messages'

        s₁ : State
        s₁ = record s₀
               { blockTrees =
                   set sutId (newChain tree chain)
                     (set (creatorId block) (newChain tree chain)
                       blockTrees)
               ; messages = (msg ++ messages) ─ sut∈messages
               ; history = ChainMsg chain ∷ history
               }
             where
               open State s₀

        creatorExists  : State.blockTrees s₀ ⁉ (creatorId block) ≡ just tree -- TODO: always the same tree?
        creatorExists = {!!}

        sutExists : set (creatorId block) (newChain tree chain) (State.blockTrees s₀) ⁉ sutId ≡ just tree
        sutExists =
          trans
            (k'≢k-get∘set {k = sutId} {k' = creatorId block} {v = newChain tree chain} {m = State.blockTrees s₀} notFromSut)
            (sutTree inv)

        trace : s₀ ↝⋆ s₁
        trace = CreateBlock
                  (invFetched inv)
                  (honest
                    creatorExists
                    validChain'
                  )
              ↣ Fetch {h = sutHonesty} {m = ChainMsg chain}
                  (honest {p = sutId}
                    sutExists
                    sut∈messages
                    ChainReceived
                  )
              ↣ ∎

        set-irrelevant :
          let s = record s₀
                    { blockTrees =
                        set sutId (newChain tree chain)
                          (set (creatorId block) (newChain tree chain)
                            (State.blockTrees s₀)) }
          in
          record
            { clock        = State.clock s
            ; protocol     = modelParams
            ; allChains    = maybe′ chains [] (State.blockTrees s ⁉ sutId)
            ; allVotes     = maybe′ votes  [] (State.blockTrees s ⁉ sutId)
            ; allSeenCerts = maybe′ certs  [] (State.blockTrees s ⁉ sutId)
            }
          ≡
          let s = record s₀
                    { blockTrees =
                        set sutId (newChain tree chain)
                          (State.blockTrees s₀) }
          in
          record
            { clock        = State.clock s
            ; protocol     = modelParams
            ; allChains    = maybe′ chains [] (State.blockTrees s ⁉ sutId)
            ; allVotes     = maybe′ votes  [] (State.blockTrees s ⁉ sutId)
            ; allSeenCerts = maybe′ certs  [] (State.blockTrees s ⁉ sutId)
            }
        set-irrelevant
          rewrite k'≢k-get∘set∘set
            {k  = sutId}
            {k' = creatorId block}
            {v  = newChain tree chain}
            {v' = newChain tree chain}
            {m  = State.blockTrees s₀}
            notFromSut = refl

        newChain-modelState :
          let s = record s₀
                    { blockTrees =
                        set sutId (newChain tree chain)
                          (State.blockTrees s₀) }
          in
          record
            { clock        = State.clock s
            ; protocol     = modelParams
            ; allChains    = maybe′ chains [] (State.blockTrees s ⁉ sutId)
            ; allVotes     = maybe′ votes  [] (State.blockTrees s ⁉ sutId)
            ; allSeenCerts = maybe′ certs  [] (State.blockTrees s ⁉ sutId)
            }
          ≡
          record tree
            { allChains    = chain ∷ maybe′ chains [] (State.blockTrees s₀ ⁉ sutId)
            ; allVotes     = maybe′ votes [] (State.blockTrees s₀ ⁉ sutId)
            ; allSeenCerts = foldr insertCert (maybe′ certs [] (State.blockTrees s₀ ⁉ sutId)) (mapMaybe certificate chain)
            }
        newChain-modelState
          rewrite
            get∘set≡id
              {k = sutId}
              {v = newChain tree chain}
              {m = State.blockTrees s₀}
          = refl

        s₁-agrees :
          modelState
            (record s₀
              { blockTrees =
                  set sutId
                    (record tree
                      { allChains = chain ∷ (allChains tree)
                      ; allSeenCerts = foldr insertCert (allSeenCerts tree) (mapMaybe certificate chain)
                      }
                    )
                    (set
                      (creatorId block)
                      (record tree
                        { allChains = chain ∷ (allChains tree)
                        ; allSeenCerts = foldr insertCert (allSeenCerts tree) (mapMaybe certificate chain)
                        }
                      )
                      (State.blockTrees s₀)
                    )
              }
            )
            ≡ record tree
                { allChains = (block ∷ rest) ∷ maybe allChains [] (State.blockTrees s₀ ⁉ sutId)
                ; allSeenCerts = foldr insertCert (allSeenCerts tree) (mapMaybe certificate (block ∷ rest))
                }
        s₁-agrees with creatorId block ≟ sutId
        ... | yes p = ⊥-elim (notFromSut p)
        ... | no q rewrite validHead rewrite validRest = trans set-irrelevant newChain-modelState

        votes-agree : sutVotesInTrace trace ≡ map (State.clock s₀ ,_) vs
        votes-agree with creatorId block ≟ sutId
        ... | yes p = ⊥-elim (notFromSut p)
        ... | no _  = refl

        msg₀≡msg₁ : State.messages s₀ ≡ (msg ++ State.messages s₀) ─ sut∈messages
        msg₀≡msg₁ rewrite map∘apply-filter = refl

        inv₁ : Invariant s₁
        inv₁ with i ← invFetched inv rewrite msg₀≡msg₁ =
          record
            { invFetched = i
            ; sutTree = existsTrees {sutId} {s₀} {s₁} (sutTree inv) trace
            }

    @0 tick-soundness : ∀ {vs ms₁} s₀
                          → Invariant s₀
                          → transition (modelState s₀) Tick ≡ Just (vs , ms₁)
                          → Soundness s₀ ms₁ (map (State.clock s₀ ,_) vs)
    tick-soundness s₀ inv refl
      with mod (getSlotNumber (State.clock s₀)) (Params.U params) == 0 in isSlotZero

    tick-soundness {vs} s₀ inv refl
      | True with vs

    tick-soundness s₀ inv refl
      | True | vote ∷ xs
      with   checkSignedVote vote in checkedSig
           | isYes (checkVotingRules (modelState s₀)) in checkedVRs
           | votingBlockHash (modelState s₀) == blockHash vote in isValidBlockHash

    tick-soundness {vs} s₀ inv refl
      | True | vote ∷ [] | True | True | True =

        record
          { s₁ = s₁
          ; invariant₀ = inv
          ; invariant₁ = inv₁
          ; trace = trace
          ; s₁-agrees = s₁-agrees
          ; votes-agree = votes-agree
          }
        where

          slot : SlotNumber
          slot = State.clock s₀

          r : RoundNumber
          r = v-round slot

          tree : NodeModel
          tree = modelState s₀

          v : Vote
          v = createVote slot sutId (proofM vote) (signature vote) (blockHash vote)

          startOfRound : StartOfRound slot r
          startOfRound = lem-divMod _ _ (eqℕ-sound isSlotZero)

          msg : List SmallStep.Envelope
          msg =
            map
              (P.uncurry ⦅_,_, VoteMsg v , fzero ⦆)
              (filter (λ x → ¬? (sutId ≟ proj₁ x)) parties)

          map∘apply-filter : msg ≡ ⦅ otherId , Honest { otherId } , VoteMsg v , fzero ⦆ ∷ []
          map∘apply-filter rewrite apply-filter' = refl

          other∈messages' : ⦅ otherId , Honest , VoteMsg v , fzero ⦆ ∈ msg
          other∈messages' rewrite map∘apply-filter = singleton⁺ refl

          other∈messages : ⦅ otherId , Honest , VoteMsg v , fzero ⦆ ∈ msg ++ State.messages s₀
          other∈messages = ++⁺ˡ other∈messages'

          s₁ : State
          s₁ = tick record s₀
                 { blockTrees =
                     set otherId (addVote tree v)
                       (set sutId (addVote tree v)
                         blockTrees)
                 ; messages = (msg ++ messages) ─ other∈messages
                 ; history = VoteMsg v ∷ history
                 }
               where
                 open State s₀

          validVote : VotingRule slot tree
          validVote =
            let
              witness = toWitness (isYes≡True⇒TTrue checkedVRs)
              f₁ = vr-1a⇒VotingRule-1A s₀
              f₂ = vr-1b⇒VotingRule-1B s₀
              f₃ = vr-2a⇒VotingRule-2A s₀
              f₄ = vr-2b⇒VotingRule-2B s₀
            in
              S.map (P.map f₁ f₂) (P.map f₃ f₄) witness

          postulate -- TODO
            filter-eq : ∀ {l : Chain} {f : Block → ℕ} {b : ℕ} →
              Haskell.filter (λ { a → (f a) <= b }) l ≡ filter (λ { a → (f a) ≤? b }) l

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

          vote-round : getRoundNumber (votingRound vote) ≡ rnd (getSlotNumber slot)
          vote-round = {!!} -- TODO: refl

          creatorId≡sutId : creatorId vote ≡ sutId
          creatorId≡sutId = {!!} -- TODO: refl

          correctVote : vote ≡ v
          correctVote
            rewrite sym creatorId≡sutId
            = cong (λ {r → record vote { votingRound = MkRoundNumber r}}) vote-round

          validSignature : IsVoteSignature v (signature v)
          validSignature with v ← axiom-checkVoteSignature checkedSig
            rewrite correctVote rewrite (sym creatorId≡sutId)
            = v

          otherExists : set sutId (addVote tree v) (State.blockTrees s₀) ⁉ otherId ≡ just tree
          otherExists = {!!}

          trace : s₀ ↝⋆ s₁
          trace = CreateVote (invFetched inv)
                      (honest {p = sutId} {t = modelState s₀}
                        validBlockHash
                        (sutTree inv)
                        validSignature
                        startOfRound
                        axiom-everyoneIsOnTheCommittee
                        validVote
                      )
                ↣ Fetch {h = otherHonesty} {m = VoteMsg v}
                    (honest {p = otherId}
                      otherExists
                      other∈messages
                      VoteReceived
                    )
                ↣ NextSlot (invFetched inv) {!!}
                ↣ ∎

          tree' : NodeModel
          tree' = addVote' tree v

          bt₀ : AssocList ℕ NodeModel
          bt₀ = State.blockTrees s₀

          set-irrelevant :
            let s = record s₀
                      { blockTrees =
                          set otherId tree'
                            (set sutId tree' bt₀) }
            in
            record
              { clock        = MkSlotNumber (suc (getSlotNumber (State.clock s)))
              ; protocol     = modelParams
              ; allChains    = maybe′ chains [] (State.blockTrees s ⁉ sutId)
              ; allVotes     = maybe′ votes  [] (State.blockTrees s ⁉ sutId)
              ; allSeenCerts = maybe′ certs  [] (State.blockTrees s ⁉ sutId)
              }
            ≡
            let s = record s₀
                      { blockTrees =
                          set sutId tree' bt₀ }
            in
            record
              { clock        = MkSlotNumber (suc (getSlotNumber (State.clock s)))
              ; protocol     = modelParams
              ; allChains    = maybe′ chains [] (State.blockTrees s ⁉ sutId)
              ; allVotes     = maybe′ votes  [] (State.blockTrees s ⁉ sutId)
              ; allSeenCerts = maybe′ certs  [] (State.blockTrees s ⁉ sutId)
              }
          set-irrelevant
            rewrite k'≢k-get∘set
              {k  = sutId}
              {k' = otherId}
              {v  = tree'}
              {m  = set sutId tree' bt₀}
              uniqueIds = refl

          addVote-modelState :
            let s = record s₀
                      { blockTrees =
                          set sutId tree' bt₀ }
            in
            record
              { clock        = MkSlotNumber (suc (getSlotNumber (State.clock s)))
              ; protocol     = modelParams
              ; allChains    = maybe′ chains [] (State.blockTrees s ⁉ sutId)
              ; allVotes     = maybe′ votes  [] (State.blockTrees s ⁉ sutId)
              ; allSeenCerts = maybe′ certs  [] (State.blockTrees s ⁉ sutId)
              }
            ≡
            let s = record tree
                      { clock    = MkSlotNumber (suc (getSlotNumber (State.clock s₀)))
                      ; allVotes = vote ∷ maybe′ votes [] (State.blockTrees s₀ ⁉ sutId)
                      }
            in record s { allSeenCerts = foldr insertCert (allSeenCerts s) (certsFromQuorum s) }
          addVote-modelState
            rewrite get∘set≡id
              {k = sutId}
              {v = tree'}
              {m = bt₀}
            rewrite correctVote
            = refl

          s₁-agrees :
            let s = record tree { allVotes = v ∷ (allVotes tree) }
                s' = record s { allSeenCerts = foldr insertCert (allSeenCerts s) (certsFromQuorum s) }
            in
            modelState
              record s₀
                 { clock = MkSlotNumber (suc (getSlotNumber (State.clock s₀)))
                 ; blockTrees =
                     set otherId s'
                       (set sutId s' (State.blockTrees s₀))
                 }
            ≡
            let s = record tree
                      { clock = MkSlotNumber (suc (getSlotNumber (State.clock s₀)))
                      ; allVotes = vote ∷ maybe′ votes [] (State.blockTrees s₀ ⁉ sutId)
                      }
            in record s { allSeenCerts = foldr insertCert (allSeenCerts s) (certsFromQuorum s) }
          s₁-agrees
            = trans set-irrelevant addVote-modelState

          votes-agree :
            (State.clock s₀ , v)  ∷ []
            ≡
            (State.clock s₀ , vote) ∷ map (State.clock s₀ ,_) []
          votes-agree
            rewrite correctVote
            = refl

          inv₁ : Invariant s₁
          inv₁ =
            record
              { invFetched = {!!}
              ; sutTree = existsTrees {sutId} {s₀} {s₁} (sutTree inv) trace
              }

    tick-soundness {vs} s₀ inv refl
      | True | vote ∷ (x ∷ xs) | True | True | True = {!!} -- contradiction: length vs ≡ 1

    tick-soundness s₀ inv refl
      | True | vote ∷ xs | _ | _ | _ = {!!}

    tick-soundness s₀ inv refl
      | True | [] = {!!} -- a vote is expected

    tick-soundness s₀ inv refl
      | False with NextSlotInSameRound? s₀
    tick-soundness {vs} {ms₁} s₀ inv refl
      | False
      | yes q =
        record
          { s₁ = s₁
          ; invariant₀ = inv
          ; invariant₁ = inv₁
          ; trace = trace
          ; s₁-agrees = s₁-agrees
          ; votes-agree = votes-agree
          }

      where

        tree : NodeModel
        tree = modelState s₀

        nextSlotNotNewRound : (suc (getSlotNumber (State.clock s₀)) % Params.U params ≡ᵇ 0) ≡ False
        nextSlotNotNewRound = /-% {x = getSlotNumber (State.clock s₀)} {n = Params.U params} q isSlotZero

        noCertsFromQuorum : certsFromQuorum (record tree { clock = nextSlot (clock tree) }) ≡ []
        noCertsFromQuorum = {!!} -- no new vote has been added

        s₁ : State
        s₁ = tick s₀

        s₁-agrees :
          record
            { clock        = State.clock s₁
            ; protocol     = modelParams
            ; allChains    = maybe′ chains [] (State.blockTrees s₁ ⁉ sutId)
            ; allVotes     = maybe′ votes  [] (State.blockTrees s₁ ⁉ sutId)
            ; allSeenCerts = maybe′ certs  [] (State.blockTrees s₁ ⁉ sutId)
            }
          ≡
          let s' = record tree { clock = nextSlot (clock tree) }
              s'' = record s' { allVotes = votesInState s' Haskell.++ allVotes s' }
          in
          record s'' { allSeenCerts = foldr insertCert (allSeenCerts s'') (certsFromQuorum s'') }
        s₁-agrees
          rewrite nextSlotNotNewRound
          rewrite noCertsFromQuorum
          = refl

        trace : s₀ ↝⋆ s₁
        trace = NextSlot (invFetched inv) q ↣ ∎

        votes-agree : sutVotesInTrace trace ≡ map (State.clock s₀ ,_) vs
        votes-agree rewrite nextSlotNotNewRound = refl

        fetched→[] : ∀ {s} → Fetched s → State.messages s ≡ []
        fetched→[] {s} x = {!!} -- all parties are honest and therefore there are no delayed messages

        fetched : ∀ {s} → Fetched s → Fetched (tick s) -- TODO: only if no delayed msgs...
        fetched {s} x
          rewrite fetched→[] {s} x
          = All.[]

        inv₁ : Invariant s₁
        inv₁ =
          record
            { invFetched = fetched {s₀} (invFetched inv)
            ; sutTree = existsTrees {sutId} {s₀} {s₁} (sutTree inv) trace
            }


    tick-soundness {vs} {ms₁} s₀ inv refl
      | False
      | no ¬q =
        record
          { s₁ = s₁
          ; invariant₀ = inv
          ; invariant₁ = inv₁
          ; trace = trace
          ; s₁-agrees = s₁-agrees
          ; votes-agree = votes-agree
          }

      where

        tree : NodeModel
        tree = modelState s₀

        s₁ : State
        s₁ = tick s₀

        lastSlotInRound :
            ¬ (getSlotNumber (State.clock s₀) / Params.U params
                ≡ suc (getSlotNumber (State.clock s₀)) / Params.U params)
          → LastSlotInRound s₀
        lastSlotInRound x = {!!}

        noCertsFromQuorum : certsFromQuorum (record tree { clock = nextSlot (clock tree) }) ≡ []
        noCertsFromQuorum = {!!} -- no new vote has been added

        noVoteInState : votesInState (record tree { clock = nextSlot (clock tree) }) ≡ []
        noVoteInState = {!!}

        s₁-agrees :
          record
            { clock        = State.clock s₁
            ; protocol     = modelParams
            ; allChains    = maybe′ chains [] (State.blockTrees s₁ ⁉ sutId)
            ; allVotes     = maybe′ votes  [] (State.blockTrees s₁ ⁉ sutId)
            ; allSeenCerts = maybe′ certs  [] (State.blockTrees s₁ ⁉ sutId)
            }
          ≡
          let s' = record tree { clock = nextSlot (clock tree) }
              s'' = record s' { allVotes = votesInState s' Haskell.++ allVotes s' }
          in
          record s'' { allSeenCerts = foldr insertCert (allSeenCerts s'') (certsFromQuorum s'') }
        s₁-agrees
          rewrite noVoteInState
          rewrite noCertsFromQuorum
          = refl

        trace : s₀ ↝⋆ s₁
        trace = NextSlotNewRound (invFetched inv) (lastSlotInRound ¬q) {!!} ↣ ∎

        votes-agree : sutVotesInTrace trace ≡ map (State.clock s₀ ,_) vs
        votes-agree rewrite noVoteInState = refl

        inv₁ : Invariant s₁
        inv₁ =
          record
            { invFetched = {!!}
            ; sutTree = existsTrees {sutId} {s₀} {s₁} (sutTree inv) trace
            }


    @0 soundness : ∀ {ms₁ vs} (s₀ : State) (a : EnvAction)
              → Invariant s₀
              → transition (modelState s₀) a ≡ Just (vs , ms₁)
              → Soundness s₀ ms₁ (map (State.clock s₀ ,_) vs)

    soundness s₀ (NewVote vote) = newVote-soundness s₀ vote
    soundness s₀ (NewChain chain) = newChain-soundness s₀ chain
    soundness s₀ Tick = tick-soundness s₀
