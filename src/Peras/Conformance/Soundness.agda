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
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)

open import Peras.Block
open import Peras.Chain
open import Peras.Crypto
open import Peras.Foreign using (checkSignedVote; checkSignedBlock; checkLeadershipProof)
open import Peras.Numbering
open import Peras.Params
open import Peras.Util
open import Prelude.AssocList
open import Prelude.Default
open import Prelude.DecEq hiding (_==_; _≟_)

open import Peras.Conformance.Params
open import Peras.Conformance.ProofPrelude

open import Peras.Conformance.Model as Model

module _ ⦃ _ : Hashable (List Tx) ⦄
         ⦃ postulates : Postulates ⦄
         {S : Set} {adversarialState₀ : S}
         {txSelection : SlotNumber → PartyId → List Tx}
    where

  -- The model introduces two parties, the sut (system under test) and
  -- an other one. Both are honest and there are no other parties.

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
    let f₁ = filter-accept (λ x → ¬? (otherId ≟ proj₁ x)) {sutId ⸴ Honest {sutId}} {(otherId ⸴ Honest {otherId}) ∷ []} uniqueIds
        f₂ = filter-reject (λ x → (proj₁ x ≟ sutId)) {(otherId ⸴ Honest {otherId})} {[]} uniqueIds
    in trans f₁ (cong ((sutId ⸴ Honest {sutId}) ∷_) f₂)

  apply-filter' : filter (λ x → ¬? (sutId ≟ proj₁ x)) parties ≡ (otherId ⸴ Honest {otherId}) ∷ []
  apply-filter' = filter-reject (λ x → (proj₁ x ≟ otherId)) {sutId ⸴ Honest {sutId}} {(otherId ⸴ Honest {otherId}) ∷ []} uniqueIds'

  -- The parameters are the ones defined in the test model

  modelParams : PerasParams
  modelParams = testParams

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

  import Peras.SmallStep as SmallStep

  module Assumptions
           (let open Postulates postulates)

           -- Currently we allow anyone to vote
           (axiom-everyoneIsOnTheCommittee :
             ∀ {p r prf} → IsCommitteeMember p r prf)

           (axiom-checkVoteSignature :
             ∀ {vote} → checkSignedVote vote ≡ True → IsVoteSignature vote (signature vote))

           (axiom-checkLeadershipProof :
             ∀ {block} → checkLeadershipProof (leadershipProof block) ≡ True
             → IsSlotLeader (creatorId block) (slotNumber block) (leadershipProof block))

           (axiom-checkBlockSignature :
             ∀ {block} → checkSignedBlock block ≡ True
             → IsBlockSignature block (signature block))

{-
           -- Assume that blocks are created correctly, as the model is not explicit about block creation
           (axiom-blockCreatedCorrectly :
             ∀ {block s} →
             block ≡ createBlock (clock s) (creatorId block) (leadershipProof block) (signature block) s)
-}

         where

    open SmallStep using (⦅_,_,_,_⦆)
    open SmallStep.Message

    open import Data.List.Membership.Propositional
    import Data.List.Relation.Unary.All as All

    postulate
      maximumBy-default-or-∈ : ∀ {a : Set} → (d : a) → (o : a → a → Ordering) → (l : List a)
        → maximumBy d o l ∈ d ∷ l

    valid-chain : ∀ (t : NodeModel) → ValidChain (pref t)
    valid-chain t = valid-chain' (pref t)
      where
        valid-chain' : ∀ (c : Chain) → ValidChain c
        valid-chain' [] = Genesis
        valid-chain' (b ∷ bs) =
          let checked-blockSignature = axiom-checkBlockSignature {b} {!!}
              checked-slotLeader = axiom-checkLeadershipProof {b} {!!}
          in Cons checked-blockSignature checked-slotLeader {!!} (valid-chain' bs)

{-
    valid-votes : ∀ (t : NodeModel) → All.All ValidVote (allVotes t)
    valid-votes t = valid-votes' (allVotes t)
      where
        valid-votes' : ∀ (l : List Vote) → All.All ValidVote l
        valid-votes' [] = All.[]
        valid-votes' (v ∷ vs) =
          let checked-membership =
                axiom-everyoneIsOnTheCommittee
                  {creatorId v}
                  {votingRound v}
                  {proofM v}
              checked-signature = axiom-checkVoteSignature {v} {!!}
          in (checked-membership ⸴ checked-signature) All.∷ (valid-votes' vs)
-}

    isTreeType :
      SmallStep.IsTreeType
        initialModelState
        newChain'
        allChains -- (λ t → genesisChain ∷ allChains t)
        pref
        addVote'
        allVotes
        allSeenCerts
        genesisCert

    isTreeType =
      record
        { instantiated = refl
        ; instantiated-certs = refl
        ; instantiated-votes = refl
        ; extendable-chain = λ _ _ → refl -- TODO: set union
        ; valid = valid-chain -- ?
        ; optimal = {!!} -- ok
        ; self-contained = {!!} -- λ t → maximumBy-default-or-∈ genesisChain _ (allChains t)
{-
        ; valid-votes = valid-votes
        ; unique-votes = {!!}
        ; no-equivocations = {!!}
-}
        ; quorum-cert = {!!}
        }

    NodeModelTree : SmallStep.TreeType NodeModel
    NodeModelTree = record { is-TreeType = isTreeType }

    open SmallStep.Semantics {NodeModel} {NodeModelTree} {S} {adversarialState₀} {txSelection} {parties}
    open SmallStep.TreeType NodeModelTree renaming (allChains to chains; preferredChain to prefChain)

    private
      instance
        Default-T : Default NodeModel
        Default-T .def = tree₀

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
    sutVotesInTrace ∎ = []
    sutVotesInTrace (step ↣ trace) = sutVotesInStep step ++ sutVotesInTrace trace

    postulate -- TODO
      filter-eq : ∀ {l : Chain} {f : Block → ℕ} {b : ℕ} →
        Haskell.filter (λ { a → (f a) <= b }) l ≡ filter (λ { a → (f a) ≤? b }) l

    blockSelection-eq :
      ∀ {s : State} →
      BlockSelection (State.clock s) (modelState s) ≡ votingBlockHash (modelState s)
    blockSelection-eq {s}
      rewrite
        sym (filter-eq
               {prefChain (modelState s)}
               {λ {x → getSlotNumber (slotNumber x) + (Params.L params)}}
               {getSlotNumber (State.clock s)})
      = refl

    -- Voting rules from the test-model to the small-step semantics

    f-1a : ∀ {s : State}
      → Vr1A (modelState s)
      → VotingRule-1A (v-round (State.clock s)) (modelState s)
    f-1a {s} x = cong getRoundNumber (sym x)

    f-1b : ∀ {s : State}
      → Vr1B (modelState s)
      → VotingRule-1B (State.clock s) (modelState s)
    f-1b {s} x
      rewrite
        filter-eq
          {prefChain (modelState s)}
          {λ {a → getSlotNumber (slotNumber a) + (Params.L params)}}
          {getSlotNumber (clock (modelState s))}
      = x

    f-2a : ∀ {s : State}
      → Vr2A (modelState s)
      → VotingRule-2A (v-round (State.clock s)) (modelState s)
    f-2a x = x

    f-2b : ∀ {s : State}
      → Vr2B (modelState s)
      → VotingRule-2B (v-round (State.clock s)) (modelState s)
    f-2b x = x

    -- Some postulates, resp. TODOs

    postulate -- TODO
      existsTrees : ∀ {p sᵢ sⱼ}
        → State.blockTrees sᵢ ⁉ p ≡ just (modelState sᵢ)
        → sᵢ ↝⋆ sⱼ
        → State.blockTrees sⱼ ⁉ p ≡ just (modelState sⱼ)

      fetched→[] : ∀ {s} → Fetched s → State.messages s ≡ []
      -- fetched→[] {s} x = {!!} -- all parties are honest and therefore there are no delayed messages

      lastSlotInRound : ∀ {s : State} → ¬ (NextSlotInSameRound s) → LastSlotInRound s
      {-
      lastSlotInRound {s} = lastSlotInRound' {s}
        where
          lastSlotInRound' : ∀ {s : State} →
            ¬ (rnd (getSlotNumber (State.clock s))
                   ≡ (rnd (suc (getSlotNumber (State.clock s)))))
            → LastSlotInRound s
          lastSlotInRound' x = {!!} -- suc (rnd (getSlotNumber clock)) ≡ rnd (suc (getSlotNumber clock))
      -}

      noCertsFromQuorum : ∀ {s : State} → Fetched s → certsFromQuorum (modelState s) ≡ []
      -- noCertsFromQuorum = {!!}

      noVotesAfterTick : ∀ {s₀ s₁}
        → voteInState (modelState s₀) ≡ Nothing
        → s₀ ↝⋆ s₁
        → voteInState (modelState s₁) ≡ Nothing
      -- noVotesAfterTick = {!!}

    fetched : ∀ {s} → Fetched s → Fetched (tick s) -- TODO: only if no delayed msgs...
    fetched {s} x
      rewrite fetched→[] {s} x
      = All.[]

    record Invariant (s : State) : Set where
      field
        invFetched : Fetched s
        sutTree : State.blockTrees s ⁉ sutId ≡ just (modelState s)
        otherTree : State.blockTrees s ⁉ otherId ≡ just (modelState s)

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
         | div (getSlotNumber (State.clock s₀)) (Params.U params)
             == getRoundNumber (votingRound vote) in isVotingRound
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

        slot₀ : SlotNumber
        slot₀ = State.clock s₀

        r : RoundNumber
        r = v-round slot₀

        notFromSut : creatorId vote ≢ sutId
        notFromSut x = uniqueIds (trans (sym (eqℕ-sound checkedOther)) x)

        tree : NodeModel
        tree = modelState s₀  -- we don't track the block trees for the environment nodes in the test model!

        startOfRound : StartOfRound slot₀ r
        startOfRound = lem-divMod _ _ (eqℕ-sound isSlotZero)

        σ : Signature
        σ = signature vote

        creatorId≡otherId : creatorId vote ≡ otherId
        creatorId≡otherId = eqℕ-sound checkedOther

        v : Vote
        v = createVote slot₀ (creatorId vote) (proofM vote) σ (blockHash vote)

        validVote : VotingRule slot₀ tree
        validVote = S.map
          (P.map (f-1a {s₀}) (f-1b {s₀}))
          (P.map (f-2a {s₀}) (f-2b {s₀}))
          (toWitness (isYes≡True⇒TTrue checkedVRs))

        vote-round : getRoundNumber (votingRound vote) ≡ rnd (getSlotNumber slot₀)
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

        creatorExists : State.blockTrees s₀ ⁉ (creatorId vote) ≡ just tree
        creatorExists
          rewrite creatorId≡otherId
          = otherTree inv

        sutExists :
          set (creatorId vote)
            (addVote tree v)
              (State.blockTrees s₀) ⁉ sutId ≡ just tree
        sutExists =
          trans
            (k'≢k-get∘set
              {k = sutId}
              {k' = creatorId vote}
              {v = addVote tree v}
              {m = State.blockTrees s₀}
              notFromSut)
            (sutTree inv)

        validBlockHash : BlockSelection (State.clock s₀) tree ≡ blockHash vote
        validBlockHash =
          MkHash-inj $
            trans
              (cong hashBytes (blockSelection-eq {s₀}))
              (lem-eqBS isValidBlockHash)

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

        tree⁺ : NodeModel
        tree⁺ = addVote' tree v

        bt₀ : AssocList ℕ NodeModel
        bt₀ = State.blockTrees s₀

        set-irrelevant :
          let s = record s₀
                    { blockTrees =
                        set sutId tree⁺
                          (set (creatorId vote) tree⁺ bt₀) }
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
                        set sutId tree⁺ bt₀ }
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
            {v  = tree⁺}
            {v' = tree⁺}
            {m  = State.blockTrees s₀}
            notFromSut = refl

        addVote-modelState :
          let s = record s₀
                    { blockTrees =
                        set sutId tree⁺ bt₀ }
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
            {v = tree⁺}
            {m = State.blockTrees s₀}
          rewrite correctVote
          = refl

        s₁-agrees : modelState s₁ ≡ ms₁
        s₁-agrees = trans set-irrelevant addVote-modelState

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
            ; otherTree = existsTrees {otherId} {s₀} {s₁} (otherTree inv) trace
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
      with (slotNumber block == State.clock s₀) in checkSlot
         | checkBlockFromOther block in checkedOther
         | (parentBlock block == headBlockHash rest) in checkHash
         | (rest == pref (modelState s₀)) in checkRest
         | checkSignedBlock block in checkedSig
         | checkLeadershipProof (leadershipProof block) in checkedLead
    newChain-soundness {vs} {ms₁} s₀ (block ∷ rest) inv refl
      | True | True | True | True | True | True =
      record
        { s₁ = s₁
        ; invariant₀ = inv
        ; invariant₁ = inv₁
        ; trace = trace
        ; s₁-agrees = s₁-agrees
        ; votes-agree = votes-agree
        }
      where

        slot₀ : SlotNumber
        slot₀ = State.clock s₀

        notFromSut : creatorId block ≢ sutId
        notFromSut x = uniqueIds (trans (sym (eqℕ-sound checkedOther)) x)

        tree : NodeModel
        tree = modelState s₀

        β : Block
        β = createBlock slot₀ (creatorId block) (leadershipProof block) (signature block) tree

        chain : Chain
        chain = β ∷ prefChain tree

        block-slotNumber : slotNumber block ≡ slot₀
        block-slotNumber = cong MkSlotNumber (eqℕ-sound checkSlot)

        validRest : rest ≡ prefChain tree
        validRest = eqList-sound checkRest

        headBlockHash≡tipHash : ∀ {c : Chain} → headBlockHash c ≡ tipHash c
        headBlockHash≡tipHash {[]} = refl
        headBlockHash≡tipHash {x ∷ c} = refl

        block-parentBlock : hashBytes (parentBlock block) ≡ hashBytes (tipHash rest)
        block-parentBlock
          rewrite sym (headBlockHash≡tipHash {rest})
          = eqBS-sound checkHash

        validHead : block ≡ β
        validHead = {!!} -- axiom-blockCreatedCorrectly {block} {tree}

        validSignature : IsBlockSignature β (signature β)
        validSignature with v ← axiom-checkBlockSignature checkedSig
          rewrite validHead rewrite validRest
          = v

        validChain : ValidChain
          (createBlock slot₀ (creatorId block) (leadershipProof block) (signature block) tree
            ∷ prefChain tree)
        validChain
          = let open SmallStep.IsTreeType
            in Cons validSignature (axiom-checkLeadershipProof {β} checkedLead) refl (is-TreeType .valid tree)

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

        creatorExists  : State.blockTrees s₀ ⁉ (creatorId block) ≡ just tree
        creatorExists
          rewrite creatorId≡otherId
          = otherTree inv

        sutExists :
          set (creatorId block)
            (newChain tree chain)
              (State.blockTrees s₀) ⁉ sutId ≡ just tree
        sutExists =
          trans
            (k'≢k-get∘set
              {k = sutId}
              {k' = creatorId block}
              {v = newChain tree chain}
              {m = State.blockTrees s₀}
              notFromSut)
            (sutTree inv)

        trace : s₀ ↝⋆ s₁
        trace = CreateBlock
                  (invFetched inv)
                  (honest
                    creatorExists
                    validChain
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
                      { allChains = chain ∷ allChains tree
                      ; allSeenCerts = foldr insertCert (allSeenCerts tree) (mapMaybe certificate chain)
                      }
                    )
                    (set
                      (creatorId block)
                      (record tree
                        { allChains = chain ∷ allChains tree
                        ; allSeenCerts = foldr insertCert (allSeenCerts tree) (mapMaybe certificate chain)
                        }
                      )
                      (State.blockTrees s₀)
                    )
              }
            )
            ≡ ms₁
        s₁-agrees
          rewrite validHead
          rewrite validRest
          = trans set-irrelevant newChain-modelState

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
            ; otherTree = existsTrees {otherId} {s₀} {s₁} (otherTree inv) trace
            }

    @0 tick-soundness : ∀ {vs ms₁} s₀
                          → Invariant s₀
                          → transition (modelState s₀) Tick ≡ Just (vs , ms₁)
                          → Soundness s₀ ms₁ (map (State.clock s₀ ,_) vs)
    tick-soundness s₀ inv refl
      with mod (getSlotNumber (State.clock s₀)) (Params.U params) == 0 in isSlotZero

    tick-soundness {vs} s₀ inv refl
      | True
      with vs

    tick-soundness s₀ inv refl
      | True
      | vote ∷ xs
      with   checkSignedVote vote in checkedSig
           | isYes (checkVotingRules (modelState s₀)) in checkedVRs
           | votingBlockHash (modelState s₀) == blockHash vote in isValidBlockHash
           | div (getSlotNumber (State.clock s₀)) (Params.U params)
               == getRoundNumber (votingRound vote) in isVotingRound
           | checkVoteFromSut vote in checkedSut

    tick-soundness {vs} {ms₁} s₀ inv refl
      | True | vote ∷ [] | True | True | True | True | True =

        record
          { s₁ = s₁
          ; invariant₀ = inv
          ; invariant₁ = inv₁
          ; trace = trace
          ; s₁-agrees = s₁-agrees
          ; votes-agree = votes-agree
          }
        where

          slot₀ : SlotNumber
          slot₀ = State.clock s₀

          r : RoundNumber
          r = v-round slot₀

          tree : NodeModel
          tree = modelState s₀

          v : Vote
          v = createVote slot₀ sutId (proofM vote) (signature vote) (blockHash vote)

          startOfRound : StartOfRound slot₀ r
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

          validVote : VotingRule slot₀ tree
          validVote = S.map
            (P.map (f-1a {s₀}) (f-1b {s₀}))
            (P.map (f-2a {s₀}) (f-2b {s₀}))
            (toWitness (isYes≡True⇒TTrue checkedVRs))

          validBlockHash : BlockSelection slot₀ tree ≡ blockHash vote
          validBlockHash =
            MkHash-inj $
              trans
                (cong hashBytes (blockSelection-eq {s₀}))
                (lem-eqBS isValidBlockHash)

          vote-round : getRoundNumber (votingRound vote) ≡ rnd (getSlotNumber slot₀)
          vote-round = sym (eqℕ-sound isVotingRound)

          creatorId≡sutId : creatorId vote ≡ sutId
          creatorId≡sutId = eqℕ-sound checkedSut

          correctVote : vote ≡ v
          correctVote = {!!} -- cong (λ {r → record vote { votingRound = MkRoundNumber r}}) vote-round

          validSignature : IsVoteSignature v (signature v)
          validSignature with v ← axiom-checkVoteSignature checkedSig
            rewrite correctVote rewrite creatorId≡sutId
            = v

          otherExists : set sutId (addVote tree v) (State.blockTrees s₀) ⁉ otherId ≡ just tree
          otherExists =
            trans
              (k'≢k-get∘set {k = otherId} {k' = sutId} {v = addVote tree v} {m = State.blockTrees s₀} uniqueIds')
              (otherTree inv)

          postulate -- TODO
            -- U = 5
            noNewRound : rnd (getSlotNumber slot₀) ≡ rnd (suc (getSlotNumber slot₀))

          nextSlotInSameRound : NextSlotInSameRound s₀
          nextSlotInSameRound = noNewRound

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
                ↣ NextSlot (invFetched inv) nextSlotInSameRound
                ↣ ∎

          tree⁺ : NodeModel
          tree⁺ = addVote' tree v

          blockTrees₀ : AssocList ℕ NodeModel
          blockTrees₀ = State.blockTrees s₀

          set-irrelevant :
            let s = record s₀
                      { blockTrees =
                          set otherId tree⁺
                            (set sutId tree⁺ blockTrees₀) }
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
                          set sutId tree⁺ blockTrees₀ }
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
              {v  = tree⁺}
              {m  = set sutId tree⁺ blockTrees₀}
              uniqueIds = refl

          addVote-modelState :
            let s = record s₀
                      { blockTrees =
                          set sutId tree⁺ blockTrees₀ }
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
                      { clock    = MkSlotNumber (suc (getSlotNumber slot₀))
                      ; allVotes = vote ∷ maybe′ votes [] (State.blockTrees s₀ ⁉ sutId)
                      }
            in record s { allSeenCerts = foldr insertCert (allSeenCerts s) (certsFromQuorum s) }
          addVote-modelState
            rewrite get∘set≡id
              {k = sutId}
              {v = tree⁺}
              {m = blockTrees₀}
            rewrite correctVote
            = refl

          s₁-agrees :
            modelState s₁ ≡
            let s = record tree
                    { clock = MkSlotNumber (suc (getSlotNumber slot₀))
                    ; allVotes = vote ∷ maybe′ votes [] (State.blockTrees s₀ ⁉ sutId)
                    }
            in record s { allSeenCerts = foldr insertCert (allSeenCerts s) (certsFromQuorum s) }
          s₁-agrees = trans set-irrelevant addVote-modelState

          votes-agree : sutVotesInTrace trace ≡ (slot₀ , vote) ∷ map (slot₀ ,_) []
          votes-agree rewrite correctVote = refl

          msg₀≡msg₁ : State.messages s₀ ≡ (msg ++ State.messages s₀) ─ other∈messages
          msg₀≡msg₁ rewrite map∘apply-filter = refl

          inv₁ : Invariant s₁
          inv₁ with i ← invFetched inv rewrite msg₀≡msg₁ =
            record
              { invFetched = let open State s₀ in
                fetched {
                  record s₀
                    { blockTrees =
                        set otherId (addVote tree v)
                          (set sutId (addVote tree v)
                            blockTrees)
                    ; messages = (msg ++ messages) ─ other∈messages
                    ; history = VoteMsg v ∷ history
                    }
                  } i
              ; sutTree = existsTrees {sutId} {s₀} {s₁} (sutTree inv) trace
              ; otherTree = existsTrees {otherId} {s₀} {s₁} (otherTree inv) trace
              }

    tick-soundness {vs} s₀ inv refl
      | True | vote ∷ (x ∷ xs) | True | True | True | True | True = {!!} -- contradiction: length vs ≡ 1

    tick-soundness {vs} s₀ inv refl
      | True | vote ∷ xs | _ | _ | _ | _ | _ = {!!} -- precondition does not hold for vote

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

        slot₀ : SlotNumber
        slot₀ = State.clock s₀

        tree : NodeModel
        tree = modelState s₀

        nextSlotNotNewRound : (suc (getSlotNumber slot₀) % Params.U params ≡ᵇ 0) ≡ False
        nextSlotNotNewRound = /-% {x = getSlotNumber slot₀} {n = Params.U params} q isSlotZero

        s₁ : State
        s₁ = tick s₀

        invFetched₁ : Fetched s₁
        invFetched₁ = fetched {s₀} (invFetched inv)

        s₁-agrees :
          record
            { clock        = State.clock s₁
            ; protocol     = modelParams
            ; allChains    = maybe′ chains [] (State.blockTrees s₁ ⁉ sutId)
            ; allVotes     = maybe′ votes  [] (State.blockTrees s₁ ⁉ sutId)
            ; allSeenCerts = maybe′ certs  [] (State.blockTrees s₁ ⁉ sutId)
            }
          ≡ ms₁
        s₁-agrees
          rewrite nextSlotNotNewRound
          rewrite noCertsFromQuorum {s₁} invFetched₁
          = refl

        trace : s₀ ↝⋆ s₁
        trace = NextSlot (invFetched inv) q ↣ ∎

        votes-agree : sutVotesInTrace trace ≡ map (slot₀ ,_) vs
        votes-agree rewrite nextSlotNotNewRound = refl

        inv₁ : Invariant s₁
        inv₁ =
          record
            { invFetched = invFetched₁
            ; sutTree = existsTrees {sutId} {s₀} {s₁} (sutTree inv) trace
            ; otherTree = existsTrees {otherId} {s₀} {s₁} (otherTree inv) trace
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

        slot₀ : SlotNumber
        slot₀ = State.clock s₀

        tree : NodeModel
        tree = modelState s₀

        s₁ : State
        s₁ = tick s₀

        invFetched₁ : Fetched s₁
        invFetched₁ = fetched {s₀} (invFetched inv)

        req : RequiredVotes s₀
        req = {!!} -- FIXME: ?

        lastInRound : LastSlotInRound s₀
        lastInRound = lastSlotInRound {s₀} ¬q

        trace : s₀ ↝⋆ s₁
        trace = NextSlotNewRound (invFetched inv) lastInRound req ↣ ∎

        noVoteInState₀ : voteInState (modelState s₀) ≡ Nothing
        noVoteInState₀ rewrite isSlotZero = refl

        noVoteInState : voteInState (record tree { clock = nextSlot (clock tree) }) ≡ Nothing
        noVoteInState = noVotesAfterTick {s₀} {s₁} noVoteInState₀ trace

        s₁-agrees : modelState s₁ ≡ ms₁
        s₁-agrees
          rewrite noVoteInState
          rewrite noCertsFromQuorum {s₁} invFetched₁
          = refl

        votes-agree : sutVotesInTrace trace ≡ map (slot₀ ,_) vs
        votes-agree rewrite noVoteInState = refl

        inv₁ : Invariant s₁
        inv₁ =
          record
            { invFetched = invFetched₁
            ; sutTree = existsTrees {sutId} {s₀} {s₁} (sutTree inv) trace
            ; otherTree = existsTrees {otherId} {s₀} {s₁} (otherTree inv) trace
            }


    @0 soundness : ∀ {ms₁ vs} (s₀ : State) (a : EnvAction)
              → Invariant s₀
              → transition (modelState s₀) a ≡ Just (vs , ms₁)
              → Soundness s₀ ms₁ (map (State.clock s₀ ,_) vs)

    soundness s₀ (NewVote vote) = newVote-soundness s₀ vote
    soundness s₀ (NewChain chain) = newChain-soundness s₀ chain
    soundness s₀ Tick = tick-soundness s₀
    soundness s₀ (BadVote vote) = {!!}
