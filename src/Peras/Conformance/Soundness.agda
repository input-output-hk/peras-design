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
open import Data.Product as P using (proj₁ ; proj₂) renaming (_,_ to _,ᵖ_)
open import Relation.Nullary.Decidable using (Dec; yes; no; ¬?)

open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)

open import Prelude.AssocList
open import Prelude.Default
open import Prelude.DecEq hiding (_==_; _≟_)

open import Peras.Block
open import Peras.Chain
open import Peras.Crypto
open import Peras.Foreign using (checkSignedVote; checkSignedBlock; checkLeadershipProof)
open import Peras.Numbering
open import Peras.Params
open import Peras.Util

open import Peras.Conformance.Params
open import Peras.Conformance.ProofPrelude hiding (⊥-elim)
open import Peras.Conformance.Model as Model

module _ ⦃ _ : Hashable (List Tx) ⦄
         ⦃ postulates : Postulates ⦄
         {S : Set} {adversarialState₀ : S}
         {txSelection : SlotNumber → PartyId → List Tx}
    where

  -- The model introduces two parties, the sut (system under test) and
  -- an other one. Both are honest and there are no other parties.

  otherId≢sutId : otherId ≢ sutId
  otherId≢sutId = λ ()

  sutId≢otherId : sutId ≢ otherId
  sutId≢otherId = λ ()

  parties : Parties
  parties = (sutId ,ᵖ Honest {sutId}) ∷ (otherId ,ᵖ Honest {otherId}) ∷ [] -- wlog

  sut∈parties : (sutId ,ᵖ Honest {sutId}) ∈ parties
  sut∈parties = Any.here refl

  sutHonesty : Honesty sutId
  sutHonesty = proj₂ (Any.lookup sut∈parties)

  other∈parties : (otherId ,ᵖ Honest {otherId}) ∈ parties
  other∈parties = Any.there (Any.here refl)

  otherHonesty : Honesty otherId
  otherHonesty = proj₂ (Any.lookup other∈parties)

  -- The parameters are the ones defined in the test model

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

         where

    import Peras.SmallStep as SmallStep
    open SmallStep using (⦅_,_,_,_⦆)
    open SmallStep.Message

    open import Data.List.Membership.Propositional
    import Data.List.Relation.Unary.All as All

    postulate
      maximumBy-default-or-∈ : ∀ {a : Set} → (d : a) → (o : a → a → Ordering) → (l : List a)
        → maximumBy d o l ∈ d ∷ l

    addChain'' : NodeModel → {c : Chain} → ValidChain c → NodeModel
    addChain'' s {c} _ = addChain' s c

    addVote'' : NodeModel → {v : Vote} → ValidVote v → NodeModel
    addVote'' s {v} _ = addVote' s v

    {-
    allChains' : NodeModel → List Chain
    allChains' t with (allChains t) == []
    ... | True = genesisChain ∷ []
    ... | False = allChains t
    -}

    isTreeType :
      SmallStep.IsTreeType
        initialModelState
        addChain''
        allChains -- (λ t → genesisChain ∷ allChains t)
        pref
        addVote''
        allVotes
        allSeenCerts
        genesisCert

    isTreeType =
      record
        { instantiated = refl
        ; instantiated-certs = refl
        ; instantiated-votes = refl
        ; extendable-chain = λ _ _ → refl -- TODO: set union
        ; valid = {!!}
        ; optimal = {!!} -- ok
        ; self-contained = {!!} -- λ t → maximumBy-default-or-∈ genesisChain _ (allChains t)
        ; unique-votes = {!!}
        ; no-equivocations = {!!}
--        ; quorum-cert = {!!} -- invariants
        }

    NodeModelTree : SmallStep.TreeType NodeModel
    NodeModelTree = record { is-TreeType = isTreeType }

    open SmallStep.Semantics {NodeModel} {NodeModelTree} {S} {adversarialState₀} {txSelection} {parties}
    open SmallStep.TreeType NodeModelTree renaming (preferredChain to prefChain)

    private
      instance
        Default-T : Default NodeModel
        Default-T .def = tree₀

    modelState : State → NodeModel
    modelState s = record
      { clock        = State.clock s
      ; protocol     = testParams
      ; allChains    = maybe′ chains [] (State.blockTrees s ⁉ sutId)
      ; allVotes     = maybe′ votes  [] (State.blockTrees s ⁉ sutId)
      ; allSeenCerts = maybe′ certs  [] (State.blockTrees s ⁉ sutId)
      }

    sutVotesInStep : ∀ {s₀ s₁} → s₀ ↝ s₁ → List (SlotNumber × Vote)
    sutVotesInStep (Fetch _) = []
    sutVotesInStep (CreateBlock _ _) = []
    sutVotesInStep (NextSlot _) = []
    sutVotesInStep {s₀} (CreateVote _ (honest {p} {t} {M} {π} {σ} {b} _ _ _ _ _ _))
      with p ≟ sutId
    ... | (yes _) = (State.clock s₀ , createVote (State.clock M) p π σ b) ∷ []
    ... | (no _)  = []

    sutVotesInTrace : ∀ {s₀ s₁} → s₀ ↝⋆ s₁ → List (SlotNumber × Vote)
    sutVotesInTrace ∎ = []
    sutVotesInTrace (step ↣ trace) = sutVotesInStep step ++ sutVotesInTrace trace

    blockSelection-eq : ∀ {s : State} →
      BlockSelection (State.clock s) (modelState s) ≡ votingBlockHash (modelState s)
    blockSelection-eq = refl

    postulate -- TODO
      existsTrees : ∀ {p sᵢ sⱼ}
        → State.blockTrees sᵢ ⁉ p ≡ just (modelState sᵢ)
        → sᵢ ↝⋆ sⱼ
        → State.blockTrees sⱼ ⁉ p ≡ just (modelState sⱼ)

      fetched→[] : ∀ {s} → Fetched s → State.messages s ≡ []
      -- fetched→[] {s} x = {!!} -- all parties are honest and therefore there are no delayed messages

      noCertsFromQuorum : ∀ {s : State} → Fetched s → certsFromQuorum (modelState s) ≡ []
      -- noCertsFromQuorum = {!!}

    fetched : ∀ {s} → Fetched s → Fetched (tick s)
    fetched {s} x
      rewrite fetched→[] {s} x
      = allNil

    record Invariant (s : State) : Set where
      field
        invFetched : Fetched s
        sutTree : State.blockTrees s ⁉ sutId ≡ just (modelState s)
        otherTree : State.blockTrees s ⁉ otherId ≡ just (modelState s)
{-
        no-equivocations : ∀ (t : T) (v : Vote)
          → let vs = votes t
            in
            Any (v ∻_) vs
          → vs ≡ votes (addVote t v)
-}

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

    @0 newVote-soundness : ∀ {cs vs ms₁} s₀ vote
                          → Invariant s₀
                          → transition (modelState s₀) (NewVote vote) ≡ Just ((cs , vs) , ms₁)
                          → Soundness s₀ ms₁ (map (State.clock s₀ ,_) vs)

    newVote-soundness s₀ vote inv prf
      with mod (getSlotNumber (State.clock s₀)) (Params.U params) == 0 in isSlotZero
         | div (getSlotNumber (State.clock s₀)) (Params.U params)
             == getRoundNumber (votingRound vote) in isVotingRound
         | checkSignedVote vote in checkedSig
         | checkVoteFromOther vote in checkedOther
         | isYes (checkVotingRules (modelState s₀)) in checkedVRs
         | votingBlockHash (modelState s₀) == blockHash vote in isValidBlockHash
    newVote-soundness {cs} {vs} {ms₁} s₀ vote inv refl | True | True | True | True | True | True =
      record
        { s₁          = s₁
        ; invariant₀  = inv
        ; invariant₁  = inv₁
        ; trace       = trace
        ; s₁-agrees   = s₁-agrees
        ; votes-agree = votes-agree
        }
      where
        open State s₀ renaming (clock to slot)

        tree : NodeModel
        tree = modelState s₀  -- we don't track the block trees for the environment nodes in the test model!

        startOfRound : StartOfRound slot (v-round slot)
        startOfRound = lem-divMod _ _ (eqℕ-sound isSlotZero)

        notFromSut : creatorId vote ≢ sutId
        notFromSut x = otherId≢sutId (trans (sym (eqℕ-sound checkedOther)) x)

        creatorId≡otherId : creatorId vote ≡ otherId
        creatorId≡otherId = eqℕ-sound checkedOther

        otherId≡creatorId : otherId ≡ creatorId vote
        otherId≡creatorId = sym creatorId≡otherId

        σ : Signature
        σ = signature vote

        v : Vote
        v = createVote slot (creatorId vote) (proofM vote) σ (blockHash vote)

        votingRound≡rnd-slot : getRoundNumber (votingRound vote) ≡ rnd (getSlotNumber slot)
        votingRound≡rnd-slot = sym (eqℕ-sound isVotingRound)

        vote≡v : vote ≡ v
        vote≡v = cong (λ {r → record vote { votingRound = MkRoundNumber r}}) votingRound≡rnd-slot

        validSignature : IsVoteSignature v σ
        validSignature with v' ← axiom-checkVoteSignature checkedSig rewrite vote≡v = v'

        ν : ValidVote v
        ν = axiom-everyoneIsOnTheCommittee , validSignature

        validVote : VotingRule slot tree
        validVote = toWitness (isYes≡True⇒TTrue checkedVRs)

        s₁ : State
        s₁ = record s₀
               { blockTrees =
                   set otherId (addVote tree ν)
                     (set sutId (addVote tree ν)
                       blockTrees)
               ; history = VoteMsg ν ∷ history
               }

        creatorExists : blockTrees ⁉ (creatorId vote) ≡ just tree
        creatorExists rewrite creatorId≡otherId = otherTree inv

        otherExists :
          set sutId
            (addVote tree ν)
              blockTrees ⁉ otherId ≡ just tree
        otherExists =
             trans
               (k'≢k-get∘set {k = otherId} {k' = sutId} {v = addVote tree ν} {m = blockTrees} sutId≢otherId)
               (otherTree inv)

        validBlockHash : BlockSelection slot tree ≡ blockHash vote
        validBlockHash =
          MkHash-inj $
            trans
              (cong hashBytes (blockSelection-eq {s₀}))
              (lem-eqBS isValidBlockHash)

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
              ↣ Fetch {m = VoteMsg ν}
                  (honest
                    (sutTree inv)
                    (Any.here refl)
                    VoteReceived
                  )
              ↣ Fetch {m = VoteMsg ν}
                  (honest
                    otherExists
                    (Any.here refl)
                    VoteReceived
                  )
              ↣ ∎

        tree⁺ : NodeModel
        tree⁺ = addVote tree ν

        s₁-agrees :
          let s = record s₀
                    { blockTrees =
                        set otherId tree⁺
                          (set sutId tree⁺ blockTrees) }
          in
          record
            { clock        = State.clock s
            ; protocol     = testParams
            ; allChains    = maybe′ chains [] (State.blockTrees s ⁉ sutId)
            ; allVotes     = maybe′ votes  [] (State.blockTrees s ⁉ sutId)
            ; allSeenCerts = maybe′ certs  [] (State.blockTrees s ⁉ sutId)
            }
          ≡ ms₁
        s₁-agrees
          rewrite
            k'≢k-get∘set
              {k = sutId}
              {k' = otherId}
              {v = tree⁺}
              {m = set sutId tree⁺ blockTrees}
              otherId≢sutId
          rewrite get∘set≡id
            {k = sutId}
            {v = tree⁺}
            {m = blockTrees}
          rewrite vote≡v
          = refl

        votes-agree : sutVotesInTrace trace ≡ map (slot ,_) vs
        votes-agree with creatorId vote ≟ sutId
        ... | yes p = ⊥-elim (notFromSut p)
        ... | no _  = refl

        inv₁ : Invariant s₁
        inv₁ =
          record
            { invFetched = invFetched inv
            ; sutTree = existsTrees {sutId} {s₀} {s₁} (sutTree inv) trace
            ; otherTree = existsTrees {otherId} {s₀} {s₁} (otherTree inv) trace
            }

    @0 newChain-soundness : ∀ {cs vs ms₁} s₀ chain
                          → Invariant s₀
                          → transition (modelState s₀) (NewChain chain) ≡ Just ((cs , vs) , ms₁)
                          → Soundness s₀ ms₁ (map (State.clock s₀ ,_) vs)
    newChain-soundness s₀ (block ∷ rest) inv prf
      with (slotNumber block == State.clock s₀) in checkSlot
         | checkBlockFromOther block in checkedOther
         | (parentBlock block == tipHash rest) in checkHash
         | (rest == pref (modelState s₀)) in checkRest
         | checkSignedBlock block in checkedSig
         | checkLeadershipProof (leadershipProof block) in checkedLead
    newChain-soundness {cs} {vs} {ms₁} s₀ (block ∷ rest) inv refl
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
        open State s₀ renaming (clock to slot)

        tree : NodeModel
        tree = modelState s₀

        notFromSut : creatorId block ≢ sutId
        notFromSut x = otherId≢sutId (trans (sym (eqℕ-sound checkedOther)) x)

        creatorId≡otherId : creatorId block ≡ otherId
        creatorId≡otherId = eqℕ-sound checkedOther

        β : Block
        β = createBlock slot otherId (leadershipProof block) (signature block) tree

        slotNumber≡slot : slotNumber block ≡ slot
        slotNumber≡slot = cong MkSlotNumber (eqℕ-sound checkSlot)

        rest≡pref : rest ≡ prefChain tree
        rest≡pref = eqList-sound checkRest

        block-parentBlock : hashBytes (parentBlock block) ≡ hashBytes (tipHash rest)
        block-parentBlock = eqBS-sound checkHash

        parent≡tip : parentBlock block ≡ tipHash rest
        parent≡tip = MkHash-inj block-parentBlock

        cert≡needCert : certificate block ≡ needCert (v-round slot) tree
        cert≡needCert = {!!} -- TODO: guards in transition

        bodyHash≡txsHash :
          bodyHash block ≡
            let txs = txSelection slot (creatorId block)
                open Hashable ⦃...⦄
            in blockHash
                 record
                   { blockHash = hash txs
                   ; payload = txs
                   }
        bodyHash≡txsHash = {!!} -- TODO: txSelection/hash from model

        block≡β : block ≡ β
        block≡β
          with v ←
          cong
            (λ i →  record
                      { slotNumber = i
                      ; creatorId = creatorId block
                      ; parentBlock = parentBlock block
                      ; certificate = certificate block
                      ; leadershipProof = leadershipProof block
                      ; bodyHash = bodyHash block
                      ; signature = signature block
                      })
            slotNumber≡slot
          rewrite parent≡tip
          rewrite cert≡needCert
          rewrite bodyHash≡txsHash
          rewrite rest≡pref
          rewrite creatorId≡otherId
          = v

        validSignature : IsBlockSignature β (signature β)
        validSignature with v ← axiom-checkBlockSignature checkedSig
          rewrite block≡β
          rewrite rest≡pref
          = v

        chain : ValidChain (β ∷ prefChain tree)
        chain
          = let open SmallStep.IsTreeType
            in Cons {prefChain tree} {β}
              validSignature
              (axiom-checkLeadershipProof {β} checkedLead)
              refl
              (is-TreeType .valid tree)

        s₁ : State
        s₁ = record s₀
               { blockTrees =
                   set otherId (addChain tree chain)
                     (set sutId (addChain tree chain)
                       blockTrees)
               ; history = ChainMsg chain ∷ history
               }

        otherExists :
          set sutId
            (addChain tree chain)
              blockTrees ⁉ otherId ≡ just tree
        otherExists =
          trans
            (k'≢k-get∘set
              {k = otherId}
              {k' = sutId}
              {v = addChain tree chain}
              {m = blockTrees}
              sutId≢otherId)
            (otherTree inv)

        trace : s₀ ↝⋆ s₁
        trace = CreateBlock (invFetched inv)
                  (honest
                    (otherTree inv)
                    chain
                  )
              ↣ Fetch {m = ChainMsg chain}
                  (honest {p = sutId}
                    (sutTree inv)
                    (Any.here refl)
                    ChainReceived
                  )
              ↣ Fetch {m = ChainMsg chain}
                  (honest {p = otherId}
                    otherExists
                    (Any.here refl)
                    ChainReceived
                  )
              ↣ ∎

        s₁-agrees :
          let s = record s₀
                    { blockTrees =
                        set otherId (addChain tree chain)
                        (set sutId (addChain tree chain)
                          blockTrees) }
          in
          record
            { clock        = State.clock s
            ; protocol     = testParams
            ; allChains    = maybe′ chains [] (State.blockTrees s ⁉ sutId)
            ; allVotes     = maybe′ votes  [] (State.blockTrees s ⁉ sutId)
            ; allSeenCerts = maybe′ certs  [] (State.blockTrees s ⁉ sutId)
            }
          ≡ ms₁
        s₁-agrees
          rewrite
            k'≢k-get∘set
              {k = sutId}
              {k' = otherId}
              {v = addChain tree chain}
              {m = set sutId (addChain tree chain) blockTrees}
              otherId≢sutId
          rewrite
            get∘set≡id
              {k = sutId}
              {v = addChain tree chain}
              {m = blockTrees}
          rewrite block≡β
          rewrite rest≡pref
          = refl

        votes-agree : sutVotesInTrace trace ≡ map (slot ,_) vs
        votes-agree with creatorId block ≟ sutId
        ... | yes p = ⊥-elim (notFromSut p)
        ... | no _  = refl

        inv₁ : Invariant s₁
        inv₁ =
          record
            { invFetched = invFetched inv
            ; sutTree = existsTrees {sutId} {s₀} {s₁} (sutTree inv) trace
            ; otherTree = existsTrees {otherId} {s₀} {s₁} (otherTree inv) trace
            }


    @0 tick-soundness : ∀ {cs vs ms₁} s₀
                          → Invariant s₀
                          → transition (modelState s₀) Tick ≡ Just ((cs , vs) , ms₁)
                          → Soundness s₀ ms₁ (map (State.clock s₀ ,_) vs)
    tick-soundness s₀ inv refl
      with mod (getSlotNumber (State.clock s₀)) (Params.U params) == 0 in isSlotZero

    tick-soundness {cs} {vs} s₀ inv refl
      | True
      with vs
      with cs

    tick-soundness s₀ inv refl
      | True
      | vote ∷ xs
      | []
      with   checkSignedVote vote in checkedSig
           | isYes (checkVotingRules (modelState s₀)) in checkedVRs
           | votingBlockHash (modelState s₀) == blockHash vote in isValidBlockHash
           | div (getSlotNumber (State.clock s₀)) (Params.U params)
               == getRoundNumber (votingRound vote) in isVotingRound
           | checkVoteFromSut vote in checkedSut

    tick-soundness {cs} {vs} {ms₁} s₀ inv refl
      | True | vote ∷ [] | [] | True | True | True | True | True =

        record
          { s₁ = s₁
          ; invariant₀ = inv
          ; invariant₁ = inv₁
          ; trace = trace
          ; s₁-agrees = s₁-agrees
          ; votes-agree = votes-agree
          }
        where
          open State s₀ renaming (clock to slot)

          r : RoundNumber
          r = v-round slot

          tree : NodeModel
          tree = modelState s₀

          w' : Vote
          w' = createVote slot (creatorId vote) (proofM vote) (signature vote) (blockHash vote)

          w : Vote
          w = createVote slot sutId (proofM vote) (signature vote) (blockHash vote)

          votingRound≡rnd-slot : getRoundNumber (votingRound vote) ≡ rnd (getSlotNumber slot)
          votingRound≡rnd-slot = sym (eqℕ-sound isVotingRound)

          vote≡w' : vote ≡ w'
          vote≡w' = cong (λ {r → record vote { votingRound = MkRoundNumber r}}) votingRound≡rnd-slot

          creatorId≡sutId : creatorId vote ≡ sutId
          creatorId≡sutId = eqℕ-sound checkedSut

          w≡w' : w ≡ w'
          w≡w' = cong (λ {r → record w' { creatorId = r}}) (sym creatorId≡sutId)

          vote≡w : vote ≡ w
          vote≡w = trans vote≡w' (sym w≡w')

          validSignature : IsVoteSignature w (signature w)
          validSignature with v ← axiom-checkVoteSignature checkedSig
            rewrite vote≡w
            = v

          v : ValidVote w
          v = axiom-everyoneIsOnTheCommittee , validSignature

          startOfRound : StartOfRound slot r
          startOfRound = lem-divMod _ _ (eqℕ-sound isSlotZero)

          s₁ : State
          s₁ = tick record s₀
                 { blockTrees =
                     set otherId (addVote tree v)
                       (set sutId (addVote tree v)
                         blockTrees)
                 ; history = VoteMsg v ∷ history
                 }

          validVote : VotingRule slot tree
          validVote = toWitness (isYes≡True⇒TTrue checkedVRs)

          validBlockHash : BlockSelection slot tree ≡ blockHash vote
          validBlockHash =
            MkHash-inj $
              trans
                (cong hashBytes (blockSelection-eq {s₀}))
                (lem-eqBS isValidBlockHash)

          otherExists : set sutId (addVote tree v) blockTrees ⁉ otherId ≡ just tree
          otherExists =
            trans
              (k'≢k-get∘set {k = otherId} {k' = sutId} {v = addVote tree v} {m = blockTrees} sutId≢otherId)
              (otherTree inv)

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
                ↣ Fetch {m = VoteMsg v}
                    (honest {p = sutId}
                      (sutTree inv)
                      (Any.here refl)
                      VoteReceived
                    )
                ↣ Fetch {m = VoteMsg v}
                    (honest {p = otherId}
                      otherExists
                      (Any.here refl)
                      VoteReceived
                    )
                ↣ NextSlot (invFetched inv)
                ↣ ∎

          tree⁺ : NodeModel
          tree⁺ = addVote tree v

          s₁-agrees :
            let s = record s₀
                      { blockTrees =
                          set otherId tree⁺
                            (set sutId tree⁺ blockTrees) }
            in
            record
              { clock        = MkSlotNumber (suc (getSlotNumber (State.clock s)))
              ; protocol     = testParams
              ; allChains    = maybe′ chains [] (State.blockTrees s ⁉ sutId)
              ; allVotes     = maybe′ votes  [] (State.blockTrees s ⁉ sutId)
              ; allSeenCerts = maybe′ certs  [] (State.blockTrees s ⁉ sutId)
              }
            ≡
            let s = record tree
                    { clock = MkSlotNumber (suc (getSlotNumber slot))
                    ; allVotes = vote ∷ maybe′ votes [] (blockTrees ⁉ sutId)
                    }
            in record s { allSeenCerts = foldr insertCert (allSeenCerts s) (certsFromQuorum s) }
          s₁-agrees
            rewrite k'≢k-get∘set
              {k  = sutId}
              {k' = otherId}
              {v  = tree⁺}
              {m  = set sutId tree⁺ blockTrees}
              otherId≢sutId
            rewrite get∘set≡id
              {k = sutId}
              {v = tree⁺}
              {m = blockTrees}
            rewrite vote≡w
            = refl

          votes-agree : sutVotesInTrace trace ≡ (slot , vote) ∷ map (slot ,_) []
          votes-agree rewrite vote≡w = refl

          inv₁ : Invariant s₁
          inv₁ =
            record
              { invFetched =
                  fetched {
                    record s₀
                      { blockTrees =
                          set otherId (addVote tree v)
                            (set sutId (addVote tree v)
                              blockTrees)
                      ; history = VoteMsg v ∷ history
                      }
                    } (invFetched inv)
              ; sutTree = existsTrees {sutId} {s₀} {s₁} (sutTree inv) trace
              ; otherTree = existsTrees {otherId} {s₀} {s₁} (otherTree inv) trace
              }

    tick-soundness {cs} {vs} {ms₁} s₀ inv refl
      | True | vote ∷ [] | [] | _ | _ | _ | _ | _ = {!!}

    tick-soundness s₀ inv refl
      | True
      | vote ∷ xs
      | (block ∷ rest) ∷ ys
      with   checkSignedVote vote in checkedSig
           | isYes (checkVotingRules (modelState s₀)) in checkedVRs
           | votingBlockHash (modelState s₀) == blockHash vote in isValidBlockHash
           | div (getSlotNumber (State.clock s₀)) (Params.U params)
               == getRoundNumber (votingRound vote) in isVotingRound
           | checkVoteFromSut vote in checkedSut

           | (slotNumber block == State.clock s₀) in checkSlot
           | checkBlockFromSut block in checkedBlockSut
           | (parentBlock block == tipHash rest) in checkHash
           | (rest == pref (modelState s₀)) in checkRest -- FIXME: modelState s'
           | checkSignedBlock block in checkedBlockSig
           | checkLeadershipProof (leadershipProof block) in checkedLead


    tick-soundness {cs} {vs} {ms₁} s₀ inv refl
      | True | vote ∷ [] | (block ∷ rest) ∷ []
      | True | True | True | True | True
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
          open State s₀ renaming (clock to slot)

          r : RoundNumber
          r = v-round slot

          tree : NodeModel
          tree = modelState s₀

          -- NewVote

          w' : Vote
          w' = createVote slot (creatorId vote) (proofM vote) (signature vote) (blockHash vote)

          w : Vote
          w = createVote slot sutId (proofM vote) (signature vote) (blockHash vote)

          votingRound≡rnd-slot : getRoundNumber (votingRound vote) ≡ rnd (getSlotNumber slot)
          votingRound≡rnd-slot = sym (eqℕ-sound isVotingRound)

          vote≡w' : vote ≡ w'
          vote≡w' = cong (λ {r → record vote { votingRound = MkRoundNumber r}}) votingRound≡rnd-slot

          creatorId≡sutId : creatorId vote ≡ sutId
          creatorId≡sutId = eqℕ-sound checkedSut

          w≡w' : w ≡ w'
          w≡w' = cong (λ {r → record w' { creatorId = r}}) (sym creatorId≡sutId)

          vote≡w : vote ≡ w
          vote≡w = trans vote≡w' (sym w≡w')

          validSignature : IsVoteSignature w (signature w)
          validSignature with v ← axiom-checkVoteSignature checkedSig
            rewrite vote≡w
            = v

          v : ValidVote w
          v = axiom-everyoneIsOnTheCommittee , validSignature

          startOfRound : StartOfRound slot r
          startOfRound = lem-divMod _ _ (eqℕ-sound isSlotZero)

          s' : State
          s' = record s₀
                 { blockTrees =
                     set otherId (addVote tree v)
                       (set sutId (addVote tree v)
                         blockTrees)
                 ; history = VoteMsg v ∷ history
                 }

          validVote : VotingRule slot tree
          validVote = toWitness (isYes≡True⇒TTrue checkedVRs)

          validBlockHash : BlockSelection slot tree ≡ blockHash vote
          validBlockHash =
            MkHash-inj $
              trans
                (cong hashBytes (blockSelection-eq {s₀}))
                (lem-eqBS isValidBlockHash)

          otherExists : set sutId (addVote tree v) blockTrees ⁉ otherId ≡ just tree
          otherExists =
            trans
              (k'≢k-get∘set {k = otherId} {k' = sutId} {v = addVote tree v} {m = blockTrees} sutId≢otherId)
              (otherTree inv)

          trace₁ : s₀ ↝⋆ s'
          trace₁ = CreateVote (invFetched inv)
                    (honest {p = sutId}
                      validBlockHash
                      (sutTree inv)
                      validSignature
                      startOfRound
                      axiom-everyoneIsOnTheCommittee
                      validVote
                    )
                ↣ Fetch {m = VoteMsg v}
                    (honest {p = sutId}
                      (sutTree inv)
                      (Any.here refl)
                      VoteReceived
                    )
                ↣ Fetch {m = VoteMsg v}
                    (honest {p = otherId}
                      otherExists
                      (Any.here refl)
                      VoteReceived
                    )
                ↣ ∎

          -- NewChain

          β : Block
          β = createBlock slot sutId (leadershipProof block) (signature block) (modelState s')

          creatorId≡sutId-block : creatorId block ≡ sutId
          creatorId≡sutId-block = eqℕ-sound checkedBlockSut

          slotNumber≡slot : slotNumber block ≡ slot
          slotNumber≡slot = cong MkSlotNumber (eqℕ-sound checkSlot)

          parent≡tip : parentBlock block ≡ tipHash rest
          parent≡tip = MkHash-inj block-parentBlock
            where
              block-parentBlock : hashBytes (parentBlock block) ≡ hashBytes (tipHash rest)
              block-parentBlock = eqBS-sound checkHash

          cert≡needCert : certificate block ≡ needCert (v-round slot) (modelState s')
          cert≡needCert = {!!} -- TODO: see ↑

          bodyHash≡txsHash :
            bodyHash block ≡
              let txs = txSelection slot (creatorId block)
                  open Hashable ⦃...⦄
              in blockHash
                 record
                   { blockHash = hash txs
                   ; payload = txs
                   }
          bodyHash≡txsHash = {!!} -- TODO: see ↑

          rest≡pref : rest ≡ prefChain (modelState s')
          rest≡pref = {!!} -- eqList-sound checkRest

          pref≡rest : prefChain (modelState s') ≡ rest
          pref≡rest = sym rest≡pref

          block≡β : block ≡ β
          block≡β
            with v ←
            cong
              (λ i →  record
                      { slotNumber = i
                      ; creatorId = creatorId block
                      ; parentBlock = parentBlock block
                      ; certificate = certificate block
                      ; leadershipProof = leadershipProof block
                      ; bodyHash = bodyHash block
                      ; signature = signature block
                      })
              slotNumber≡slot
            rewrite creatorId≡sutId-block
            rewrite parent≡tip
            rewrite cert≡needCert
            rewrite bodyHash≡txsHash
            rewrite pref≡rest
            = {!v!}

          validBlockSignature : IsBlockSignature β (signature β)
          validBlockSignature with v ← axiom-checkBlockSignature checkedBlockSig
            rewrite sym block≡β
            rewrite rest≡pref
            = v

          chain : ValidChain (β ∷ prefChain (modelState s'))
          chain
            = let open SmallStep.IsTreeType
              in Cons {prefChain (modelState s')} {β}
                validBlockSignature
                (axiom-checkLeadershipProof {β} checkedLead)
                refl
                (is-TreeType .valid (modelState s'))

          s'' : State
          s'' = record s'
                 { blockTrees =
                     set otherId (addChain (modelState s') chain) (
                       set sutId (addChain (modelState s') chain) (
                         State.blockTrees s'))
                 ; history = ChainMsg chain ∷ State.history s'
                 }

          s₁ : State
          s₁ = tick s''

          otherExists2 :
            set sutId (addChain (modelState s') chain)
              (set otherId (addVote tree v)
                (set sutId (addVote tree v) blockTrees))
                  ⁉ otherId
            ≡ just (modelState s')
          otherExists2 =
            trans
              (k'≢k-get∘set
                {k = otherId}
                {k' = sutId}
                {v = addChain (modelState s') chain}
                {m = set otherId (addVote tree v) (set sutId (addVote tree v) blockTrees)}
                sutId≢otherId)
              otherExists'
            where
              otherExists'' : addVote (modelState s₀) v ≡
                 let bt = set otherId (addVote tree v) (set sutId (addVote tree v) blockTrees)
                 in record
                      { clock        = State.clock s'
                      ; protocol     = testParams
                      ; allChains    = maybe′ chains [] (bt ⁉ sutId)
                      ; allVotes     = maybe′ votes  [] (bt ⁉ sutId)
                      ; allSeenCerts = maybe′ certs  [] (bt ⁉ sutId)
                      }
              otherExists''
                rewrite k'≢k-get∘set
                          {k = sutId}
                          {k' = otherId}
                          {v = addVote tree v}
                          {m = set sutId (addVote tree v) blockTrees}
                          otherId≢sutId
                rewrite get∘set≡id
                          {k = sutId}
                          {v = addVote tree v}
                          {m = blockTrees}
                = refl

              otherExists' :
                set otherId (addVote tree v) (set sutId (addVote tree v) blockTrees) ⁉ otherId
                  ≡ just (modelState s')
              otherExists' =
                trans
                  (k'≢k-get∘set∘set
                    {k = otherId}
                    {k' = sutId}
                    {v = addVote tree v}
                    {v' = addVote tree v}
                    {m = blockTrees}
                    sutId≢otherId)
                  (trans (get∘set≡id
                           {k = otherId}
                           {v = addVote tree v}
                           {m = blockTrees})
                             (cong just otherExists''))

          trace₂ : s' ↝⋆ s''
          trace₂ = CreateBlock (invFetched inv)
                    (honest {p = sutId}
                      (existsTrees (sutTree inv) trace₁)
                      chain
                    )
                ↣ Fetch {m = ChainMsg chain}
                    (honest {p = sutId}
                      {!!} -- otherExists2
                      (Any.here refl)
                      ChainReceived
                    )
                ↣ Fetch {m = ChainMsg chain}
                    (honest {p = otherId}
                      otherExists2
                      (Any.here refl)
                      ChainReceived
                    )
                ↣ ∎

          trace₃ : s'' ↝⋆ s₁
          trace₃ = NextSlot (invFetched inv) ↣ ∎

          trace : s₀ ↝⋆ s₁
          trace = trace₁ ++' trace₂ ++' trace₃

          tree⁺ : NodeModel
          tree⁺ = addChain (modelState s') chain

          set-irrelevant :
            let s = record s₀
                      { blockTrees =
                         set otherId (addChain (modelState s') chain) (
                           set sutId (addChain (modelState s') chain) (
                             State.blockTrees s')) }
            in
            record
              { clock        = MkSlotNumber (suc (getSlotNumber (State.clock s)))
              ; protocol     = testParams
              ; allChains    = maybe′ chains [] (State.blockTrees s ⁉ sutId)
              ; allVotes     = maybe′ votes  [] (State.blockTrees s ⁉ sutId)
              ; allSeenCerts = maybe′ certs  [] (State.blockTrees s ⁉ sutId)
              }
            ≡
            let s = record s₀
                      { blockTrees =
                          set sutId (addChain (modelState s') chain) (
                          set sutId (addVote tree v) blockTrees) }
            in
            record
              { clock        = MkSlotNumber (suc (getSlotNumber (State.clock s)))
              ; protocol     = testParams
              ; allChains    = maybe′ chains [] (State.blockTrees s ⁉ sutId)
              ; allVotes     = maybe′ votes  [] (State.blockTrees s ⁉ sutId)
              ; allSeenCerts = maybe′ certs  [] (State.blockTrees s ⁉ sutId)
              }
          set-irrelevant
            rewrite k'≢k-get∘set
              {k  = sutId}
              {k' = otherId}
              {v  = addChain (modelState s') chain}
              {m  = set sutId (addChain (modelState s') chain) (State.blockTrees s')}
              otherId≢sutId
            rewrite k'≢k-get∘set∘set
              {k = sutId}
              {k' = otherId}
              {v = addChain (modelState s') chain}
              {v' = addVote tree v}
              {m = set sutId (addVote tree v) blockTrees}
              otherId≢sutId
            = refl

          addVote-modelState :
            let s = record s₀
                      { blockTrees =
                          set sutId (addChain (modelState s') chain) (
                          set sutId (addVote tree v) blockTrees) }
            in
            record
              { clock        = MkSlotNumber (suc (getSlotNumber (State.clock s)))
              ; protocol     = testParams
              ; allChains    = maybe′ chains [] (State.blockTrees s ⁉ sutId)
              ; allVotes     = maybe′ votes  [] (State.blockTrees s ⁉ sutId)
              ; allSeenCerts = maybe′ certs  [] (State.blockTrees s ⁉ sutId)
              }
            ≡
            let s = record tree
                      { clock    = MkSlotNumber (suc (getSlotNumber slot))
                      ; allVotes = w ∷ maybe′ votes [] (blockTrees ⁉ sutId)
                      ; allChains = (β ∷ prefChain (modelState s')) ∷ maybe′ chains [] (blockTrees ⁉ sutId)
                      }
            in record s { allSeenCerts = foldr insertCert (allSeenCerts s) (certsFromQuorum s) }
          addVote-modelState
            rewrite get∘set≡id
              {k = sutId}
              {v = addChain (modelState s') chain}
              {m = set sutId (addVote tree v) blockTrees }
            rewrite get∘set≡id
              {k = sutId}
              {v = addVote (modelState s₀) v}
              {m = blockTrees}
            = {!refl!}

          substitute :
            let s = record tree
                      { clock    = MkSlotNumber (suc (getSlotNumber slot))
                      ; allVotes = w ∷ maybe′ votes [] (blockTrees ⁉ sutId)
                      ; allChains = (β ∷ prefChain (modelState s')) ∷ maybe′ chains [] (blockTrees ⁉ sutId)
                      }
            in record s { allSeenCerts = foldr insertCert (allSeenCerts s) (certsFromQuorum s) }
            ≡
            let s = record tree
                      { clock    = MkSlotNumber (suc (getSlotNumber slot))
                      ; allVotes = vote ∷ maybe′ votes [] (blockTrees ⁉ sutId)
                      ; allChains = (block ∷ rest) ∷ maybe′ chains [] (blockTrees ⁉ sutId)
                      }
            in record s { allSeenCerts = foldr insertCert (allSeenCerts s) (certsFromQuorum s) }
          substitute
            rewrite sym vote≡w
            rewrite sym block≡β
            rewrite sym rest≡pref
            rewrite votingRound≡rnd-slot
            = {!refl!}

          s₁-agrees :
            modelState s₁ ≡
            let s = record tree
                    { clock = MkSlotNumber (suc (getSlotNumber slot))
                    ; allVotes = vote ∷ maybe′ votes [] (blockTrees ⁉ sutId)
                    ; allChains = (block ∷ rest) ∷ maybe′ chains [] (blockTrees ⁉ sutId)
                    }
            in record s { allSeenCerts = foldr insertCert (allSeenCerts s) (certsFromQuorum s) }
          s₁-agrees = trans set-irrelevant (trans addVote-modelState substitute)

          votes-agree : sutVotesInTrace trace ≡ (slot , vote) ∷ map (slot ,_) []
          votes-agree = {!!} -- rewrite vote≡w = refl

          inv₁ : Invariant s₁
          inv₁ =
            record
              { invFetched =
                fetched {
                  record s₀
                    { blockTrees =
                        set otherId (addVote tree v)
                          (set sutId (addVote tree v)
                            blockTrees)
                    ; history = ChainMsg chain ∷ State.history s'
                    }
                  } (invFetched inv)
              ; sutTree = existsTrees {sutId} {s₀} {s₁} (sutTree inv) trace
              ; otherTree = existsTrees {otherId} {s₀} {s₁} (otherTree inv) trace
              }


    tick-soundness {cs} {vs} {ms₁} s₀ inv refl
      | True | vote ∷ [] | (block ∷ rest) ∷ []
      | _ | _ | _ | _ | _
      | _ | _ | _ | _ | _ | _ = {!!}


    tick-soundness s₀ inv refl
      | True | _ | _ = {!!} -- a vote is expected

    tick-soundness {cs} {vs} {ms₁} s₀ inv refl
      | False
      with cs

    tick-soundness {cs} {vs} {ms₁} s₀ inv refl
      | False
      | []
      rewrite isSlotZero
      =
        record
          { s₁ = s₁
          ; invariant₀ = inv
          ; invariant₁ = inv₁
          ; trace = trace
          ; s₁-agrees = {!s₁-agrees!} -- s₁-agrees
          ; votes-agree = votes-agree
          }

      where
        open State s₀ renaming (clock to slot)

        tree : NodeModel
        tree = modelState s₀

        s₁ : State
        s₁ = tick s₀

        invFetched₁ : Fetched s₁
        invFetched₁ = fetched {s₀} (invFetched inv)

        s₁-agrees :
          modelState s₁ ≡ ms₁
          {-
          modelState (tick s₀)
          ≡
          record
            { clock        = MkSlotNumber (suc (getSlotNumber slot))
            ; protocol     = testParams
            ; allChains    = maybe′ chains [] (State.blockTrees s₀ ⁉ sutId)
            ; allVotes     = maybe′ votes  [] (State.blockTrees s₀ ⁉ sutId)
            ; allSeenCerts = maybe′ certs  [] (State.blockTrees s₀ ⁉ sutId)
            } -}
        s₁-agrees
          rewrite noCertsFromQuorum {s₁} invFetched₁
          = {!!} -- refl

        trace : s₀ ↝⋆ s₁
        trace = NextSlot (invFetched inv) ↣ ∎

        votes-agree : sutVotesInTrace trace ≡ map (slot ,_) vs
        votes-agree = {!refl!} -- isSlotZero ≡ False → no vote

        inv₁ : Invariant s₁
        inv₁ =
          record
            { invFetched = invFetched₁
            ; sutTree = existsTrees {sutId} {s₀} {s₁} (sutTree inv) trace
            ; otherTree = existsTrees {otherId} {s₀} {s₁} (otherTree inv) trace
            }

    tick-soundness s₀ inv refl
      | False | _ = {!!}


    @0 badVote-soundness : ∀ {cs vs ms₁} s₀ vote
                          → Invariant s₀
                          → transition (modelState s₀) (BadVote vote) ≡ Just ((cs , vs) , ms₁)
                          → Soundness s₀ ms₁ (map (State.clock s₀ ,_) vs)
    badVote-soundness s₀ vote inv prf
      with hasVoted (voterId vote) (votingRound vote) (modelState s₀)
    badVote-soundness {cs} {vs} {ms₁} s₀ vote inv refl | True =
      record
        { s₁ = s₀
        ; invariant₀ = inv
        ; invariant₁ = inv
        ; trace = ∎
        ; s₁-agrees = refl
        ; votes-agree = refl
        }

    @0 soundness : ∀ {ms₁ cs vs} (s₀ : State) (a : EnvAction)
              → Invariant s₀
              → transition (modelState s₀) a ≡ Just ((cs , vs) , ms₁)
              → Soundness s₀ ms₁ (map (State.clock s₀ ,_) vs)

    soundness s₀ (NewVote vote) = newVote-soundness s₀ vote
    soundness s₀ (NewChain chain) = newChain-soundness s₀ chain
    soundness s₀ Tick = tick-soundness s₀
    soundness s₀ (BadVote vote) = badVote-soundness s₀ vote
