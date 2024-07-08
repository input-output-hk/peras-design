
module Peras.Conformance.Soundness where

open import Haskell.Prelude
open import Haskell.Prim.Tuple
open import Haskell.Law.Equality

open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (NonZero; ℕ; _≡ᵇ_)
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

open import Peras.Conformance.Model
open import Peras.Conformance.Params

-- TODO: ProofPrelude
eqℕ-sound : {n m : Nat} → (n == m) ≡ True → n ≡ m
eqℕ-sound {zero}  {zero}   _   = refl
eqℕ-sound {suc n} {suc m} prf = cong suc (eqℕ-sound prf)

module _ ⦃ _ : Hashable (List Tx) ⦄
         ⦃ params     : Params ⦄
         ⦃ network    : Network ⦄
         ⦃ postulates : Postulates ⦄

         {T : Set} {blockTree : SmallStep.TreeType T}
         {S : Set} {adversarialState₀ : S}
         {txSelection : SlotNumber → PartyId → List Tx}
         {parties : Parties} -- TODO: use parties from blockTrees
    where

  open SmallStep.Semantics {T} {blockTree} {S} {adversarialState₀} {txSelection} {parties}
  open SmallStep.TreeType blockTree renaming (allChains to chains)

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
      ; perasT = 0      -- TODO: Missing from Params
      ; perasΔ = Δ
      }
      where
        open Params params
        open Network network

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
    sutVotesInStep {s₀ = s₀} (CreateVote _ (honest {p} {t} {M} {π} {σ} _ _ _ _ _)) =
      case p ≟ sutId of λ where
        (yes _) → (State.clock s₀ , createVote (State.clock M) p π σ t) ∷ []
        (no _)  → []
    sutVotesInStep (CreateBlock _ _) = []
    sutVotesInStep (NextSlot _ _) = []
    sutVotesInStep (NextSlotNewRound _ _ _) = []

    sutVotesInTrace : ∀ {s₀ s₁} → s₀ ↝⋆ s₁ → List (SlotNumber × Vote)
    sutVotesInTrace ∎              = []
    sutVotesInTrace (step ↣ trace) = sutVotesInStep step ++ sutVotesInTrace trace

    -- Preconditions ---
    private
      mod : ℕ → (n : ℕ) → @0 ⦃ NonZero n ⦄ → ℕ
      mod a b ⦃ prf ⦄ = _%_ a b ⦃ uneraseNonZero prf ⦄

      div : ℕ → (n : ℕ) → @0 ⦃ NonZero n ⦄ → ℕ
      div a b ⦃ prf ⦄ = _/_ a b ⦃ uneraseNonZero prf ⦄

    record NewVotePreconditions (s : State) (vote : Vote) : Set where
      slot = State.clock s
      r    = v-round slot
      σ    = signature vote
      field
        {tree}         : T
        creatorExists  : State.blockTrees s ⁉ (creatorId vote) ≡ just tree
        startOfRound   : StartOfRound slot r
        validSignature : IsVoteSignature vote σ
        correctVote    : vote ≡ createVote slot (creatorId vote) (proofM vote) σ tree
        validVote      : (VotingRule-1A r tree) ⊎ (VotingRule-2A r tree P.× VotingRule-2B r tree) -- FIXME: all voting rules

      validSignature' : IsVoteSignature (createVote slot (creatorId vote) (proofM vote) σ tree) σ
      validSignature' with valid ← validSignature rewrite correctVote = valid

    lem-divMod : ∀ a b ⦃ _ : NonZero b ⦄ → mod a b ≡ 0 → a ≡ div a b * b
    lem-divMod a b eq with lem ← m≡m%n+[m/n]*n a b rewrite eq = lem

    suc-definition : ∀ {n} → suc n ≡ n + 1
    suc-definition {zero} = refl
    suc-definition {suc n} = cong suc (suc-definition {n})

    open import Data.Nat using (_≥_; _≥?_; _>?_)

{-
    postulate
      hash-genesis : (hashBytes (Hashable.hash hashBlock (Network.block₀ network))) ≡ emptyBS
      sign-genesis : (bytesS (signature (Network.block₀ network))) ≡ emptyBS
-}

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
      → let
          m = modelState s p
          block = case (votingBlock m) of
                   λ { (Just block) → block
                     ; Nothing → Network.block₀ network
                     }
          cert' = maximumBy cert₀ (comparing round) (allSeenCerts m)
        in
          extends block cert' (allChains m) ≡ True
      → VotingRule-1B (proj₁ ∃tree)
    vr-1b⇒VotingRule-1B = {!!}

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
      rewrite (proj₂ ∃tree)
      rewrite suc-definition {n = getRoundNumber (round (latestCert cert₀ (allSeenCerts (modelState s p))))}
      = {!!} P., {!!}

    record Invariant (s : State) : Set where
      field
        invFetched : Fetched s
        hasTree : ∀ (p : ℕ) → ∃[ t ] (State.blockTrees s ⁉ p ≡ just t)

    open Invariant

    @0 newVote-preconditions : ∀ {vs ms₁} s vote
                          → Invariant s
                          → transition (modelState s (creatorId vote)) (NewVote vote) ≡ Just (vs , ms₁)
                          → NewVotePreconditions s vote
    newVote-preconditions s vote inv prf
      with mod (getSlotNumber (State.clock s)) (Params.U params) == 0 in isSlotZero
         | checkSignedVote vote in checkedSig
         | isYes (checkVotingRules (modelState s (creatorId vote))) in checkedVRs
    newVote-preconditions s vote inv refl | True | True | True =
      record
      { tree            = proj₁ (hasTree inv (creatorId vote)) -- we don't track the block trees for the environment nodes in the test model!
      ; creatorExists   = proj₂ (hasTree inv (creatorId vote)) -- maybe invariant that everyone has the same blockTree?
      ; startOfRound    = lem-divMod _ _ (eqℕ-sound isSlotZero)
      ; validSignature  = axiom-checkVoteSignature checkedSig
      ; correctVote     = {!!}    -- this needs to go in the `transition` (checking preferred chains and L etc)
      ; validVote       =
        let
          witness = toWitness' (isYes≡True⇒TTrue checkedVRs )
          f₁ = vr-1a⇒VotingRule-1A  s (creatorId vote) (hasTree inv (creatorId vote))
          f₂ = vr-1b⇒VotingRule-1B  s (creatorId vote) (hasTree inv (creatorId vote))
          f₃ = vr-2a⇒VotingRule-2A  s (creatorId vote) (hasTree inv (creatorId vote))
          f₄ = vr-2b⇒VotingRule-2B  s (creatorId vote) (hasTree inv (creatorId vote))
        in
          S.map (proj₁ ∘ P.map₁ f₁) (P.map f₃ f₄) witness -- need to check the VR logic also for environment votes
      }

    -- Soundness --
    record Soundness (s₀ : State) (ms₁ : NodeModel) (vs : List (SlotNumber × Vote)) : Set where
      field
        s₁          : State
        invariant₀  : Invariant s₀
        invariant₁  : Invariant s₁
        trace       : s₀ ↝⋆ s₁
        s₁-agrees   : modelState s₁ sutId ≡ ms₁
        votes-agree : sutVotesInTrace trace ≡ vs -- prefix

    @0 soundness : ∀ {ms₁ vs} (s₀ : State) (a : EnvAction)
              → Invariant s₀
              → transition (modelState s₀ sutId) a ≡ Just (vs , ms₁)
              → Soundness s₀ ms₁ (map (State.clock s₀ ,_) vs)
    soundness s₀ Tick inv prf = {!!}
    soundness s₀ (NewChain x) inv prf = {!!}
    soundness s₀ (NewVote vote) inv prf
      with sutId ≟ creatorId vote
    ... | yes x rewrite x =
      let pre = newVote-preconditions s₀ vote inv prf
          open NewVotePreconditions pre
          open SmallStep.Message
      in
        record
          { s₁          = let v = createVote slot (creatorId vote) (proofM vote) σ tree
                          in VoteMsg v , fzero , creatorId v , addVote tree v ⇑ s₀
          ; invariant₀  = inv
          ; invariant₁  = {!!}
          ; trace       = CreateVote (invFetched inv)
                            (honest {σ = Vote.signature vote}
                              creatorExists
                              validSignature'
                              startOfRound
                              axiom-everyoneIsOnTheCommittee
                              {!!} -- FIXME: validVote
                            )
                          -- TODO: also deliver the vote message to establish Fetched s₁
                          ↣ ∎
          ; s₁-agrees   = {!!}
          ; votes-agree = {!!}
          }
    ... | no x = {!!}
