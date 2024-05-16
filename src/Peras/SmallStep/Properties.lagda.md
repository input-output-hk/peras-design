```agda
module Peras.SmallStep.Properties where
```

<!--
```agda
open import Data.Bool as Bool using (Bool; true; false)
open import Data.List as List using (List; []; _∷_; null; map; _++_; foldr; filter)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ʳ; ∈-++⁺ˡ; ∈-resp-≋)

open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Relation.Unary.Any as Any using (Any; _─_; _∷=_; here; there)
open import Data.List.Relation.Unary.Any.Properties as Any using (¬Any[])
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.All.Properties as All using (¬All⇒Any¬; All¬⇒¬Any; ─⁺; ─⁻)

open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (zero; suc; _≟_)
open import Data.Fin.Properties using (0≢1+n)
open import Data.Nat as ℕ using (ℕ; _∸_; _<_; _≤_; _≥_; _*_; _+_; pred)
open import Data.Nat.Properties using (n≤1+n; 1+n≰n; ≤-refl; ≤-reflexive; ≤-trans)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂; curry; uncurry)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Function.Base using (_∘_; id; _$_; flip)

open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (¬?)
open import Relation.Nullary.Negation using (contradiction)

open import Peras.Block
open import Peras.Chain
open import Peras.Crypto
open import Peras.Params using (Params)
open import Peras.SmallStep
open TreeType

open import Data.List.Membership.DecPropositional _≟-Block_ using (_∈?_)
open import Data.List.Relation.Binary.Subset.Propositional {A = Block} using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional {A = Envelope} renaming (_⊆_ to _⊆ᵐ_)

open import Data.List.Relation.Binary.Equality.Propositional using (_≋_; ≡⇒≋; ≋⇒≡)

open import Data.Tree.AVL.Map PartyIdO as M using (Map; lookup; insert; empty; fromList)

open import Data.Tree.AVL.Map.Membership.Propositional PartyIdO
open import Data.Tree.AVL.Map.Membership.Propositional.Properties PartyIdO

open import Relation.Unary using (Pred)
open import Level using (Level)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; subst; trans)
```
-->

```agda
module _ {block₀ : Block} {cert₀ : Certificate}
         (IsCommitteeMember : PartyId → RoundNumber → MembershipProof → Set)
         (IsVoteSignature : Vote → Signature → Set)
         (IsSlotLeader : PartyId → Slot → LeadershipProof → Set)
         (IsBlockSignature : Block → Signature → Set)
         ⦃ _ : Hashable Block ⦄
         ⦃ _ : Hashable (List Tx) ⦄
         ⦃ _ : Params ⦄
         where

  open Hashable ⦃...⦄
  open Params ⦃...⦄

  module _ {A : Set}
           (blockTree : TreeType A)
           {AdversarialState : Set}
           (adversarialState₀ : AdversarialState)
           (txSelection : Slot → PartyId → List Tx)
           (parties : Parties)
           where
```
### Initial state
```agda
    LocalState′ = Stateˡ {block₀} {cert₀} {IsCommitteeMember} {IsVoteSignature} {IsSlotLeader} {IsBlockSignature} {A} {blockTree} {AdversarialState} {adversarialState₀} {txSelection} {parties}
    GlobalState = Stateᵍ {block₀} {cert₀} {IsCommitteeMember} {IsVoteSignature} {IsSlotLeader} {IsBlockSignature} {A} {blockTree} {AdversarialState} {adversarialState₀} {txSelection} {parties}

    state₀ : LocalState′
    state₀ = ⟪ tree₀ blockTree ⟫

    states₀ : Map LocalState′
    states₀ = foldr (λ where (p , _) m → insert p state₀ m ) empty parties

    N₀ : GlobalState
    N₀ = ⟦ 0
         , states₀
         , []
         , []
         , adversarialState₀
         ⟧
```
<!--
```agda
    open Stateᵍ
    open Honesty
    open _↝_
    open IsTreeType
    open Envelope
```
-->
<!--
```agda
    clock-incr : ∀ {M N : GlobalState}
      → M ↝ N
      → clock M ≤ clock N
    clock-incr {⟦ c , _ , _ , _ , _ ⟧} {⟦ c , _ , _ , _ , _ ⟧} (Deliver (honest _ _ _)) = ≤-refl
    clock-incr {⟦ c , _ , _ , _ , _ ⟧} {⟦ c , _ , _ , _ , _ ⟧} (Deliver (corrupt _)) = ≤-refl
    clock-incr {⟦ c , _ , _ , _ , _ ⟧} {⟦ c , _ , _ , _ , _ ⟧} (CastVote (honest _ _ _ _ _ _)) = ≤-refl
    clock-incr {⟦ c , _ , _ , _ , _ ⟧} {⟦ c , _ , _ , _ , _ ⟧} (CreateBlock (honest _ _ _ _)) = ≤-refl
    clock-incr {⟦ c , _ , _ , _ , _ ⟧} {⟦ c , _ , _ , _ , _ ⟧} (CreateBlock (honest-cooldown _ _ _ _ _ _ _)) = ≤-refl
    clock-incr {M} (NextSlot _) = n≤1+n (clock M)

    clock-incr⋆ : ∀ {M N : GlobalState}
      → M ↝⋆ N
      → clock M ≤ clock N
    clock-incr⋆ []′ = ≤-refl
    clock-incr⋆ ( x ∷′ x₁) = ≤-trans (clock-incr x) (clock-incr⋆ x₁)
```
-->
### Knowledge propagation
<!--
```agda
    All-∷= : {a p : Level} {A : Set a} {P : Pred A p} {x y : A} {xs : List A}
      → All P xs
      → (x∈xs : x ∈ xs)
      → P y
      → All P (x∈xs ∷= y)
    All-∷= (_ All.∷ x₁) (here refl) x₂ = x₂ All.∷ x₁
    All-∷= (px All.∷ x₁) (there x∈xs) x₂ = px All.∷ (All-∷= x₁ x∈xs x₂)
```
-->
<!--
```agda
{-
    data Any↝ (P : ∀ {A B : GlobalState} → (A ↝ B) → Set) : ∀ {M N : GlobalState} → (M ↝⋆ N) → Set where
      here  : ∀ {A B N : GlobalState} {x xs} (px : P {A} {B} x) → Any↝ P {A} {N} (_ ↝⟨ x ⟩ xs)
      there : ∀ {M N : GlobalState} {x xs} (pxs : Any↝ P {M} {N} xs) → Any↝ P {M} {N} (_ ↝⟨ x ⟩ xs)

    HasStep : ∀ {A B M N : GlobalState} → (A ↝ B) → (M ↝⋆ N) → Set
    HasStep {A} {B} {M} {N} x xs = Any↝ (λ { y → y ≡ x }) xs

    HasCreateStep : ∀ {M N : GlobalState} → Block → (M ↝⋆ N) → Set
    HasCreateStep b xs =
      let h = honest {block = b} refl {!!} {!!} {!!} {!!}
      in HasStep (CreateBlock {!h!}) xs

    knowledge-propagation1 : ∀ {N : GlobalState}
        → {p₁ p : PartyId}
        → {t₁ t : A}
        → {h₁ : Honesty p₁}
        → {b : Block}
        → (p₁ , h₁) ∈ parties
        → (s : N₀ ↝⋆ N)
        → Delivered N
        → lookup (stateMap N) p₁ ≡ just ⟪ t₁ ⟫
        → b ∈ allBlocks blockTree t₁
        → HasCreateStep b s
    knowledge-propagation1 x s d x₂ b∈bt = {!!}
-}
```
-->
```agda
    postulate
      knowledge-propagation₁ : ∀ {N : GlobalState}
        → {p₁ p : PartyId}
        → {t₁ t : A}
        → {h₁ : Honesty p₁}
        → {b : Block}
        → (p₁ , h₁) ∈ parties
        → (s : N₀ ↝⋆ N)
        → Delivered N
        → lookup (stateMap N) p₁ ≡ just ⟪ t₁ ⟫
        → b ∈ allBlocks blockTree t₁
        → Σ[ (M , M′) ∈ GlobalState × GlobalState ] (
             Σ[ (s₀ , s₁ , s₂) ∈ (N₀ ↝⋆ M) × (M ↝ M′) × (M′ ↝⋆ N) ] (
               s ≡ ↝⋆∘↝⋆ s₀ (s₁ ∷′ s₂) × ⦅ p , Honest , BlockMsg b , zero ⦆ ∈ messages M′))
```
<!--
```agda
    x∈x∷xs : ∀ {x : Block} {xs : List Block}
      → x ∈ x ∷ xs
    x∈x∷xs {x} {xs} = here refl

    postulate
      blocksNotLost : ∀ {M N : GlobalState} {p} {tₘ tₙ} {b}
        → M ↝⋆ N
        → lookup (Stateᵍ.stateMap M) p ≡ just ⟪ tₘ ⟫
        → lookup (Stateᵍ.stateMap N) p ≡ just ⟪ tₙ ⟫
        → b ∈ allBlocks blockTree tₘ
        → b ∈ allBlocks blockTree tₙ
{-
    blocksNotLost (_ ∎) x₁ x₂ x₃ = {!!}
    blocksNotLost (_ ↝⟨ Deliver x ⟩ x₄) x₁ x₂ x₃ = {!!}
    blocksNotLost (_ ↝⟨ CastVote x ⟩ x₄) x₁ x₂ x₃ = {!!}
    blocksNotLost (_ ↝⟨ CreateBlock x ⟩ x₄) x₁ x₂ x₃ = {!!}
    blocksNotLost (_ ↝⟨ NextSlot x ⟩ x₄) x₁ x₂ x₃ = {!!}
-}
    postulate
      e∈m′∈ms∷=m′ : ∀ {e : Envelope} {m : Message} {p} {ms}
        → e ∈ ms
        → (m′∈ms : ⦅ p , Corrupt , m , zero ⦆ ∈ ms )
        → e ∈ (m′∈ms ∷= (⦅ p , Corrupt , m , suc zero ⦆))

      m′∈ms─m∈ms : ∀ {m m′ : Envelope} {ms}
        → (m∈ms : m ∈ ms)
        → m′ ∈ ms
        → m ≢ m′
        → m′ ∈ (ms ─ m∈ms)

{-
    m′∈ms─m∈ms {m} {m′} {.(_ ∷ _)} m∈ms (here refl) x = {!!}
    m′∈ms─m∈ms {m} {m′} {.(x ∷ xs)} (here px) (there {x} {xs} y) a = {!!}
    m′∈ms─m∈ms {m} {m′} {.(x ∷ xs)} (there z) (there {x} {xs} y) a = m′∈ms─m∈ms z y a
-}

{-
    CertMsg≢BlockMsg : ∀ {p q c b} → ⦅ p , Honest , CertMsg c , zero ⦆ ≢ ⦅ q , Honest , BlockMsg b , zero ⦆
    CertMsg≢BlockMsg x with cong message x
    ... | ()
-}

    VoteMsg≢BlockMsg : ∀ {p q v b} → ⦅ p , Honest , VoteMsg v , zero ⦆ ≢ ⦅ q , Honest , BlockMsg b , zero ⦆
    VoteMsg≢BlockMsg x with cong message x
    ... | ()

    ⊆-vote : ∀ {M N : GlobalState} {p} {h : Honesty p}
      → h ⊢ M ⇉ N
      → messages M ⊆ᵐ messages N
    ⊆-vote {p = p} (honest {vote = v} refl _ _ _ _ _) = ∈-++⁺ʳ $ map (uncurry ⦅_,_, VoteMsg v , zero ⦆) (filter (¬? ∘ (p ℕ.≟_) ∘ proj₁) parties)

    ⊆-block : ∀ {M N : GlobalState} {p} {h : Honesty p}
      → h ⊢ M ↷ N
      → messages M ⊆ᵐ messages N
    ⊆-block {p = p} (honest {block = b} refl _ _ _) = ∈-++⁺ʳ $ map (uncurry ⦅_,_, BlockMsg b , zero ⦆)  (filter (¬? ∘ (p ℕ.≟_) ∘ proj₁) parties)
    ⊆-block {p = p} (honest-cooldown {block = b} refl _ _ _ _ _ _) = ∈-++⁺ʳ $ map (uncurry ⦅_,_, BlockMsg b , zero ⦆) (filter (¬? ∘ (p ℕ.≟_) ∘ proj₁) parties)
```
-->
```agda
    knowledge-propagation₂ : ∀ {M N : GlobalState}
        → {p : PartyId}
        → {t : A}
        → {h : Honesty p}
        → {b : Block}
        → (p , h) ∈ parties
        → N₀ ↝⋆ M
        → M ↝⋆ N
        → ⦅ p , Honest , BlockMsg b , zero ⦆ ∈ messages M
        → lookup (stateMap N) p ≡ just ⟪ t ⟫
        → Delivered N
        → b ∈ allBlocks blockTree t
```
```agda
    knowledge-propagation₂ {M} {p = p} {b = b} p∈ps N₀↝⋆M []′ m∈ms N×p≡t Delivered-M =
      contradiction (Any.map (sym ∘ cong delay) m∈ms) (All¬⇒¬Any Delivered-M)
```
```agda
    knowledge-propagation₂ {M} {N} {p} p∈ps N₀↝⋆M (M↝M′@(Deliver (honest x m′∈ms VoteReceived)) ∷′ M′↝⋆N) m∈ms N×p≡t Delivered-N =
      knowledge-propagation₂ p∈ps (↝∘↝⋆ N₀↝⋆M M↝M′) M′↝⋆N (m′∈ms─m∈ms m′∈ms m∈ms VoteMsg≢BlockMsg) N×p≡t Delivered-N
```
```agda
    knowledge-propagation₂ {M} {N} {p} {t} {h} {b} p∈ps N₀↝⋆M (M↝M′@(Deliver (honest {p′} {lₚ} {lₚ′} x m′∈ms (BlockReceived {b′} {t₁}))) ∷′ M′↝⋆N)
      m∈ms N×p≡t Delivered-N
      with p ℕ.≟ p′
    ... | no p≢p′ =
      let m≢m′ = ⦅⦆-injective′ (p≢p′ ∘ sym)
      in knowledge-propagation₂ p∈ps (↝∘↝⋆ N₀↝⋆M M↝M′) M′↝⋆N (m′∈ms─m∈ms m′∈ms m∈ms m≢m′) N×p≡t Delivered-N
    ... | yes p≡p′ with b′ ≟-Block b
    ... | yes b′≡b =
      let lookup-insert≡id = ∈ₖᵥ-lookup⁺ (∈ₖᵥ-insert⁺⁺ {p′} {m = stateMap M})
          lookup-p≡lookup-p′ = cong (lookup (insert p′ lₚ′ (stateMap M))) p≡p′
          bt≡bt′ = cong (allBlocks blockTree) (cong (extendTree blockTree t₁) (sym b′≡b))
          b∈bt = ∈-resp-≋ (≡⇒≋ bt≡bt′) (
            (proj₂ $ extendable (is-TreeType blockTree) t₁ b)
            (x∈x∷xs {b} {allBlocks blockTree t₁}))
      in blocksNotLost {tₘ = LocalState.tree lₚ′} M′↝⋆N (trans lookup-p≡lookup-p′ lookup-insert≡id) N×p≡t b∈bt
    ... | no b′≢b =
      let m≢m′ = ⦅⦆-injective₃′ (Message-injective′ b′≢b)
      in knowledge-propagation₂ p∈ps (↝∘↝⋆ N₀↝⋆M M↝M′) M′↝⋆N (m′∈ms─m∈ms m′∈ms m∈ms m≢m′) N×p≡t Delivered-N
```
```agda
    knowledge-propagation₂ {M} {N} {p} {t} {b} p∈ps N₀↝⋆M (M↝M′@(Deliver (corrupt {p₁} m′∈ms)) ∷′ M′↝⋆N) m∈ms N×p≡t Delivered-N =
      knowledge-propagation₂ p∈ps (↝∘↝⋆ N₀↝⋆M M↝M′) M′↝⋆N (e∈m′∈ms∷=m′ m∈ms m′∈ms) N×p≡t Delivered-N
```
```agda
    knowledge-propagation₂ p∈ps N₀↝⋆M (M↝M′@(CastVote x₂) ∷′ M′↝⋆N) m∈ms N×p≡t Delivered-N =
      knowledge-propagation₂ p∈ps (↝∘↝⋆ N₀↝⋆M M↝M′) M′↝⋆N (⊆-vote x₂ m∈ms) N×p≡t Delivered-N
```
```agda
    knowledge-propagation₂ p∈ps N₀↝⋆M (M↝M′@(CreateBlock x₂) ∷′ M′↝⋆N) m∈ms N×p≡t Delivered-N =
      knowledge-propagation₂ p∈ps (↝∘↝⋆ N₀↝⋆M M↝M′) M′↝⋆N (⊆-block x₂ m∈ms) N×p≡t Delivered-N
```
```agda
    knowledge-propagation₂ p∈ps N₀↝⋆M (M↝M′@(NextSlot Delivered-M) ∷′ M′↝⋆N) m∈ms N×p≡t Delivered-N =
      contradiction (Any.map (sym ∘ cong delay) m∈ms) (All¬⇒¬Any Delivered-M)
```
```agda
    knowledge-propagation₀ : ∀ {N : GlobalState}
        → {p₁ p₂ : PartyId}
        → {t₁ t₂ : A}
        → {honest₁ : Honesty p₁}
        → {honest₂ : Honesty p₂}
        → (p₁ , honest₁) ∈ parties
        → (p₂ , honest₂) ∈ parties
        → N₀ ↝⋆ N
        → lookup (stateMap N) p₁ ≡ just ⟪ t₁ ⟫
        → lookup (stateMap N) p₂ ≡ just ⟪ t₂ ⟫
        → Delivered N
        → allBlocks blockTree t₁ ⊆ allBlocks blockTree t₂
    knowledge-propagation₀ {N} {p₁} {p₂} {t₁} {t₂} p₁∈ps p₂∈ps x₂ x₃ x₄ Delivered-N x₆
      with knowledge-propagation₁ {N} {p₁} {p₂} {t₁} {t₂} p₁∈ps x₂ Delivered-N x₃ x₆
    ... | (M , M′) , (fst , fst₁ , snd) , refl , here refl = knowledge-propagation₂ p₂∈ps (↝∘↝⋆ fst fst₁) snd (here refl) x₄ Delivered-N
    ... | (M , M′) , (fst , fst₁ , snd) , refl , there s = knowledge-propagation₂ p₂∈ps (↝∘↝⋆ fst fst₁) snd (there s) x₄ Delivered-N
```

The lemma describes how knowledge is propagated between honest parties in the system.

```agda
    knowledge-propagation : ∀ {N₁ N₂ : GlobalState}
      → {p₁ p₂ : PartyId}
      → {t₁ t₂ : A}
      → {honesty₁ : Honesty p₁}
      → {honesty₂ : Honesty p₂}
      → honesty₁ ≡ Honest {p₁}
      → honesty₂ ≡ Honest {p₂}
      → (p₁ , honesty₁) ∈ parties
      → (p₂ , honesty₂) ∈ parties
      → N₀ ↝⋆ N₁
      → N₁ ↝⋆ N₂
      → lookup (stateMap N₁) p₁ ≡ just ⟪ t₁ ⟫
      → lookup (stateMap N₂) p₂ ≡ just ⟪ t₂ ⟫
      → Delivered N₂
      → clock N₁ ≡ clock N₂
      → allBlocks blockTree t₁ ⊆ allBlocks blockTree t₂
```
#### base case
```agda
    knowledge-propagation {N₁} _ _ p₁∈ps p₂∈ps N₀↝⋆N₁ []′ N₁×p₁≡t₁ N₂×p₂≡t₂ Delivered-N₂ _ = knowledge-propagation₀ p₁∈ps p₂∈ps N₀↝⋆N₁ N₁×p₁≡t₁ N₂×p₂≡t₂ Delivered-N₂
```
#### Deliver
```agda
    knowledge-propagation {N₁} {N₂} {p₁} {p₂} {t₁} {t₂}
      h₁ h₂ p₁∈ps p₂∈ps N₀↝⋆N₁ (N₁↝N′@(Deliver (honest {p} {lₚ} {.(⟪ extendTree blockTree _ _ ⟫)} {.(BlockMsg _)} lookup≡just-lₚ m∈ms (BlockReceived {b} {t}))) ∷′ N′↝⋆N₂)
      N₁×p₁≡t₁ N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
      with p₁ ℕ.≟ p
```
adds a block/vote/cert to p₁'s blocktree
proof: p₂ either already has the block in the local blocktree or it is in the message buffer with delay 0 (honest create in prev slot)
```agda
    ... | yes p₁≡p =
      let lookup-insert≡id = ∈ₖᵥ-lookup⁺ (∈ₖᵥ-insert⁺⁺ {p} {x = ⟪ extendTree blockTree t b ⟫} {m = stateMap N₁})
          lookup-p₁≡lookup-p = cong (lookup (insert p ⟪ extendTree blockTree t b ⟫ (stateMap N₁))) p₁≡p
          t≡t₁ = sym $ ⟪⟫-injective $ just-injective $ trans (sym N₁×p₁≡t₁) (trans (cong (lookup (stateMap N₁)) p₁≡p) lookup≡just-lₚ)
          N′×p₁≡t′ = trans (trans lookup-p₁≡lookup-p lookup-insert≡id) (cong just $ cong ⟪_⟫ $ cong (flip (extendTree blockTree) b) t≡t₁)
          H₀ = knowledge-propagation {p₁ = p₁} {t₁ = extendTree blockTree t₁ b} h₁ h₂ p₁∈ps p₂∈ps (↝∘↝⋆ N₀↝⋆N₁ N₁↝N′) N′↝⋆N₂ N′×p₁≡t′ N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
          ⊆-ext = proj₂ $ extendable (is-TreeType blockTree) t₁ b
      in ⊆-trans
           (xs⊆x∷xs (allBlocks blockTree t₁) b)
           (⊆-trans ⊆-ext H₀)
```
adds a block/vote/cert to some p's blocktree
```agda
    ... | no p₁≢p =
      let r = ∈ₖᵥ-lookup⁺ (∈ₖᵥ-insert⁺ p₁≢p (∈ₖᵥ-lookup⁻ {m = stateMap N₁} N₁×p₁≡t₁))
      in knowledge-propagation {p₁ = p₁} h₁ h₂ p₁∈ps p₂∈ps (↝∘↝⋆ N₀↝⋆N₁ N₁↝N′) N′↝⋆N₂ r N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
```
```agda
    knowledge-propagation {N₁} {N₂} {p₁} {p₂} {t₁} {t₂}
      h₁ h₂ p₁∈ps p₂∈ps N₀↝⋆N₁ (N₁↝N′@(Deliver (honest {p} {⟪ t ⟫} {.(⟪ addVote blockTree _ _ ⟫)} {.(VoteMsg _)} lookup≡just-lₚ m∈ms (VoteReceived {v}))) ∷′ N′↝⋆N₂)
      N₁×p₁≡t₁ N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
      with p₁ ℕ.≟ p
    ... | no p₁≢p =
      let r = ∈ₖᵥ-lookup⁺ (∈ₖᵥ-insert⁺ p₁≢p (∈ₖᵥ-lookup⁻ {m = stateMap N₁} N₁×p₁≡t₁))
      in knowledge-propagation {p₁ = p₁} h₁ h₂ p₁∈ps p₂∈ps (↝∘↝⋆ N₀↝⋆N₁ N₁↝N′) N′↝⋆N₂ r N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
    ... | yes p₁≡p =
      let lookup-insert≡id = ∈ₖᵥ-lookup⁺ (∈ₖᵥ-insert⁺⁺ {p} {x = ⟪ addVote blockTree t v ⟫} {m = stateMap N₁})
          lookup-p₁≡lookup-p = cong (lookup (insert p ⟪ addVote blockTree t v ⟫ (stateMap N₁))) p₁≡p
          t≡t₁ = sym $ ⟪⟫-injective $ just-injective $ trans (sym N₁×p₁≡t₁) (trans (cong (lookup (stateMap N₁)) p₁≡p) lookup≡just-lₚ)
          N′×p₁≡t′ = trans (trans lookup-p₁≡lookup-p lookup-insert≡id) (cong just $ cong ⟪_⟫ $ cong (flip (addVote blockTree) v) t≡t₁)
          H₀ = knowledge-propagation {t₁ = addVote blockTree t₁ v} h₁ h₂ p₁∈ps p₂∈ps (↝∘↝⋆ N₀↝⋆N₁ N₁↝N′) N′↝⋆N₂ N′×p₁≡t′ N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
          ⊆-ext = proj₂ $ extendable-votes (is-TreeType blockTree) t₁ v
      in ⊆-trans ⊆-ext H₀
```
Adversarial behaviour: potentially adds a block to p₂'s blocktree in the next slot
```agda
    knowledge-propagation {N₁} {N₂} {p₁} {p₂} {t₁} {t₂} {honesty₁} {honesty₂} h₁ h₂ p₁∈ps p₂∈ps N₀↝⋆N₁ (N₁↝N′@(Deliver {p} {h} (corrupt {p} m∈ms)) ∷′ N′↝⋆N₂)
      N₁×p₁≡t₁ N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
      with p₁ ℕ.≟ p
    ... | no p₁≢p = knowledge-propagation h₁ h₂ p₁∈ps p₂∈ps (↝∘↝⋆ N₀↝⋆N₁ N₁↝N′) N′↝⋆N₂ N₁×p₁≡t₁ N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
    ... | yes p₁≡p = contradiction p₁≡p (Honest≢Corrupt {p₁} {p} {honesty₁} {h} h₁ refl)
```
#### CastVote
CastVote is not relevant for allBlocks
```agda
    knowledge-propagation {N₁} {N₂} {p₁} {p₂} {t₁} {t₂} h₁ h₂ p₁∈ps p₂∈ps N₀↝⋆N₁ (N₁↝N′@(CastVote (honest {p} {t} {vote = v} refl lookup≡just-lₚ _ _ _ _)) ∷′ N′↝⋆N₂)
      N₁×p₁≡t₁ N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
      with p₁ ℕ.≟ p
    ... | no p₁≢p =
      let r = ∈ₖᵥ-lookup⁺ (∈ₖᵥ-insert⁺ p₁≢p (∈ₖᵥ-lookup⁻ {m = stateMap N₁} N₁×p₁≡t₁))
      in knowledge-propagation h₁ h₂ p₁∈ps p₂∈ps (↝∘↝⋆ N₀↝⋆N₁ N₁↝N′) N′↝⋆N₂ r N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
    ... | yes p₁≡p =
      let lookup-insert≡id = ∈ₖᵥ-lookup⁺ (∈ₖᵥ-insert⁺⁺ {p} {x = ⟪ addVote blockTree t v ⟫} {m = stateMap N₁})
          lookup-p₁≡lookup-p = cong (lookup (insert p ⟪ addVote blockTree t v ⟫ (stateMap N₁))) p₁≡p
          t≡t₁ = sym $ ⟪⟫-injective $ just-injective $ trans (sym N₁×p₁≡t₁) (trans (cong (lookup (stateMap N₁)) p₁≡p) lookup≡just-lₚ)
          N′×p₁≡t′ = trans (trans lookup-p₁≡lookup-p lookup-insert≡id) (cong just $ cong ⟪_⟫ $ cong (flip (addVote blockTree) v) t≡t₁)
          H₀ = knowledge-propagation {t₁ = addVote blockTree t₁ v} h₁ h₂ p₁∈ps p₂∈ps (↝∘↝⋆ N₀↝⋆N₁ N₁↝N′) N′↝⋆N₂ N′×p₁≡t′ N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
          ⊆-ext = proj₂ $ extendable-votes (is-TreeType blockTree) t₁ v
      in ⊆-trans ⊆-ext H₀
```
#### CreateBlock
When creating a block, there will be messages for all parties to be consumed in order to get to `Delivered` again. Consuming
those messages adds the blocks into the local trees.
```agda
    knowledge-propagation {N₁} {N₂} {p₁} {p₂} {t₁} {t₂} h₁ h₂ p₁∈ps p₂∈ps N₀↝⋆N₁ (N₁↝N′@(CreateBlock (honest {p} {t} {block = b} refl lookup≡just-lₚ _ _)) ∷′ N′↝⋆N₂)
      N₁×p₁≡t₁ N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
      with p₁ ℕ.≟ p
```
```agda
    ... | no p₁≢p =
      let r = ∈ₖᵥ-lookup⁺ (∈ₖᵥ-insert⁺ p₁≢p (∈ₖᵥ-lookup⁻ {m = stateMap N₁} N₁×p₁≡t₁))
      in knowledge-propagation h₁ h₂ p₁∈ps p₂∈ps (↝∘↝⋆ N₀↝⋆N₁ N₁↝N′) N′↝⋆N₂ r N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
    ... | yes p₁≡p =
      let lookup-insert≡id = ∈ₖᵥ-lookup⁺ (∈ₖᵥ-insert⁺⁺ {p} {x = ⟪ extendTree blockTree t b ⟫} {m = stateMap N₁})
          lookup-p₁≡lookup-p = cong (lookup (insert p ⟪ extendTree blockTree t b ⟫ (stateMap N₁))) p₁≡p
          t≡t₁ = sym $ ⟪⟫-injective $ just-injective $ trans (sym N₁×p₁≡t₁) (trans (cong (lookup (stateMap N₁)) p₁≡p) lookup≡just-lₚ)
          N′×p₁≡t′ = trans (trans lookup-p₁≡lookup-p lookup-insert≡id) (cong just $ cong ⟪_⟫ $ cong (flip (extendTree blockTree) b) t≡t₁)
          H₀ = knowledge-propagation {t₁ = extendTree blockTree t₁ b} h₁ h₂ p₁∈ps p₂∈ps (↝∘↝⋆ N₀↝⋆N₁ N₁↝N′) N′↝⋆N₂ N′×p₁≡t′ N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
          ⊆-ext = proj₂ $ extendable (is-TreeType blockTree) t₁ b
      in x∷xs⊆ys→xs⊆ys $ ⊆-trans ⊆-ext H₀
      where
         x∷xs⊆ys→xs⊆ys : ∀ {x xs ys}
           → x ∷ xs ⊆ ys
           → xs ⊆ ys
         x∷xs⊆ys→xs⊆ys {x} {xs} = ⊆-trans (xs⊆x∷xs xs x)
```
```agda
    knowledge-propagation {N₁} {N₂} {p₁} {p₂} {t₁} {t₂} h₁ h₂ p₁∈ps p₂∈ps N₀↝⋆N₁ (N₁↝N′@(CreateBlock (honest-cooldown {p} {t} {block = b} refl lookup≡just-lₚ _ _ _ _ _)) ∷′ N′↝⋆N₂)
      N₁×p₁≡t₁ N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
      with p₁ ℕ.≟ p
```
```agda
    ... | no p₁≢p =
      let r = ∈ₖᵥ-lookup⁺ (∈ₖᵥ-insert⁺ p₁≢p (∈ₖᵥ-lookup⁻ {m = stateMap N₁} N₁×p₁≡t₁))
      in knowledge-propagation h₁ h₂ p₁∈ps p₂∈ps (↝∘↝⋆ N₀↝⋆N₁ N₁↝N′) N′↝⋆N₂ r N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
    ... | yes p₁≡p =
      let lookup-insert≡id = ∈ₖᵥ-lookup⁺ (∈ₖᵥ-insert⁺⁺ {p} {x = ⟪ extendTree blockTree t b ⟫} {m = stateMap N₁})
          lookup-p₁≡lookup-p = cong (lookup (insert p ⟪ extendTree blockTree t b ⟫ (stateMap N₁))) p₁≡p
          t≡t₁ = sym $ ⟪⟫-injective $ just-injective $ trans (sym N₁×p₁≡t₁) (trans (cong (lookup (stateMap N₁)) p₁≡p) lookup≡just-lₚ)
          N′×p₁≡t′ = trans (trans lookup-p₁≡lookup-p lookup-insert≡id) (cong just $ cong ⟪_⟫ $ cong (flip (extendTree blockTree) b) t≡t₁)
          H₀ = knowledge-propagation {t₁ = extendTree blockTree t₁ b} h₁ h₂ p₁∈ps p₂∈ps (↝∘↝⋆ N₀↝⋆N₁ N₁↝N′) N′↝⋆N₂ N′×p₁≡t′ N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
          ⊆-ext = proj₂ $ extendable (is-TreeType blockTree) t₁ b
      in x∷xs⊆ys→xs⊆ys $ ⊆-trans ⊆-ext H₀
      where
         x∷xs⊆ys→xs⊆ys : ∀ {x xs ys}
           → x ∷ xs ⊆ ys
           → xs ⊆ ys
         x∷xs⊆ys→xs⊆ys {x} {xs} = ⊆-trans (xs⊆x∷xs xs x)
```
#### NextSlot
```agda
    knowledge-propagation {N₁} {N₂} _ _ p₁∈ps p₂∈ps _ ((NextSlot _) ∷′ N′↝⋆N₂) _ _ _ clock-N₁≡clock-N₂ _ =
      let 1+c≤c = ≤-trans (≤-reflexive (cong ℕ.suc (sym clock-N₁≡clock-N₂))) (clock-incr⋆ N′↝⋆N₂)
          1+c≰c = 1+n≰n {clock N₂}
      in contradiction 1+c≤c 1+c≰c
```
```agda
    postulate
      luckySlots : Slot × Slot → ℕ
      superSlots : Slot × Slot → ℕ
      adversarialSlots : Slot × Slot → ℕ
```

The chain growth property informally says that in each period, the best chain of any honest
party will increase at least by a number that is proportional to the number of lucky slots in
that period.

```agda
    postulate
      chain-growth : ∀ {N₁ N₂ : GlobalState}
        → {p₁ p₂ : PartyId}
        → {h₁ : Honesty p₁} {h₂ : Honesty p₂}
        → {t₁ t₂ : A}
        → {w : ℕ}
        → h₁ ≡ Honest {p₁}
        → h₂ ≡ Honest {p₂}
        → N₀ ↝⋆ N₁
        → N₁ ↝⋆ N₂
        → lookup (stateMap N₁) p₁ ≡ just ⟪ t₁ ⟫
        → lookup (stateMap N₂) p₂ ≡ just ⟪ t₂ ⟫
        → luckySlots (clock N₁ , clock N₂) ≥ w
        → let c₁ = bestChain blockTree ((clock N₁) ∸ 1) t₁
              c₂ = bestChain blockTree ((clock N₂) ∸ 1) t₂
              cs₁ = certs blockTree t₁
              cs₂ = certs blockTree t₂
          in ∥ c₁ ∥ cs₁ + w ≤ ∥ c₂ ∥ cs₂
```

## Chain quality

The chain quality property informally says that within any chunk of consecutive blocks in an
honest party's best chain, there is an honest share of blocks. This share is proportional to
the difference between the number of honest and adversarial slots.

```agda

```

## Common prefix

The common prefix property informally says that during the execution of the protocol the
chains of honest parties will always be a common prefix of each other.

```agda
    postulate
      common-prefix : ∀ {N : GlobalState}
        → {p : PartyId} {h : Honesty p} {c : Chain} {k : Slot} {bh : List Block} {t : A}
        → lookup (stateMap N) p ≡ just ⟪ t ⟫
        → N₀ ↝⋆ N
        → ForgingFree N
        → CollisionFree N
        → h ≡ Honest {p}
        → let sl = clock N
          in prune k (bestChain blockTree (sl ∸ 1) t) ⪯ c
           ⊎ ∃[ sl′ ] (sl′ < k × superSlots (sl′ , sl) < 2 * adversarialSlots (sl′ , sl))
```
## Timed common prefix

```agda

```
