```agda
module Peras.SmallStep.Properties where
```

<!--
```agda
open import Data.Bool as Bool using (Bool; true; false)
open import Data.List as List using (List; []; _∷_; null; map; _++_; foldr)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ʳ)

open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Relation.Unary.Any as Any using (Any; _─_; _∷=_; here; there)
open import Data.List.Relation.Unary.Any.Properties using (¬Any[])
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.All.Properties as All using (¬All⇒Any¬; All¬⇒¬Any; ─⁺; ─⁻)

open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Fin using (zero; suc; _≟_)
open import Data.Fin.Properties using (0≢1+n)
open import Data.Nat as ℕ using (ℕ; _∸_; _<_; _≤_; _≥_; _*_; _+_; pred)
open import Data.Nat.Properties using (n≤1+n; 1+n≰n; ≤-refl; ≤-reflexive; ≤-trans)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Function.Base using (_∘_; id; _$_; flip)

open import Relation.Nullary using (yes; no; ¬_)
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
    states₀ = foldr (λ { (p , _) m → insert p state₀ m }) empty parties

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
```agda
    clock-incr : ∀ {M N : GlobalState}
      → M ↝ N
      → clock M ≤ clock N
    clock-incr {⟦ c , _ , _ , _ , _ ⟧} {⟦ c , _ , _ , _ , _ ⟧} (Deliver (honest _ _ _)) = ≤-refl
    clock-incr {⟦ c , _ , _ , _ , _ ⟧} {⟦ c , _ , _ , _ , _ ⟧} (Deliver (corrupt _)) = ≤-refl
    clock-incr {⟦ c , _ , _ , _ , _ ⟧} {⟦ c , _ , _ , _ , _ ⟧} (CastVote (honest _ _ _ _ _ _)) = ≤-refl
    clock-incr {⟦ c , _ , _ , _ , _ ⟧} {⟦ c , _ , _ , _ , _ ⟧} (CreateBlock (honest _ _ _ _ _)) = ≤-refl
    clock-incr {M} (NextSlot _) = n≤1+n (clock M)

    clock-incr⋆ : ∀ {M N : GlobalState}
      → M ↝⋆ N
      → clock M ≤ clock N
    clock-incr⋆ (_ ∎) = ≤-refl
    clock-incr⋆ (_ ↝⟨ x ⟩ x₁) = ≤-trans (clock-incr x) (clock-incr⋆ x₁)
```
### Knowledge propagation

```agda
    All-∷= : {a p : Level} {A : Set a} {P : Pred A p} {x y : A} {xs : List A}
      → All P xs
      → (x∈xs : x ∈ xs)
      → P y
      → All P (x∈xs ∷= y)
    All-∷= (_ All.∷ x₁) (here refl) x₂ = x₂ All.∷ x₁
    All-∷= (px All.∷ x₁) (there x∈xs) x₂ = px All.∷ (All-∷= x₁ x∈xs x₂)
```
TODO: proof
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
               s ≡ ↝⋆∘↝⋆ s₀ (_ ↝⟨ s₁ ⟩ s₂) × ⦅ p , Honest , BlockMsg b , zero ⦆ ∈ messages M′))
```
<!--
```agda
{-
    m′∈ms─m∈ms : ∀ {m m′ : Envelope} {ms}
      → (m∈ms : m ∈ ms)
      → (m′∈ms  : m′ ∈ ms)
      → m ≢ m′
      → m′ ∈ (ms ─ m∈ms)
    m′∈ms─m∈ms {m} {m′} {ms} m∈ms m′∈ms = {!!}
-}
    CertMsg≢BlockMsg : ∀ {p q c b} → ⦅ p , Honest , CertMsg c , zero ⦆ ≢ ⦅ q , Honest , BlockMsg b , zero ⦆
    CertMsg≢BlockMsg x with cong message x
    ... | ()

    VoteMsg≢BlockMsg : ∀ {p q v b} → ⦅ p , Honest , VoteMsg v , zero ⦆ ≢ ⦅ q , Honest , BlockMsg b , zero ⦆
    VoteMsg≢BlockMsg x with cong message x
    ... | ()

    ⊆-vote : ∀ {M N : GlobalState} {p} {h : Honesty p}
      → M [ h ]⇉ N
      → messages M ⊆ᵐ messages N
    ⊆-vote (honest {vote = v} refl _ _ _ _ _) = ∈-++⁺ʳ $ map (λ { (p₁ , h) → ⦅ p₁ , h , VoteMsg v , zero ⦆}) parties

    ⊆-block : ∀ {M N : GlobalState} {p} {h : Honesty p}
      → M [ h ]↷ N
      → messages M ⊆ᵐ messages N
    ⊆-block (honest {block = b} refl _ _ _ _) = ∈-++⁺ʳ $ map (λ { (p₁ , h) → ⦅ p₁ , h , BlockMsg b , zero ⦆}) parties
```
-->
```agda
    postulate
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
<!--
```agda
{-
    knowledge-propagation₂ {M} p∈ps N₀↝⋆M (_ ∎) m∈ms x₄ Delivered-M =
      let xx = All¬⇒¬Any Delivered-M
          yy = m∈ms
      in contradiction {!!} xx
    knowledge-propagation₂ {M} {N} {p} p∈ps N₀↝⋆M (_ ↝⟨ M↝M′@(Deliver (honest x m′∈ms VoteReceived)) ⟩ M′↝⋆N) m∈ms x₄ Delivered-N =
       knowledge-propagation₂ p∈ps (↝∘↝⋆ N₀↝⋆M M↝M′) M′↝⋆N (m′∈ms─m∈ms m′∈ms m∈ms VoteMsg≢BlockMsg) x₄ Delivered-N       
    knowledge-propagation₂ {M} {N} {p} p∈ps N₀↝⋆M (_ ↝⟨ M↝M′@(Deliver (honest x m′∈ms CertReceived)) ⟩ M′↝⋆N) m∈ms x₄ Delivered-N =
       knowledge-propagation₂ p∈ps (↝∘↝⋆ N₀↝⋆M M↝M′) M′↝⋆N (m′∈ms─m∈ms m′∈ms m∈ms CertMsg≢BlockMsg) x₄ Delivered-N
    knowledge-propagation₂ {M} {N} {p} p∈ps N₀↝⋆M (_ ↝⟨ M↝M′@(Deliver (honest {p′} x m′∈ms (BlockReceived {b}))) ⟩ M′↝⋆N) m∈ms x₄ Delivered-N
      with p ℕ.≟ p′
    ... | yes p≡p′ = {!!}  -- into the tree in this step
    ... | no p≢p′ =
      let m≢m′ = ⦅⦆-injective′ (p≢p′ ∘ sym)
      in knowledge-propagation₂ p∈ps (↝∘↝⋆ N₀↝⋆M M↝M′) M′↝⋆N (m′∈ms─m∈ms m′∈ms m∈ms m≢m′) x₄ Delivered-N

    knowledge-propagation₂ {M} {N} {p} {t} {b} p∈ps N₀↝⋆M (_ ↝⟨ M↝M′@(Deliver (corrupt _)) ⟩ M′↝⋆N) m∈ms m′∈ms Delivered-N =
       knowledge-propagation₂ p∈ps (↝∘↝⋆ N₀↝⋆M M↝M′) M′↝⋆N {- (m′∈ms─m∈ms m′∈ms m∈ms m≢m′)-} {!!} m′∈ms Delivered-N

    knowledge-propagation₂ p∈ps N₀↝⋆M (_ ↝⟨ M↝M′@(CastVote x₂) ⟩ M′↝⋆N) m∈ms x₄ Delivered-N = knowledge-propagation₂ p∈ps (↝∘↝⋆ N₀↝⋆M M↝M′) M′↝⋆N (⊆-vote x₂ m∈ms) x₄ Delivered-N
    knowledge-propagation₂ p∈ps N₀↝⋆M (_ ↝⟨ M↝M′@(CreateBlock x₂) ⟩ M′↝⋆N) m∈ms x₄ Delivered-N = knowledge-propagation₂ p∈ps (↝∘↝⋆ N₀↝⋆M M↝M′) M′↝⋆N (⊆-block x₂ m∈ms) x₄ Delivered-N
    knowledge-propagation₂ p∈ps N₀↝⋆M (_ ↝⟨ M↝M′@(NextSlot x₂) ⟩ M′↝⋆N) m∈ms x₄ Delivered-N = knowledge-propagation₂ p∈ps (↝∘↝⋆ N₀↝⋆M M↝M′) M′↝⋆N {!!} x₄ Delivered-N
-}
```
-->
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
    knowledge-propagation {N₁} _ _ p₁∈ps p₂∈ps N₀↝⋆N₁ (_ ∎) N₁×p₁≡t₁ N₂×p₂≡t₂ Delivered-N₂ _ = knowledge-propagation₀ p₁∈ps p₂∈ps N₀↝⋆N₁ N₁×p₁≡t₁ N₂×p₂≡t₂ Delivered-N₂
```
#### Deliver
```agda
    knowledge-propagation {N₁} {N₂} {p₁} {p₂} {t₁} {t₂}
      h₁ h₂ p₁∈ps p₂∈ps N₀↝⋆N₁ (_ ↝⟨ N₁↝N′@(Deliver (honest {p} {lₚ} {.(⟪ extendTree blockTree _ _ ⟫)} {.(BlockMsg _)} lookup≡just-lₚ m∈ms (BlockReceived {b} {t}))) ⟩ N′↝⋆N₂)
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
      h₁ h₂ p₁∈ps p₂∈ps N₀↝⋆N₁ (_ ↝⟨ N₁↝N′@(Deliver {N₁} {N′} (honest {p} {⟪ t ⟫} {.(⟪ addVote blockTree _ _ ⟫)} {.(VoteMsg _)} lookup≡just-lₚ m∈ms (VoteReceived {v}))) ⟩ N′↝⋆N₂)
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
```agda
    knowledge-propagation {N₁} {N₂} {p₁} {p₂} {t₁} {t₂}
      h₁ h₂ p₁∈ps p₂∈ps N₀↝⋆N₁ (_ ↝⟨ N₁↝N′@(Deliver {N₁} {N′} (honest {p} {⟪ t ⟫} {.(⟪ addCert blockTree _ _ ⟫)} {.(CertMsg _)} lookup≡just-lₚ m∈ms (CertReceived {c}) )) ⟩ N′↝⋆N₂)
      N₁×p₁≡t₁ N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
      with p₁ ℕ.≟ p
    ... | no p₁≢p =
      let r = ∈ₖᵥ-lookup⁺ (∈ₖᵥ-insert⁺ p₁≢p (∈ₖᵥ-lookup⁻ {m = stateMap N₁} N₁×p₁≡t₁))
      in knowledge-propagation {p₁ = p₁} h₁ h₂ p₁∈ps p₂∈ps (↝∘↝⋆ N₀↝⋆N₁ N₁↝N′) N′↝⋆N₂ r N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
    ... | yes p₁≡p =
      let lookup-insert≡id = ∈ₖᵥ-lookup⁺ (∈ₖᵥ-insert⁺⁺ {p} {x = ⟪ addCert blockTree t c ⟫} {m = stateMap N₁})
          lookup-p₁≡lookup-p = cong (lookup (insert p ⟪ addCert blockTree t c ⟫ (stateMap N₁))) p₁≡p
          t≡t₁ = sym $ ⟪⟫-injective $ just-injective $ trans (sym N₁×p₁≡t₁) (trans (cong (lookup (stateMap N₁)) p₁≡p) lookup≡just-lₚ)
          N′×p₁≡t′ = trans (trans lookup-p₁≡lookup-p lookup-insert≡id) (cong just $ cong ⟪_⟫ $ cong (flip (addCert blockTree) c) t≡t₁)
          H₀ = knowledge-propagation {t₁ = addCert blockTree t₁ c} h₁ h₂ p₁∈ps p₂∈ps (↝∘↝⋆ N₀↝⋆N₁ N₁↝N′) N′↝⋆N₂ N′×p₁≡t′ N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
          ⊆-ext = proj₂ $ extendable-certs (is-TreeType blockTree) t₁ c
      in ⊆-trans ⊆-ext H₀
```
Adversarial behaviour: potentially adds a block to p₂'s blocktree in the next slot
```agda
    knowledge-propagation {N₁} {N₂} {p₁} {p₂} {t₁} {t₂} {honesty₁} {honesty₂} h₁ h₂ p₁∈ps p₂∈ps N₀↝⋆N₁ (_ ↝⟨ N₁↝N′@(Deliver {N₁} {N′} {p} {h} (corrupt {p} m∈ms)) ⟩ N′↝⋆N₂)
      N₁×p₁≡t₁ N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
      with p₁ ℕ.≟ p
    ... | no p₁≢p = knowledge-propagation h₁ h₂ p₁∈ps p₂∈ps (↝∘↝⋆ N₀↝⋆N₁ N₁↝N′) N′↝⋆N₂ N₁×p₁≡t₁ N₂×p₂≡t₂ Delivered-N₂ clock-N₁≡clock-N₂
    ... | yes p₁≡p = contradiction p₁≡p (Honest≢Corrupt {p₁} {p} {honesty₁} {h} h₁ refl)
```
#### CastVote
CastVote is not relevant for allBlocks
```agda
    knowledge-propagation {N₁} {N₂} {p₁} {p₂} {t₁} {t₂} h₁ h₂ p₁∈ps p₂∈ps N₀↝⋆N₁ (_ ↝⟨ N₁↝N′@(CastVote {N₁} {N′} (honest {p} {t} {vote = v} refl lookup≡just-lₚ _ _ _ _)) ⟩ N′↝⋆N₂)
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
    knowledge-propagation {N₁} {N₂} {p₁} {p₂} {t₁} {t₂} h₁ h₂ p₁∈ps p₂∈ps N₀↝⋆N₁ (_ ↝⟨ N₁↝N′@(CreateBlock {N₁} {N′} (honest {p} {t} {block = b} refl lookup≡just-lₚ _ _ _)) ⟩ N′↝⋆N₂)
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
    knowledge-propagation {N₁} {N₂} _ _ p₁∈ps p₂∈ps _ (_ ↝⟨ (NextSlot _) ⟩ N′↝⋆N₂) _ _ _ clock-N₁≡clock-N₂ _ =
      let 1+c≤c = ≤-trans (≤-reflexive (cong ℕ.suc (sym clock-N₁≡clock-N₂))) (clock-incr⋆ N′↝⋆N₂)
          1+c≰c = 1+n≰n {clock N₂}
      in contradiction 1+c≤c 1+c≰c
```
## Chain growth
```agda
    postulate
      honest-chain-growth : ∀ {N₁ N₂ : GlobalState}
        → {p₁ p₂ : PartyId}
        → {h₁ : Honesty p₁} {h₂ : Honesty p₂}
        → {t₁ t₂ : A}
        → h₁ ≡ Honest {p₁}
        → h₂ ≡ Honest {p₂}
        → N₀ ↝⋆ N₁
        → N₁ ↝⋆ N₂
        → lookup (stateMap N₁) p₁ ≡ just ⟪ t₁ ⟫
        → lookup (stateMap N₂) p₂ ≡ just ⟪ t₂ ⟫
        → let c₁ = bestChain blockTree ((clock N₁) ∸ 1) t₁
              c₂ = bestChain blockTree ((clock N₂) ∸ 1) t₂
              cs₁ = certs blockTree t₁ c₁
              cs₂ = certs blockTree t₂ c₂
          in ∥ c₁ , cs₁ ∥ ≤ ∥ c₂ , cs₂ ∥
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
              cs₁ = certs blockTree t₁ c₁
              cs₂ = certs blockTree t₂ c₂
          in ∥ c₁ , cs₁ ∥ + w ≤ ∥ c₂ , cs₂ ∥
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
