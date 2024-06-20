```agda
module Peras.Chain where
```

<!--
```agda
open import Data.Bool using (_∧_; true; false)
open import Data.List using (sum; upTo; applyUpTo; filterᵇ; filter; concat; catMaybes; zip) renaming (length to ∣_∣)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (any?; Any; here; there; lookup)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe as M using (nothing; just)
open import Data.Nat using (ℕ; _/_; _>_; _≥_; _≥?_; _≤?_; NonZero; pred; _∸_; z≤n; s≤s)
open import Data.Nat using (_≤_; _<_; _∸_)
open import Data.Nat.Properties using (n≮n; _≟_)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
open import Function.Base using (_∘_; _$_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_)
open import Relation.Binary using (DecidableEquality)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≢_)

open import Peras.Crypto
open import Peras.Block
open import Peras.Numbering
open import Peras.Params

open import Haskell.Prelude hiding (length; trans; _<_; _>_; _∘_; sum; b; pred; filter; concat; _$_; lookup; zip; All; _,_; _×_)

{-# FOREIGN AGDA2HS
{-# LANGUAGE DeriveGeneric #-}
import GHC.Generics (Generic)
#-}

{-# FOREIGN GHC
import qualified Peras.Chain as G
#-}
```
-->

## Voting

### Vote

```agda
record Vote : Set where
  constructor MkVote
  field votingRound : RoundNumber
        creatorId   : PartyId
        proofM      : MembershipProof
        blockHash   : Hash Block
        signature   : Signature

  votingRound' : ℕ
  votingRound' = getRoundNumber votingRound

open Vote public

instance
  iVoteEq : Eq Vote
  iVoteEq ._==_ x y = votingRound x == votingRound y
                        && creatorId x == creatorId y
                        && proofM x == proofM y
                        && blockHash x == blockHash y
                        && signature x == signature y
```

<!--
```agda
{-# COMPILE AGDA2HS Vote deriving (Generic) #-}
{-# COMPILE GHC Vote = data G.Vote (G.MkVote) #-}
{-# COMPILE AGDA2HS iVoteEq #-}
```
-->

<!--
```agda
{-
toSignable : ∀{msg} → Vote msg -> ByteString
toSignable _ = emptyBS -- const ""
-}

{-
postulate
  makeVote : ∀{msg} → RoundNumber -> PartyId -> msg -> Vote msg
-}
```
-->

<!--
```agda
-- | A vote is valid if the committee-membership proof and the signature are valid.
{-
isValid : ∀{msg} → Vote msg -> Bool
isValid v@(vote _ (MkPartyId vkey) committeeMembershipProof _ signature) =
  isCommitteeMember vkey committeeMembershipProof
    ∧ verify vkey signature (toSignable v)
-}
```
-->
```agda
record Postulates : Set₁ where
  field
    IsSlotLeader : PartyId → SlotNumber → LeadershipProof → Set
    IsCommitteeMember : PartyId → RoundNumber → MembershipProof → Set
    IsBlockSignature : Block → Signature → Set
    IsVoteSignature : Vote → Signature → Set

record Network : Set₁ where
  field
    block₀ : Block
    Δ : ℕ
```
```agda
module _ ⦃ _ : Postulates ⦄

         where

  open Postulates ⦃...⦄

  ValidVote : Vote → Set
  ValidVote v =
    IsCommitteeMember
        (creatorId v)
        (votingRound v)
        (proofM v)
    × IsVoteSignature v (signature v)
```

### Equivocation relation

Equivocal votes are multiple votes by the same party for the same round.

```agda
data _∻_ : Vote → Vote → Set where

  Equivocation : ∀ {v₁ v₂}
    → creatorId v₁ ≡ creatorId v₂
    → votingRound v₁ ≡ votingRound v₂
    → v₁ ≢ v₂
    → v₁ ∻ v₂
```
<!--
```agda
-- NonEquivocation : Vote → Vote → Set
-- NonEquivocation v₁ v₂ = ¬ (v₁ ∻ v₂)

-- open import Data.List.Relation.Unary.AllPairs.Core NonEquivocation renaming (AllPairs to NoEquivocations) public
```
-->

## Chain

```agda
Chain = List Block
```
<!--
```agda
{-# COMPILE AGDA2HS Chain #-}
```
-->

### Chain prefix

```agda
data _⪯_ : Chain → Chain → Set where

  Prefix : ∀ {c₁ c₂ c₃ : Chain}
    → c₁ ++ c₃ ≡ c₂
    → c₁ ⪯ c₂
```

### Chain pruning

```agda
prune : SlotNumber → Chain → Chain
prune (MkSlotNumber sl) = filter ((_≤? sl) ∘ slotNumber')
```
### Chain weight

The weight of a chain is defined with respect of the Peras parameters
```agda
open Params ⦃...⦄
```
The weight of a chain is computed wrt to a set of dangling votes
```agda
module _ ⦃ _ : Hashable Block ⦄
         ⦃ _ : Params ⦄
         where
```
```agda
  open Hashable ⦃...⦄
```
```agda
  _PointsInto_ : Certificate → Chain → Set
  _PointsInto_ c = Any ((blockRef c ≡_) ∘ hash)
```
```agda
  _PointsInto?_ : ∀ (c : Certificate) → (ch : Chain) → Dec (c PointsInto ch)
  _PointsInto?_ c = any? ((blockRef c ≟-BlockHash_) ∘ hash)
```
```agda
  StartOfRound : SlotNumber → RoundNumber → Set
  StartOfRound (MkSlotNumber sl) (MkRoundNumber r) = sl ≡ r * U
```
```agda
  rnd : ℕ → ⦃ _ : NonZero U ⦄ → ℕ
  rnd s = s / U
```
```agda
  v-round : SlotNumber → RoundNumber
  v-round (MkSlotNumber s) = MkRoundNumber (rnd s)
```
### Chain weight

```agda
  ∥_∥_ : Chain → List Certificate → ℕ
  ∥ ch ∥ cts = ∣ ch ∣ + ∣ filter (_PointsInto? ch) cts ∣ * B
```

### Chain validity

<!--
```agda
open import Relation.Nullary.Negation using (¬_)

import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (trans)

open Block

open import Data.List.Membership.Propositional using (_∈_)
```
-->
```agda
module _ ⦃ _ : Hashable Block ⦄
         ⦃ _ : Postulates ⦄
         ⦃ _ : Network ⦄

         where

  open Hashable ⦃...⦄
  open Postulates ⦃...⦄
  open Network ⦃...⦄
```
```agda
  data ValidChain : Chain → Set where

    Genesis :
      ValidChain (block₀ ∷ [])

    Cons : ∀ {c₁ c₂ : Chain} {b₁ b₂ : Block}
      → IsBlockSignature b₁ (signature b₁)
      → IsSlotLeader (creatorId b₁) (slotNumber b₁) (leadershipProof b₁)
      → parentBlock b₁ ≡ hash b₂
      → c₂ ≡ b₂ ∷ c₁
      → ValidChain c₂
      → ValidChain (b₁ ∷ c₂)
```
```agda
  tip : ∀ {c : Chain} → ValidChain c → Block
  tip Genesis = block₀
  tip (Cons {b₁ = b} _ _ refl refl _) = b
```
```agda
  uncons : ∀ {c : Chain} → (v : ValidChain c) → Σ[ (b , d) ∈ Block × Chain ] (c ≡ b ∷ d)
  uncons {block₀ ∷ .[]} Genesis = (block₀ , []) , refl
  uncons {b₁ ∷ b₂ ∷ c₁} (Cons _ _ refl refl _) = (b₁ , (b₂ ∷ c₁)) , cong (_∷ (b₂ ∷ c₁)) refl
```
```agda
  certsFromChain : Chain → List Certificate
  certsFromChain = catMaybes ∘ map certificate
```
<!--
```agda
-- | `foldl` does not exist in `Haskell.Prelude` so let's roll our own
-- but let's make it total.
foldl1Maybe : ∀ {a : Set} -> (a -> a -> a) -> List a -> Maybe a
foldl1Maybe f xs =
  foldl (λ m y -> Just (case m of λ where
                             Nothing -> y
                             (Just x)  -> f x y))
        Nothing xs

{-# COMPILE AGDA2HS foldl1Maybe #-}

prefix : List Block -> List Block -> List Block -> List Block
prefix acc (x ∷ xs) (y ∷ ys) =
  if x == y
   then prefix (x ∷ acc) xs ys
   else reverse acc
prefix acc _ _ = reverse acc

{-# COMPILE AGDA2HS prefix #-}

commonPrefix : List Chain -> List Block
commonPrefix chains =
  case listPrefix of λ where
     Nothing -> []
     (Just bs) -> reverse bs
   where
     listPrefix : Maybe (List Block)
     listPrefix = foldl1Maybe (prefix []) (map (λ l -> reverse l) chains)

{-# COMPILE AGDA2HS commonPrefix #-}

-- I wish I could prove that and translate it to a QC property in Haskell :)
-- commonPrefixEq : {t : Set } -> ⦃ eqt : Eq t ⦄ -> (c₁ c₂ : Chain t) -> (c₁ ≡ c₂) -> (commonPrefix (c₁ ∷ c₂ ∷ []) ≡ c₁)
-- commonPrefixEq = {!!}

{-
postulate
  verifyLeadershipProof : Block → Bool

  properlyLinked : Chain → Bool
  decreasingSlots : Chain → Bool
-}

{-
correctBlocks : Chain → Bool
correctBlocks (MkChain blocks _ _) =
  let bs = toList BlockO blocks
  in all verifyLeadershipProof bs
-}
```
-->
