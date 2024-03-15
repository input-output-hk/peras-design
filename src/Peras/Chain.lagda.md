```agda
module Peras.Chain where
```

<!--
```agda
open import Data.Bool using (_∧_; true; false)
open import Data.List using (length; sum; upTo; applyUpTo; filterᵇ; filter; concat; catMaybes; zip)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (any?; Any; here; there; lookup)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe as M using (nothing; just)
open import Data.Nat using (ℕ; _/_; _>_; _≥_; _≥?_; NonZero; pred; _∸_; z≤n; s≤s)
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
open import Peras.Params

open import Haskell.Prelude hiding (length; trans; _<_; _>_; _∘_; sum; b; pred; filter; concat; _$_; lookup; zip; All; _,_; _×_)
{-# FOREIGN AGDA2HS import Peras.Crypto (Hash (..), Hashable (..)) #-}
```
-->

## Voting

### Round number

```agda
record RoundNumber : Set where
  constructor MkRoundNumber
  field roundNumber : ℕ

  prev : RoundNumber
  prev = record { roundNumber = pred roundNumber }

open RoundNumber public
```

<!--
```agda
{-# COMPILE AGDA2HS RoundNumber newtype deriving Eq #-}
```
-->

```agda
_≟-RoundNumber_ : DecidableEquality RoundNumber
(MkRoundNumber r₁) ≟-RoundNumber (MkRoundNumber r₂) with r₁ ≟ r₂
... | yes p = yes (cong MkRoundNumber p)
... | no ¬p =  no (¬p ∘ cong roundNumber)

```

<!--
### Vote

```agda
record Vote : Set where
  constructor MkVote
  field votingRound              : RoundNumber
        creatorId                : PartyId
        committeeMembershipProof : MembershipProof
        blockHash                : Hash
        signature                : Signature

open Vote public
```
-->

<!--
```agda
{-# COMPILE AGDA2HS Vote deriving Eq #-}
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

```agda
-- NonEquivocation : Vote → Vote → Set
-- NonEquivocation v₁ v₂ = ¬ (v₁ ∻ v₂)

-- open import Data.List.Relation.Unary.AllPairs.Core NonEquivocation renaming (AllPairs to NoEquivocations) public
```

## Chain

```agda
Chain = List Block
```
<!--
```agda
{-# COMPILE AGDA2HS Chain deriving Eq #-}
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
prune : Slot → Chain → Chain
prune sl c = c -- TODO: {b ← c | slot b ≤ sl}.
```

### Chain length

```agda
∣_∣ : Chain → ℕ
∣_∣ = length
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

  instance
    nonZero : NonZero T -- TODO: why is this needed..?
    nonZero = T-nonZero

  open Hashable ⦃...⦄
```

### Chain state

In a cooldown period there is no voting.

```agda
  data Reference : Certificate → Chain → Set where

  postulate
    Reference? : ∀ (c : Chain) → (cert : Certificate) → Dec (Reference cert c)
```

There is not voting in round 0

```agda
--  round≡0→¬VoteInRound : ∀ {c : Chain} → {r : RoundNumber} → roundNumber r ≡ 0 → ¬ (VoteInRound c r)
--  round≡0→¬VoteInRound refl (Last r _) = (n≮n 0) r
--  round≡0→¬VoteInRound refl (CooldownIsOver _ r _ _) = (n≮n 0) r
```

```agda
--  postulate
--    VoteInRound? : ∀ (c : ChainState) → (r : RoundNumber) → Dec (VoteInRound c r)
```
<!--
```agda
    -- VoteInRound? c r@(MkRoundNumber zero) = no λ x → let ¬p = round≡0→¬VoteInRound {c} {r} refl in ¬p x
    -- VoteInRound? c r@(MkRoundNumber (suc _)) with QuorumOnChain? c (prev r)
    -- ... | yes p = yes (Last (s≤s z≤n) p)
    -- ... | no ¬p = {!!}
```
-->
```agda
--  round-r-votes : ChainState → RoundNumber → ℕ
--  round-r-votes ⟨ c , d , p ⟩ r = sum (map (weightOfBlock ⟨ c , d , p ⟩ r) (blocks c))

  StartOfRound : Slot → RoundNumber → Set
  StartOfRound sl (MkRoundNumber r) = sl ≡ r * T

```

```agda
  v-round : Slot → ⦃ _ : NonZero T ⦄ → RoundNumber
  v-round s = MkRoundNumber (s / T)
```

### Chain weight

```agda
  ∥_,_∥ : Chain → List Certificate → ℕ
  ∥ c , cs ∥ = ∣ c ∣ + (B * length (filter (Reference? c) cs))
```

### Chain validity

<!--
```agda
-- open import Data.List.Relation.Unary.Unique.Propositional {A = Vote}
open import Relation.Nullary.Negation using (¬_)

import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (trans)

open Block

open import Data.List.Membership.Propositional using (_∈_)
```
-->
A chain is valid iff:
  * the blocks (ignoring the vote hashes) form a valid Praos chain
     * all blocks in the chain are valid -- TODO
     * the chain is linked correctly
     * the slots are strictly decreasing -- TODO
  * all votes:
    * are referenced by a unique block with a slot number *s*
      strictly larger than the slot number corresponding to the
      vote’s round number r (i.e., r*T < s),
    * point to a block on the chain at least L slots in the past
      (i.e., to a block with slot number s < r*T - L), and
  * it contains no vote equivocations (i.e., multiple votes by the
    same party for the same round)
```agda
module _ {block₀ : Block}
         ⦃ _ : Hashable Block ⦄
         ⦃ _ : Params ⦄
         where

  open Hashable ⦃...⦄
```
```agda
  data ValidChain : Chain → Set where

    Genesis :
      ValidChain (block₀ ∷ [])

    Cons : ∀ {c : Chain} {b₁ b₂ : Block}
      → parentBlock b₂ ≡ hash b₁
      → ValidChain (b₂ ∷ c)
      → ValidChain (b₁ ∷ (b₂ ∷ c))
```

```agda
  tip : ∀ {c : Chain} → ValidChain c → Block
  tip Genesis = block₀
  tip (Cons {c} {b₁} refl _) = b₁
```

#### Properties

For a valid chain we can show, that the blocks are non-empty without relying on the
property in `non-empty` of the `Chain`.

```agda
--  instance
--    itsNonEmptyChain : ∀ {c : Chain} → {ValidChain c} → NonEmpty (blocks c)
--    itsNonEmptyChain {MkChain (x ∷ _) _ } = NonEmpty.itsNonEmpty
```

The last block in a valid chain is always the genesis block.

```agda
{-
  last-is-block₀-Praos : ∀ {c : Chain}
    → (v : ValidPraosChain c)
    → last (blocks c) ⦃ itsNonEmptyPraosChain {c} {v} ⦄ ≡ block₀
  last-is-block₀-Praos Genesis = refl
  last-is-block₀-Praos (Cons {_} {c} {b} _ v) =
    trans
      (drop-head (blocks c) b ⦃ itsNonEmptyPraosChain {c} {v} ⦄)
      (last-is-block₀-Praos {c} v)
    where
      drop-head : ∀ {A : Set} → (c : List A) → (b : A) → ⦃ _ : NonEmpty c ⦄ → last (b ∷ c) ≡ last c
      drop-head (_ ∷ _) _ ⦃ NonEmpty.itsNonEmpty ⦄ = refl

  validPraos : ∀ {c} → ValidChain c → ValidPraosChain c
  validPraos (VotesCondition x _ _ _ _) = x

  last-is-block₀ : ∀ {c : Chain}
    → (v : ValidChain c)
    → last (blocks c) ⦃ itsNonEmptyPraosChain {c} {validPraos v} ⦄ ≡ block₀
  last-is-block₀ (VotesCondition x _ _ _ _) = last-is-block₀-Praos x
-}
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

instance
  postulate
    iBlockEq : Eq Block

-- {-# COMPILE AGDA2HS iBlockEq #-}

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
