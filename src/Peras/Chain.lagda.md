```agda
module Peras.Chain where
```

<!--
```agda
open import Data.Bool using (_∧_; true; false)
open import Data.List using (length; sum; upTo; applyUpTo; filterᵇ; filter; concat)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (any?; Any; here; there)
open import Data.Nat using (ℕ; _/_; _>_; _≥_; _≥?_; NonZero; pred; _∸_; z≤n; s≤s)
open import Data.Nat using (_≤_; _<_; _∸_)
open import Data.Nat.Properties using (n≮n; _≟_)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
open import Function.Base using (_∘_; _$_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_)
open import Relation.Binary using (DecidableEquality)

open import Peras.Crypto
open import Peras.Block
open import Peras.Params

open import Haskell.Prelude hiding (length; trans; _<_; _>_; _∘_; sum; b; pred; filter; concat; _$_)
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

### Vote

```agda
record Vote : Set where
  constructor MkVote
  field roundNr                  : RoundNumber
        creatorId                : PartyId
        committeeMembershipProof : MembershipProof
        blockHash                : Hash
        signature                : Signature

open Vote public
```

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

### Equivocation relation

```agda
data _∻_ : Vote → Vote → Set where

  -- TODO: add constructor
```
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

## Chain

 * The tip of this chain is the head of `blocks`
 * The set of "pending" votes, eg. which have not been included in a `Block`.

```agda
record Chain : Set where
  constructor MkChain
  field blocks : List Block
        votes : List Vote
        @0 non-empty : NonEmpty blocks

open Chain public
```

<!--
```agda
{-# COMPILE AGDA2HS Chain deriving Eq #-}
```
-->

```agda
tip : Chain → Block
tip (MkChain blocks _ non-empty) = head blocks ⦃ non-empty ⦄
```

<!--
```agda
{-# COMPILE AGDA2HS tip #-}
```
-->

### Chain state

```agda
record ChainState : Set where
  constructor ⟨_,_⟩
  field chain : Chain
        dangling : List Vote

open ChainState public
```

### Chain weight

The weight of a chain is defined with respect of the Peras parameters
```agda
open Params ⦃...⦄
```
The weight of a chain is computed wrt to a set of dangling votes
```agda
module _ ⦃ _ : Hashable Block ⦄
         ⦃ _ : Hashable Vote ⦄
         ⦃ _ : Params ⦄
         where

  instance
    nonZero : NonZero T -- TODO: why is this needed..?
    nonZero = T-nonZero

  open Hashable ⦃...⦄
```
Counting votes for a block from the dangling votes
```agda
  countDangling : List Vote → RoundNumber → Block → ℕ
  countDangling vs r b = length $
    filter (λ { v →
      (blockHash v ≟-Hash (hash b)) ×-dec
      (roundNr v ≟-RoundNumber r)
      })
    vs
```
Counting votes for a block from the blocks
FIXME: Only include votes for round r
```agda
  countBlocks : List Block → RoundNumber → Block → ℕ
  countBlocks bs (MkRoundNumber r) b = sum $
    map (λ {x →
      length $
        filter (λ {v → v ≟-Hash (hash b)})
          (includedVotes x)})
    bs
```
Counting votes for a block from dangling votes and votes on the chain
```agda
  countVotes : ChainState → RoundNumber → Block → ℕ
  countVotes ⟨ MkChain bs vs _ , d ⟩ r b =
    countBlocks bs r b + countDangling vs r b
```

### Dangling vote

```agda
  data Dangling : Chain → Vote → Set where

    C-Dangling : ∀ {r} {v} {b} {c}
      → let s = r * T in
        b ∈ blocks c
      → blockHash v ≡ hash b
      → slotNumber b ≥ (s ∸ Lₗ)
      → slotNumber b ≤ (s ∸ Lₕ)
      → ¬ (Any (λ { x → (hash v) ∈ (includedVotes x) } ) (blocks c))
      -- → ¬ (Any (λ { b → () }) (blocks c)) -- no equivocations
      → Dangling c v
```

### Quorum

The relation `QuorumOnChain` checks whether there is a round-r quorum with respect to
the votes on chain c and dangling votes for a block on chain c.

```agda
  data QuorumOnChain : ChainState → RoundNumber → Set where

    Initial : ∀ {c} {r}
      → roundNumber r ≡ 0
      → QuorumOnChain c r

    LaterRound : ∀ {c} {d} {r} {b}
      → roundNumber r > 0
      → b ∈ blocks c
      → countVotes ⟨ c , d ⟩ r b ≥ τ
      → QuorumOnChain ⟨ c , d ⟩ r
```

```agda
  postulate
    QuorumOnChain? : ∀ (c : ChainState) → (r : RoundNumber) → Dec (QuorumOnChain c r)
```

In a cooldown period there is no voting.

```agda
  data VoteInRound : ChainState → RoundNumber → Set where

    Last : ∀ {c d r}
      → roundNumber r > 0
      → All (Dangling c) d
      → QuorumOnChain ⟨ c , d ⟩ (prev r)
      → VoteInRound ⟨ c , d ⟩ r

    CooldownIsOver : ∀ {c d r n}
      → n > 0
      → roundNumber r > 0
      → All (Dangling c) d
      → QuorumOnChain ⟨ c , d ⟩ (MkRoundNumber (roundNumber r ∸ (n * K)))
      → All (λ { i → ¬ (QuorumOnChain ⟨ c , d ⟩ (MkRoundNumber (roundNumber r ∸ i))) }) (applyUpTo suc (n * K ∸ 2))
      → VoteInRound ⟨ c , d ⟩ r
```

There is not voting in round 0

```agda
--  round≡0→¬VoteInRound : ∀ {c : Chain} → {r : RoundNumber} → roundNumber r ≡ 0 → ¬ (VoteInRound c r)
--  round≡0→¬VoteInRound refl (Last r _) = (n≮n 0) r
--  round≡0→¬VoteInRound refl (CooldownIsOver _ r _ _) = (n≮n 0) r
```

```agda
  postulate
    VoteInRound? : ∀ (c : ChainState) → (r : RoundNumber) → Dec (VoteInRound c r)
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
  round-r-votes : ChainState → RoundNumber → ℕ
  round-r-votes ⟨ c , d ⟩ r = sum (map (countVotes ⟨ c , d ⟩ r) (blocks c))
```

```agda
  v-round : Slot → ⦃ _ : NonZero T ⦄ → RoundNumber
  v-round s = MkRoundNumber (s / T)
```

### Chain weight

```agda
  ∥_∥ : ChainState → ℕ
  ∥ ⟨ c , d ⟩ ∥ =
    let w = length (blocks c)
        s = slotNumber (tip c)
        r = s / T
        rs = filter (VoteInRound? ⟨ c , d ⟩) (map MkRoundNumber (upTo r))
    in w + (b * sum (map (round-r-votes ⟨ c , d ⟩) rs))
```

### Chain validity

<!--
```agda
open import Data.List.Relation.Unary.Unique.Propositional {A = Vote}
open import Data.List.Relation.Unary.AllPairs.Core _∻_ renaming (AllPairs to Equivocation)
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
         ⦃ _ : Hashable Vote ⦄
         ⦃ _ : Params ⦄
         where

  open Hashable ⦃...⦄

  data ValidChain : Chain → Set where

    Genesis :
      ValidChain
        record {
          blocks = block₀ ∷ [] ;
          votes = [] ;
          non-empty = NonEmpty.itsNonEmpty
        }

    Cons : ∀ {vs : List Vote} {c : Chain} {b : Block}
      → parentBlock b ≡ hash (tip c)
      → ValidChain c
      → Unique vs
      → ¬ (Equivocation vs)
      → All (λ { v → blockHash v ∈ (map hash (blocks c)) }) vs
--      → All (λ { v → slotNumber (blockHash v) < (roundNumber (votingRound v) * T) ∸ L }) vs
      → ValidChain
          record {
            blocks = b ∷ blocks c ;
            votes = map (λ { (MkVote r c m b s) → MkVote r c m (b) s }) vs ;
            non-empty = NonEmpty.itsNonEmpty
          }
```
#### Valid Chain state

```agda
  data ValidChainState : ChainState → Set where

    Constr : ∀ {c} {d}
      → ValidChain c
      → All (Dangling c) d
      → ValidChainState ⟨ c , d ⟩
```

#### Properties

For a valid chain we can show, that the blocks are non-empty without relying on the
property in `non-empty` of the `Chain`.

```agda
  instance
    itsNonEmptyChain : ∀ {c : Chain} → {ValidChain c} → NonEmpty (blocks c)
    itsNonEmptyChain {MkChain (x ∷ _) _ _} = NonEmpty.itsNonEmpty
```

The last block in a valid chain is always the genesis block.

```agda
  last-is-block₀ : ∀ {c : Chain}
    → (v : ValidChain c)
    → last (blocks c) ⦃ itsNonEmptyChain {c} {v} ⦄ ≡ block₀
  last-is-block₀ Genesis = refl
  last-is-block₀ (Cons {_} {c} {b} _ v _ _ _) =
    trans
      (drop-head (blocks c) b ⦃ itsNonEmptyChain {c} {v} ⦄)
      (last-is-block₀ {c} v)
    where
      drop-head : ∀ {A : Set} → (c : List A) → (b : A) → ⦃ _ : NonEmpty c ⦄ → last (b ∷ c) ≡ last c
      drop-head (_ ∷ _) _ ⦃ NonEmpty.itsNonEmpty ⦄ = refl
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
     listPrefix = foldl1Maybe (prefix []) (map (λ l -> reverse (blocks l)) chains)

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


```agda
private
  instance
    hashVote : Hashable Vote
    hashVote = record
      { hash = λ v →
                 (let record { bytes = s } = signature v
                  in record { bs = s })
      }

{-# COMPILE AGDA2HS hashVote #-}
```
