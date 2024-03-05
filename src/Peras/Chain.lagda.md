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
open import Data.Nat.Properties using (n≮n; _≟_)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
open import Function.Base using (_∘_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary using (DecidableEquality)

open import Peras.Crypto
open import Peras.Block
open import Peras.Params

open import Haskell.Prelude hiding (length; trans; _<_; _>_; _∘_; sum; b; pred; filter; concat)
{-# FOREIGN AGDA2HS import Peras.Crypto (Hash (..), Hashable (..)) #-}
```
-->

## Voting

### Round number

```agda
record RoundNumber : Set where
  constructor MkRoundNumber
  field roundNumber : ℕ

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
record Vote msg : Set where
  constructor MkVote
  field votingRound              : RoundNumber
        creatorId                : PartyId
        committeeMembershipProof : MembershipProof
        blockHash                : msg
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
data _∻_ : Vote Block → Vote Block → Set where

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
        votes : List (Vote Hash)
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

#### Chain weight

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

  countDangling : List (Vote Hash) → RoundNumber → Block → ℕ
  countDangling vs r b = length
    (filter (λ {v → blockHash v ≟-Hash (hash b)})
    (filter (λ {v → votingRound v ≟-RoundNumber r}) vs))

  -- FIXME: Only include votes for round r
  countBlocks : List Block → RoundNumber → Block → ℕ
  countBlocks bs (MkRoundNumber r) b = sum
    (map (λ {x →
      (length
        (filter (λ {v → v ≟-Hash (hash b)})
        (includedVotes x)))})
     bs)

  countVotes : Chain → RoundNumber → Block → ℕ
  countVotes (MkChain bs vs _) r b =
    countBlocks bs r b + countDangling vs r b
```

### Quorum

```agda
  data SeenQuorum : Chain → RoundNumber → Set where

    Initial : ∀ {c} {r}
      → roundNumber r ≡ 0
      → SeenQuorum c r

    LaterRound : ∀ {c} {r} {b}
      → roundNumber r > 0
      → b ∈ blocks c
      → countVotes c r b ≥ τ
      → SeenQuorum c r
```

```agda
  postulate
    SeenQuorum? : ∀ (c : Chain) → (r : RoundNumber) → Dec (SeenQuorum c r)
```

```agda
  data VoteInRound : Chain → RoundNumber → Set where

    Last : ∀ {c r}
      → roundNumber r > 0
      → SeenQuorum c (MkRoundNumber (pred (roundNumber r)))
      → VoteInRound c r

    CooldownIsOver : ∀ {c r n}
      → n > 0
      → roundNumber r > 0
      → SeenQuorum c (MkRoundNumber (roundNumber r ∸ (n * K)))
      → All (λ { i → ¬ (SeenQuorum c (MkRoundNumber (roundNumber r ∸ i))) }) (applyUpTo suc (n * K ∸ 2))
      → VoteInRound c r
```

```agda
  round≡0→¬VoteInRound : ∀ {c : Chain} → {r : RoundNumber} → roundNumber r ≡ 0 → ¬ (VoteInRound c r)
  round≡0→¬VoteInRound refl (Last r _) = (n≮n 0) r
  round≡0→¬VoteInRound refl (CooldownIsOver _ r _ _) = (n≮n 0) r
```

```agda
  postulate
    VoteInRound? : ∀ (c : Chain) → (r : RoundNumber) → Dec (VoteInRound c r)
    -- VoteInRound? c r@(MkRoundNumber zero) = no λ x → let ¬p = round≡0→¬VoteInRound {c} {r} refl in ¬p x
    -- VoteInRound? c r@(MkRoundNumber (suc _)) with SeenQuorum? c (MkRoundNumber (pred (roundNumber r)))
    -- ... | yes p = yes (Last (s≤s z≤n) p)
    -- ... | no ¬p = {!!}
```

```agda
  round-r-votes : Chain → RoundNumber → ℕ
  round-r-votes c r = sum (map (countVotes c r) (blocks c))
```

### Chain weight

```agda
  ∥_∥ : Chain → ℕ
  ∥ c ∥ =
    let w = length (blocks c)
        s = slotNumber (tip c)
        r = s / T
        rs = filter (VoteInRound? c) (map MkRoundNumber (upTo r))
    in w + (b * sum (map (round-r-votes c) rs))
```

### Chain validity

<!--
```agda
open import Data.List.Relation.Unary.Unique.Propositional {A = Vote Block}
open import Data.List.Relation.Unary.AllPairs.Core _∻_ renaming (AllPairs to Equivocation)
open import Relation.Nullary.Negation using (¬_)

import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (trans)

open Block

open import Data.Nat using (_≤_; _<_; _∸_)
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

  data ValidChain : Chain → Set where

    Genesis :
      ValidChain
        record {
          blocks = block₀ ∷ [] ;
          votes = [] ;
          non-empty = NonEmpty.itsNonEmpty
        }

    Cons : ∀ {vs : List (Vote Block)} {c : Chain} {b : Block}
      → parentBlock b ≡ hash (tip c)
      → ValidChain c
      → Unique vs
      → ¬ (Equivocation vs)
      → All (λ { v → blockHash v ∈ blocks c }) vs
      → All (λ { v → slotNumber (blockHash v) < (roundNumber (votingRound v) * T) ∸ L }) vs
      → ValidChain
          record {
            blocks = b ∷ blocks c ;
            votes = map (λ { (MkVote r c m b s) → MkVote r c m (hash b) s }) vs ;
            non-empty = NonEmpty.itsNonEmpty
          }
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
  last-is-block₀ (Cons {_} {c} {b} _ v _ _ _ _) =
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
    hashVote : Hashable (Vote a)
    hashVote = record
      { hash = λ v →
                 (let record { bytes = s } = signature v
                  in record { bs = s })
      }

{-# COMPILE AGDA2HS hashVote #-}
```
