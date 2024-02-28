```agda
module Peras.Chain where
```

<!--
```agda
open import Data.Bool using (_∧_)
open import Data.Nat using (ℕ)

open import Peras.Crypto
open import Peras.Block
open import Peras.Params

open import Haskell.Prelude
```
-->

## Voting

### Round number

```agda
record RoundNumber : Set where
  field roundNumber : ℕ

open RoundNumber public
```

<!--
```agda
{-# COMPILE AGDA2HS RoundNumber deriving Eq #-}
```
-->

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
        votes : List (Vote Block)
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

### Chain validity

<!--
```agda
open import Data.List.Relation.Unary.Unique.Propositional {A = Vote Block}
open import Data.List.Relation.Unary.AllPairs.Core _∻_ renaming (AllPairs to Equivocation)
open import Relation.Nullary.Negation using (¬_)

open Block

open import Data.Nat using (_≤_; _∸_)
open import Data.List.Membership.Propositional using (_∈_)
```
-->
The validity of a chain is defined with respect of the Peras parameters.
```agda
open Params ⦃...⦄
```
A chain is valid iff:
  * the blocks (ignoring the vote hashes) form a valid Praos chain,
  * all votes:
    * are referenced by a unique block with a slot number $s$
      strictly larger than the slot number corresponding to the
      vote’s round number r (i.e., r*T < s),
    * point to a block on the chain at least L slots in the past
      (i.e., to a block with slot number s < r*T - L), and
  * it contains no vote equivocations (i.e., multiple votes by the
    same party for the same round).

TODO: expressing those conditions directly would be very expensive,
it's more efficient to enforce them whenever the chain is extended.

```agda
module _ {block₀ : Block}
         ⦃ _ : Hashable Block ⦄
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
      → parentBlock b ≡ tip c ♯
      → ValidChain c
      → Unique vs
      → ¬ (Equivocation vs)
      → All (λ { v → blockHash v ∈ blocks c }) vs
      → All (λ { v → slotNumber (blockHash v) ≤ slotNumber b ∸ L }) vs
      → ValidChain
          record {
            blocks = b ∷ blocks c ;
            votes = vs ;
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

open import Haskell.Prelude

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
