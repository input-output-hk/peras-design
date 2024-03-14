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

## Chain

 * The tip of this chain is the head of `blocks`
 * The set of "pending" votes, eg. which have not been included in a `Block`.

TODO: consider an association list for the votes
```agda
record Chain : Set where
  constructor MkChain
  field blocks : List Block
--        votes : List Vote
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
tip (MkChain blks non-empty) = head blks ⦃ non-empty ⦄
```

<!--
```agda
{-# COMPILE AGDA2HS tip #-}
```
-->

### Chain prefix

```agda
data _⪯_ : Chain → Chain → Set where

  Prefix : ∀ {c₁ c₂ c₃ : Chain}
    → blocks c₁ ++ blocks c₃ ≡ blocks c₂
--    → votes c₁ ++ votes c₃ ≡ votes c₂
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
∣ MkChain bs _ ∣ = length bs
```

### Chain weight

The weight of a chain is defined with respect of the Peras parameters
```agda
open Params ⦃...⦄
```
The weight of a chain is computed wrt to a set of dangling votes
```agda
module _ ⦃ _ : Hashable Block ⦄
--         ⦃ _ : Hashable Vote ⦄
         ⦃ _ : Params ⦄
         where

  instance
    nonZero : NonZero T -- TODO: why is this needed..?
    nonZero = T-nonZero

  open Hashable ⦃...⦄
```
```agda
{-
  import Prelude.AssocList as A
  open A.Decidable _≟-Hash_

  referencedVote : Chain → Hash → M.Maybe Vote
  referencedVote c h =
    let vs = votes c
    in h ‼ zip (map hash vs) vs
-}
```
### Dangling vote

A C-dangling vote
  * votes for a block in C
  * is not already referenced by blocks in C
  * is not an equivocation of a vote referenced by blocks in C

```agda
{-
  data Dangling : Chain → Vote → Set where

    C-Dangling : ∀ {v} {b} {c} -- {r}
      → -- let s = r * T in
        b ∈ blocks c
      → blockHash v ≡ hash b
--      → slotNumber b ≥ (s ∸ Lₗ)
--      → slotNumber b ≤ (s ∸ Lₕ)
      → ¬ (Any (λ { x → (hash v) ∈ (includedVotes x) }) (blocks c))
      → All (λ { x → NoEquivocations
                          (catMaybes $ map (referencedVote c) (includedVotes x))
                  }) (blocks c)
      → Dangling c v
-}
```

```agda
--  DanglingVotes : Chain → List Vote → Set
--  DanglingVotes = All ∘ Dangling
```

### Chain state

```agda
  {-
  record ChainState : Set where
    constructor ⟨_,_⟩
    field chain : Chain
          certs : List Certificate

  open ChainState public
  -}
  
  postulate
    latestCertSeen : Chain → List Certificate → Certificate
    latestCertOnChain : Chain → List Certificate → Certificate
```

Counting votes for a block from votes
```agda
{-
  countVotes : List Vote → RoundNumber → Block → ℕ
  countVotes vs r b = length $
    filter (λ { v →
      (blockHash v ≟-Hash (hash b)) ×-dec
      (votingRound v ≟-RoundNumber r)
      })
    vs
-}
```
Counting votes for a block
```agda
--  weightOfBlock : ChainState → RoundNumber → Block → ℕ
--  weightOfBlock ⟨ MkChain bs vs _ , d , _ ⟩ r b = countVotes vs r b + countVotes d r b
```

### Quorum

The relation `QuorumOnChain` checks whether there is a round-r quorum with respect to
the votes on chain c and dangling votes for a block on chain c.

```agda
{-
  data QuorumOnChain : ChainState → RoundNumber → Set where

    Initial : ∀ {c} {r}
      → roundNumber r ≡ 0
      → QuorumOnChain c r

    LaterRound : ∀ {c} {d} {r} {b}
      → roundNumber r > 0
      → b ∈ blocks c
      → (p : DanglingVotes c d)
      → weightOfBlock ⟨ c , d , p ⟩ r b ≥ τ
      → QuorumOnChain ⟨ c , d , p ⟩ r
-}
```

```agda
{-
  postulate
    QuorumOnChain? : ∀ (c : ChainState) → (r : RoundNumber) → Dec (QuorumOnChain c r)
-}
```

In a cooldown period there is no voting.

```agda
  data Reference : Certificate → Chain → Set where

  postulate
    Reference? : ∀ (c : Chain) → (cert : Certificate) → Dec (Reference cert c)

  data VoteInRound : Chain → List Certificate → RoundNumber → Set where

    Regular : ∀ {c cs r} →
      let certₛ = latestCertSeen c cs
          rₛ = Certificate.roundNumber certₛ
      in
        rₛ + 1 ≥ r
      → Reference certₛ c
      → VoteInRound c cs (MkRoundNumber r) 

    AfterCooldown : ∀ {chain cs r c} →
      let certₛ = latestCertSeen chain cs
          rₛ = Certificate.roundNumber certₛ
      in
        c > 0
      → r ≥ R + rₛ
      → r ≡ (c * K) + rₛ
      → VoteInRound chain cs (MkRoundNumber r)
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
      ValidChain
        record {
          blocks = block₀ ∷ [] ;
          non-empty = NonEmpty.itsNonEmpty
        }

    Cons : ∀ {vs : List Vote} {c : Chain} {b : Block}
      → parentBlock b ≡ hash (tip c)
      → ValidChain c
      → ValidChain
          record {
            blocks = b ∷ blocks c ;
            non-empty = NonEmpty.itsNonEmpty
          }

```

#### Properties

For a valid chain we can show, that the blocks are non-empty without relying on the
property in `non-empty` of the `Chain`.

```agda
  instance
    itsNonEmptyChain : ∀ {c : Chain} → {ValidChain c} → NonEmpty (blocks c)
    itsNonEmptyChain {MkChain (x ∷ _) _ } = NonEmpty.itsNonEmpty
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
