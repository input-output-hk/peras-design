module Peras.Chain where

open import Agda.Builtin.Word
open import Data.Bool using (_∧_)
open import Data.Nat using (ℕ)
open import Level
open import Data.Tree.AVL.Sets renaming (⟨Set⟩ to set) hiding (foldr)
open import Relation.Binary using (StrictTotalOrder)

open import Peras.Crypto
open import Peras.Block hiding (ByteString; emptyBS)

open import Haskell.Prelude

record RoundNumber : Set where
  field roundNumber : ℕ

record Vote msg : Set where
  constructor vote
  field roundNumber              : RoundNumber
        creatorId                : PartyId
        committeeMembershipProof : MembershipProof
        blockHash                : msg
        signature                : Signature

postulate
  vblEq : Relation.Binary.Rel (Vote Block⋆) 0ℓ
  vblLt : Relation.Binary.Rel (Vote Block⋆) 0ℓ
  vblIs : Relation.Binary.IsStrictTotalOrder vblEq vblLt

VoteBlockO : StrictTotalOrder 0ℓ 0ℓ 0ℓ
VoteBlockO = record {
  Carrier            = Vote Block⋆ ;
  _≈_                = vblEq ;
  _<_                = vblLt ;
  isStrictTotalOrder = vblIs }

toSignable : ∀{msg} → Vote msg -> ByteString
toSignable _ = emptyBS -- const ""

postulate
  makeVote : ∀{msg} → RoundNumber -> PartyId -> msg -> Vote msg

-- | A vote is valid if the committee-membership proof and the signature are valid.

isValid : ∀{msg} → Vote msg -> Bool
isValid v@(vote _ (MkPartyId vkey) committeeMembershipProof _ signature) =
  isCommitteeMember vkey committeeMembershipProof
    ∧ verify vkey signature (toSignable v)

record Chain⋆ : Set where
  constructor MkChain
  field blocks : Blocks⋆
        tip : Block⋆ -- The tip of this chain, must be a member of `blocks`
        votes : set VoteBlockO -- The set of "pending" votes, eg. which have not been included in a `Block`.

data Chain t : Set where
  Genesis : Chain t
  Cons : Block t → Chain t → Chain t

open Chain public

{-# COMPILE AGDA2HS Chain deriving (Eq) #-}


-- | `foldl` does not exist in `Haskell.Prelude` so let's roll our own
-- but let's make it total.
foldl1Maybe : ∀ {a : Set} -> (a -> a -> a) -> List a -> Maybe a
foldl1Maybe f xs =
  foldl (λ m y -> Just (case m of λ where
                             Nothing -> y
                             (Just x)  -> f x y))
        Nothing xs

{-# COMPILE AGDA2HS foldl1Maybe #-}

{-
  Module arguments are translated as explicit foralls in by Agda2hs, check
  https://github.com/agda/agda2hs/blob/master/test/ScopedTypeVariables.agda
-}
module ChainOps {t : Set} ⦃ isEqt : Eq t ⦄ where

  -- | View of a `Chain` as a mere `List` of blocks.
  asList : (c : Chain t) -> List (Block t)
  asList Genesis = []
  asList (Cons x c) = x ∷ (asList c)

  {-# COMPILE AGDA2HS asList #-}

  -- | View of a `List` of blocks as a `Chain` anchored in `Genesis`.
  asChain : (blocks : List (Block t)) -> Chain t
  asChain [] = Genesis
  asChain (x ∷ bs) = Cons x (asChain bs)

  {-# COMPILE AGDA2HS asChain #-}

  prefix : List (Block t) -> List (Block t) -> List (Block t) -> List (Block t)
  prefix acc (x ∷ xs) (y ∷ ys) =
    if x == y
     then prefix (x ∷ acc) xs ys
     else reverse acc
  prefix acc _ _ = reverse acc

  {-# COMPILE AGDA2HS prefix #-}

  commonPrefix : List (Chain t) -> Chain t
  commonPrefix chains =
    case listPrefix of λ where
       Nothing -> Genesis
       (Just bs) -> asChain (reverse bs)
     where
       listPrefix : Maybe (List (Block t))
       listPrefix = foldl1Maybe (prefix []) (map (λ l -> reverse (asList l)) chains)

  {-# COMPILE AGDA2HS commonPrefix #-}

-- I wish I could prove that and translate it to a QC property in Haskell :)
-- commonPrefixEq : {t : Set } -> ⦃ eqt : Eq t ⦄ -> (c₁ c₂ : Chain t) -> (c₁ ≡ c₂) -> (commonPrefix (c₁ ∷ c₂ ∷ []) ≡ c₁)
-- commonPrefixEq = {!!}

-- Chain⋆ = Chain (set BlockO)

-- | Chain validity
--
-- A chain is valid iff:
-- * the blocks (ignoring the vote hashes) form a valid Praos chain,
-- * all votes:
--      * are referenced by a unique block with a slot number $s$
--        strictly larger than the slot number corresponding to the
--        vote’s round number r (i.e., r*T < s),
--      * point to a block on the chain at least L slots in the past
--        (i.e., to a block with slot number s < r*T - L), and
-- * it contains no vote equivocations (i.e., multiple votes by the
--   same party for the same round).
--
-- TODO: expressing those conditions directly would be very expensive,
-- it's more efficient to enforce them whenever the chain is extended.


postulate
  verifyLeadershipProof : Block⋆ → Bool

  properlyLinked : Chain⋆ → Bool
  decreasingSlots : Chain⋆ → Bool

{-
correctBlocks : Chain → Bool
correctBlocks (MkChain blocks _ _) =
  let bs = toList BlockO blocks
  in all verifyLeadershipProof bs
-}

data ValidChain : Chain⋆ → Set where

  -- FIXME: constructors

{-
postulate
  isValidChain : Chain⋆ -> Bool
-}
