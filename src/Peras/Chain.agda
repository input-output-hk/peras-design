module Peras.Chain where
{-# FOREIGN AGDA2HS
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
#-} 

{-# FOREIGN AGDA2HS
import Data.ByteString (ByteString)
import qualified Data.Set as S (Set)
import Data.Word (Word64)
type SET = S.Set
#-}

--import Peras.Block (Block, PartyId (..))
--import Peras.Crypto (MembershipProof, Signature, isCommitteeMember, verify)

open import Agda.Builtin.Word
open import Data.Bool
open import Level

open import Peras.Crypto
open import Peras.Block

record RoundNumber : Set where
  field roundNumber : Word64
open RoundNumber public
{-# COMPILE AGDA2HS RoundNumber newtype deriving (Eq, Show, Ord) #-}
-- newtype strategy not supported

record Vote msg : Set where
  field roundNumber              : RoundNumber
        creatorId                : PartyId
        committeeMembershipProof : MembershipProof
        blockHash                : msg
        signature                : Signature
open Vote public        
{-# COMPILE AGDA2HS Vote deriving (Eq, Show, Ord) #-}
-- stock strategy not supported

toSignable : ∀{msg} → Vote msg -> ByteString
toSignable _ = emptyBS -- const ""
{-# COMPILE AGDA2HS toSignable #-}

postulate makeVote : ∀{msg} → RoundNumber -> PartyId -> msg -> Vote msg
{-# COMPILE AGDA2HS makeVote #-}

-- | A vote is valid if the committee-membership proof and the signature are valid.

isValid : ∀{msg} → Vote msg -> Bool
isValid (record {roundNumber = roundNumber; creatorId = record {vkey = vkey}; committeeMembershipProof = committeeMembershipProof; blockHash = blockHash; signature = signature}) =
  isCommitteeMember vkey committeeMembershipProof
    ∧ verify vkey signature (toSignable (record {roundNumber = roundNumber; creatorId = record {vkey = vkey}; committeeMembershipProof = committeeMembershipProof; blockHash = blockHash; signature = signature}))
-- as patterns not supported
{-# COMPILE AGDA2HS isValid #-}

record Chain : Set where
  field blocks : SET Block
        tip : Block
  -- ^ The tip of this chain, must be a member of `blocks`.
        votes : SET (Vote Block)
  -- ^ The set of "pending" votes, eg. which have not been included in
  --   a `Block`.
open Chain public
{-# COMPILE AGDA2HS Chain deriving (Eq, Show) #-}
-- deriving stock strategy not supportd

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

postulate isValidChain : Chain -> Bool
{-# COMPILE AGDA2HS isValidChain #-}
