{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Peras.Chain where

import Data.ByteString (ByteString)
import Data.Set (Set)
import Data.Word (Word64)
import Peras.Block (Block, PartyId (..))
import Peras.Crypto (MembershipProof, Signature, isCommitteeMember, verify)

data Vote msg = Vote
  { roundNumber :: RoundNumber
  , creatorId :: PartyId
  , committeeMembershipProof :: MembershipProof
  , blockHash :: msg
  , signature :: Signature
  }
  deriving stock (Eq, Show, Ord)

toSignable :: Vote msg -> ByteString
toSignable = const ""

makeVote :: RoundNumber -> PartyId -> msg -> Vote msg
makeVote = undefined

newtype RoundNumber = RoundNumber Word64
  deriving newtype (Eq, Show, Ord)

-- | A vote is valid if the committee-membership proof and the signature are valid.
isValid :: Vote msg -> Bool
isValid vote@Vote{creatorId = PartyId{vkey}, committeeMembershipProof, signature} =
  isCommitteeMember vkey committeeMembershipProof
    && verify vkey signature (toSignable vote)

data Chain = Chain
  { blocks :: Set Block
  , tip :: Block
  -- ^ The tip of this chain, must be a member of `blocks`.
  , votes :: Set (Vote Block)
  -- ^ The set of "pending" votes, eg. which have not been included in a `Block`.
  }
  deriving stock (Eq, Show)

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
isValidChain :: Chain -> Bool
isValidChain _chain = undefined
