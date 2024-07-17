{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Peras.Voting.Arbitraries where

import qualified Cardano.Crypto.KES as KES
import qualified Cardano.Crypto.VRF as VRF
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.List as List
import Data.Maybe (fromJust)
import Peras.Voting.Vote (
  MembershipInput (..),
  Signature,
  Vote (..),
  Voter (..),
  VotingWeight (..),
  castVote,
  fromBytes,
  mkPartyId,
  newKESSigningKey,
  newVRFSigningKey,
  voterStake,
 )
import Test.QuickCheck (Gen, arbitrary, choose, oneof, vectorOf)

genVoters :: Int -> Gen [Voter]
genVoters n = vectorOf n genVoter

genVoter :: Gen Voter
genVoter = do
  voterId <- mkPartyId <$> gen32Bytes
  voterStake <- choose (1_000_000, 1_000_000_000) -- in ADA
  (vrfSignKey, vrfVerKey) <- newVRFSigningKey <$> gen32Bytes
  let kesPeriod = 0
  kesSignKey <- newKESSigningKey <$> gen32Bytes
  pure $
    MkVoter
      { voterId
      , voterStake
      , vrfSignKey
      , vrfVerKey
      , kesPeriod
      , kesSignKey
      , kesVerKey = KES.deriveVerKeyKES kesSignKey
      }

genOneVote :: Gen (Vote ByteString)
genOneVote = do
  block <- gen32Bytes
  input <- fromBytes <$> gen32Bytes
  voter <- head <$> genVoters 1
  let totalStake = 2 * voterStake voter
  let committeeSize = fromIntegral totalStake `div` 2
  pure $ fromJust $ castVote block totalStake input committeeSize 42 voter

gen32Bytes :: Gen ByteString
gen32Bytes = BS.pack <$> vectorOf 32 arbitrary

applyMutation :: Mutation -> Vote ByteString -> Vote ByteString
applyMutation (MutateSignature signature) vote =
  vote{signature}
applyMutation (MutateBlockHash blockHash) vote =
  vote{blockHash}
applyMutation (MutateWeight votingWeight) vote =
  vote{votingWeight}

mutationName :: Mutation -> String
mutationName = head . List.words . show

data Mutation
  = MutateSignature Signature
  | MutateBlockHash ByteString
  | MutateWeight VotingWeight
  deriving (Show)

genMutation :: Voter -> Vote ByteString -> Gen Mutation
genMutation MkVoter{kesSignKey, kesPeriod, vrfSignKey} _vote =
  oneof [mutateSig, mutateHash, mutateWeight]
 where
  mutateWeight = do
    weight <- VotingWeight <$> choose (1_000_000_000, 100_000_000_000)
    pure $ MutateWeight weight

  mutateSig = do
    input <- fromBytes <$> gen32Bytes
    let vrf = VRF.evalCertified @_ @MembershipInput () input vrfSignKey
        sig = KES.signKES () kesPeriod vrf kesSignKey
    pure $ MutateSignature sig

  mutateHash = do
    blockHash <- gen32Bytes
    pure $ MutateBlockHash blockHash
