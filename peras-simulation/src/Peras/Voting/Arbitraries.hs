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
import Peras.Voting.Vote (MembershipInput (..), Signature, Vote (..), Voter (..), fromBytes, mkPartyId, newKESSigningKey, newVRFSigningKey, voterStake)
import Test.QuickCheck (Gen, arbitrary, choose, vectorOf)

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

gen32Bytes :: Gen ByteString
gen32Bytes = BS.pack <$> vectorOf 32 arbitrary

applyMutation :: Mutation -> Vote ByteString -> Vote ByteString
applyMutation (MutateSignature signature) vote =
  vote{signature}

mutationName :: Mutation -> String
mutationName = head . List.words . show

data Mutation = MutateSignature Signature
  deriving (Show)

genMutation :: Voter -> Vote ByteString -> Gen Mutation
genMutation MkVoter{kesSignKey, kesPeriod, vrfSignKey} _vote = do
  input <- fromBytes <$> gen32Bytes
  let vrf = VRF.evalCertified @_ @MembershipInput () input vrfSignKey
      sig = KES.signKES () kesPeriod vrf kesSignKey
  pure $ MutateSignature sig
