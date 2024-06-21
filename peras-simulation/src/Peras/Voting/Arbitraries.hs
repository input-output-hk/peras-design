{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Peras.Voting.Arbitraries where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Peras.Voting.Vote (Voter (..), mkPartyId, newKESSigningKey, newVRFSigningKey, voterStake)
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
  pure $ MkVoter{voterId, voterStake, vrfSignKey, vrfVerKey, kesPeriod, kesSignKey}

gen32Bytes :: Gen ByteString
gen32Bytes = BS.pack <$> vectorOf 32 arbitrary
