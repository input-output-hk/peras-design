{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.Abstract.Protocol.Voting where

import Control.Concurrent.Class.MonadSTM (MonadSTM (..))
import Control.Monad.Except (ExceptT (..), runExceptT)
import Control.Monad.Trans (lift)
import Data.Bits (FiniteBits, countLeadingZeros, countTrailingZeros, finiteBitSize, (.&.), (.<<.))
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Serialize (getWord64le, runGet)
import qualified Data.Set as Set
import Data.Word (Word64)
import Peras.Abstract.Protocol.Crypto (createMembershipProof, createSignedVote)
import Peras.Abstract.Protocol.Types (PerasState (..), Voting)
import Peras.Block (Party (..))
import Peras.Crypto (Hashable (..), VerificationKey (MkVerificationKey))
import Peras.Numbering (RoundNumber)
import Peras.Orphans ()

voting :: MonadSTM m => Voting m
voting params party perasState roundNumber preagreement diffuseVote = runExceptT $ do
  MkPerasState{..} <- lift $ readTVarIO perasState
  -- Invoke Preagreement(r) when in the first slot of r to get valid voting candidate B in slot rU + T .
  ExceptT (preagreement params party perasState roundNumber) >>= \case
    Nothing -> pure ()
    (Just (block, stake)) -> do
      -- If party P is (voting) committee member in a round r,
      if isCommitteeMember party roundNumber
        then pure ()
        else do
          proofM <- ExceptT $ createMembershipProof roundNumber (Set.singleton party)
          -- then create a vote v = (r, P, h, π, σ), where
          -- h is the hash of B,
          -- π is the slot-leadership proof,
          -- and σ is a signature on the rest of v.
          vote <- ExceptT $ createSignedVote party roundNumber (hash block) proofM stake
          -- Add v to V and diffuse it.
          lift $ atomically $ modifyTVar' perasState $ \s -> s{votes = vote `Set.insert` votes}
          ExceptT $ diffuseVote vote
          pure ()

isCommitteeMember :: Party -> RoundNumber -> Bool
isCommitteeMember MkParty{pkey = MkVerificationKey bytes} roundNumber =
  bytes `modulo` fromIntegral roundNumber == 0

modulo :: ByteString -> Word64 -> Word64
modulo bytes n =
  if isPowerOf2 n
    then modPowerOf2 bytes n
    else modNonPowerOf2 bytes n

modNonPowerOf2 :: ByteString -> Word64 -> Word64
modNonPowerOf2 bytes n =
  if i >= d * n
    then error $ "failed: i = " <> show i <> ", d = " <> show d <> ", n = " <> show n <> ", k = " <> show k
    else i `mod` n
 where
  k' = 1 .<<. k
  k = logBase2 (n * εFail)
  d = k' `div` n
  i = modPowerOf2 bytes k'

εFail :: Word64
εFail = 1 .<<. 40 -- roughly 1 in 10 billions

logBase2 :: FiniteBits b => b -> Int
logBase2 x = finiteBitSize x - 1 - countLeadingZeros x

modPowerOf2 :: ByteString -> Word64 -> Word64
modPowerOf2 bytes n =
  let r = fromBytesLE bytes
   in (n - 1) .&. r

fromBytesLE :: ByteString -> Word64
fromBytesLE = either error id . runGet getWord64le . BS.take 8

isPowerOf2 :: Word64 -> Bool
isPowerOf2 n =
  countLeadingZeros n + countTrailingZeros n == 63
