{-# LANGUAGE NamedFieldPuns #-}

module Peras.Abstract.Protocol.VotingSpec where

import Control.Concurrent.Class.MonadSTM (MonadSTM (readTVarIO), newTVarIO)
import Data.Either (isRight)
import qualified Data.Set as Set
import Peras.Abstract.Protocol.Diffusion (defaultDiffuser, diffuseVote, pendingVotes)
import Peras.Abstract.Protocol.Types (NoVotingReason (..), PerasError (..), PerasState (..), defaultParams, initialPerasState)
import Peras.Abstract.Protocol.Voting (voting)
import Peras.Arbitraries (generateWith)
import Peras.Block (Certificate (..), Party (MkParty))
import Test.Hspec (Spec, it, shouldReturn, shouldSatisfy)
import Test.QuickCheck (arbitrary)
import Prelude hiding (round)

spec :: Spec
spec = do
  let params = defaultParams
      roundNumber = 43
      someCertificate = arbitrary `generateWith` 42
      preagreement _ _ _ _ = pure $ Right $ Just (arbitrary `generateWith` 12, 1)
      committeeMember = MkParty (fromIntegral roundNumber) (arbitrary `generateWith` 42)
      nonCommitteeMember = MkParty (fromIntegral roundNumber + 1) (arbitrary `generateWith` 42)
      steadyState = initialPerasState{certPrime = someCertificate{round = roundNumber - 1}}

  it "votes on preagreement's block given party is committee member" $ do
    perasState <- newTVarIO steadyState
    diffuser <- newTVarIO defaultDiffuser

    voting
      params
      committeeMember
      perasState
      roundNumber
      preagreement
      (diffuseVote diffuser)
      >>= (`shouldSatisfy` isRight)

    (Set.size . pendingVotes <$> readTVarIO diffuser) `shouldReturn` 1

  it "does not vote given party is not committee member" $ do
    perasState <- newTVarIO initialPerasState
    diffuser <- newTVarIO defaultDiffuser

    voting
      params
      nonCommitteeMember
      perasState
      roundNumber
      preagreement
      (diffuseVote diffuser)
      >>= (`shouldSatisfy` isRight)

    (pendingVotes <$> readTVarIO diffuser) `shouldReturn` mempty

  it "does not vote if last seen certificate is older than previous round" $ do
    let certPrime = someCertificate{round = roundNumber - 2}
        lastSeenCertificateOlderThanPreviousRound = initialPerasState{certPrime}
    perasState <- newTVarIO lastSeenCertificateOlderThanPreviousRound
    diffuser <- newTVarIO defaultDiffuser

    voting
      params
      committeeMember
      perasState
      roundNumber
      preagreement
      (diffuseVote diffuser)
      `shouldReturn` Left (NoVoting $ LastSeenCertNotFromPreviousRound certPrime roundNumber)

    (pendingVotes <$> readTVarIO diffuser) `shouldReturn` mempty
