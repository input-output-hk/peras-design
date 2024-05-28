{-# LANGUAGE NamedFieldPuns #-}

module Peras.Abstract.Protocol.VotingSpec where

import Control.Concurrent.Class.MonadSTM (MonadSTM (readTVarIO), newTVarIO)
import Control.Monad (void)
import Control.Tracer (nullTracer)
import qualified Data.Set as Set
import Peras.Abstract.Protocol.Crypto (mkParty)
import Peras.Abstract.Protocol.Diffusion (defaultDiffuser, diffuseVote, pendingVotes)
import Peras.Abstract.Protocol.Types (PerasParams (..), PerasState (..), defaultParams, initialPerasState)
import Peras.Abstract.Protocol.Voting (voting)
import Peras.Arbitraries (generateWith)
import Peras.Block (Block (..), Certificate (..))
import Peras.Crypto (hash)
import Test.Hspec (Spec, describe, it, shouldReturn)
import Test.QuickCheck (arbitrary)
import Prelude hiding (round)

spec :: Spec
spec = do
  let params = defaultParams
      MkPerasParams{perasR} = params
      roundNumber = 430
      someChain = arbitrary `generateWith` 42
      someCertificate = (arbitrary `generateWith` 42){round = roundNumber - 1, blockRef = hash (head someChain)}
      someBlock = (arbitrary `generateWith` 12){parentBlock = blockRef someCertificate}
      preagreement _ _ _ _ = pure $ Right $ Just (someBlock, 1)
      committeeMember = mkParty (arbitrary `generateWith` 42) [] [roundNumber]
      nonCommitteeMember = mkParty (arbitrary `generateWith` 42) [] []
      steadyState =
        initialPerasState
          { chainPref = someChain
          , certPrime = someCertificate
          }

  it "votes on preagreement's block given party is committee member" $ do
    perasState <- newTVarIO steadyState
    diffuser <- newTVarIO defaultDiffuser

    void $
      voting
        nullTracer
        params
        committeeMember
        perasState
        roundNumber
        preagreement
        (diffuseVote diffuser)

    Set.size . pendingVotes <$> readTVarIO diffuser `shouldReturn` 1

  it "does not vote given party is not committee member" $ do
    perasState <- newTVarIO steadyState
    diffuser <- newTVarIO defaultDiffuser

    void $
      voting
        nullTracer
        params
        nonCommitteeMember
        perasState
        roundNumber
        preagreement
        (diffuseVote diffuser)

    pendingVotes <$> readTVarIO diffuser `shouldReturn` mempty

  describe "VR1-A" $
    it "does not vote if last seen certificate is older than previous round" $ do
      let certPrime = someCertificate{round = roundNumber - 2}
          lastSeenCertificateOlderThanPreviousRound = initialPerasState{certPrime}
      perasState <- newTVarIO lastSeenCertificateOlderThanPreviousRound
      diffuser <- newTVarIO defaultDiffuser

      void $
        voting
          nullTracer
          params
          committeeMember
          perasState
          roundNumber
          preagreement
          (diffuseVote diffuser)
      --      `shouldReturn` Left NoVoting

      pendingVotes <$> readTVarIO diffuser `shouldReturn` mempty

  describe "VR1-B" $
    it "does not vote if block does not extend immediately last seen certificate" $ do
      let blockOnFork = someBlock{parentBlock = arbitrary `generateWith` 41}
          preagreementSelectsFork _ _ _ _ = pure $ Right $ Just (blockOnFork, 1)
      perasState <- newTVarIO steadyState
      diffuser <- newTVarIO defaultDiffuser

      void $
        voting
          nullTracer
          params
          committeeMember
          perasState
          roundNumber
          preagreementSelectsFork
          (diffuseVote diffuser)
      --     `shouldReturn` Left NoVoting

      pendingVotes <$> readTVarIO diffuser `shouldReturn` mempty

  describe "VR2-A" $
    it "votes on preagreement's block given last seen certificate is older than cooldown period" $ do
      let cooldownState = steadyState{certPrime = someCertificate{round = roundNumber - fromInteger perasR}, certStar = someCertificate{round = 430 - 2 * 100}}
      perasState <- newTVarIO cooldownState
      diffuser <- newTVarIO defaultDiffuser

      void $
        voting
          nullTracer
          params
          committeeMember
          perasState
          roundNumber
          preagreement
          (diffuseVote diffuser)

      Set.size . pendingVotes <$> readTVarIO diffuser `shouldReturn` 1
  describe "VR2-B" $
    it "Cooldown periods have ended." $ do
      let cooldownState =
            steadyState
              { certPrime = someCertificate{round = roundNumber - fromInteger perasR}
              , certStar = someCertificate{round = 430 - 2 * 100}
              }
      perasState <- newTVarIO cooldownState
      diffuser <- newTVarIO defaultDiffuser

      void $
        voting
          nullTracer
          params
          committeeMember
          perasState
          roundNumber
          preagreement
          (diffuseVote diffuser)

      Set.size . pendingVotes <$> readTVarIO diffuser `shouldReturn` 1
