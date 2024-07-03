{-# LANGUAGE NamedFieldPuns #-}

module Peras.Prototype.VotingSpec where

import Control.Concurrent.Class.MonadSTM (MonadSTM (readTVarIO), newTVarIO)
import Control.Monad (void)
import Control.Tracer (nullTracer)
import Data.Default (def)
import qualified Data.Set as Set
import Peras.Arbitraries (generateWith)
import Peras.Block (Block (..), Certificate (..))
import Peras.Crypto (hash)
import Peras.Prototype.Crypto (mkParty)
import Peras.Prototype.Diffusion (allPendingVotes, defaultDiffuser, diffuseVote)
import Peras.Prototype.Types (PerasParams (..), PerasState (..), initialPerasState)
import Peras.Prototype.Voting (voting)
import Test.Hspec (Spec, describe, it, shouldReturn)
import Test.QuickCheck (arbitrary)
import Prelude hiding (round)

spec :: Spec
spec = do
  let params@MkPerasParams{perasR} =
        def
          { perasU = 20
          , perasA = 2160
          , perasR = 100
          , perasK = 100
          , perasL = 30
          , perasτ = 75
          , perasB = 100
          , perasT = 0
          , perasΔ = 5
          }
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
          , chains = Set.singleton someChain
          }

  {- FIXME: Needs a better generator.
    it "votes on preagreement's block given party is committee member" $ do
      perasState <- newTVarIO steadyState
      diffuser <- newTVarIO $ defaultDiffuser 0

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
  -}

  it "does not vote given party is not committee member" $ do
    perasState <- newTVarIO steadyState
    diffuser <- newTVarIO $ defaultDiffuser 0

    void $
      voting
        nullTracer
        params
        nonCommitteeMember
        perasState
        roundNumber
        preagreement
        (diffuseVote diffuser)

    allPendingVotes <$> readTVarIO diffuser `shouldReturn` mempty

  it "VR1-A - does not vote if last seen certificate is older than previous round" $ do
    let certPrime = someCertificate{round = roundNumber - 2}
        lastSeenCertificateOlderThanPreviousRound = initialPerasState{certPrime}
    perasState <- newTVarIO lastSeenCertificateOlderThanPreviousRound
    diffuser <- newTVarIO $ defaultDiffuser 0

    void $
      voting
        nullTracer
        params
        committeeMember
        perasState
        roundNumber
        preagreement
        (diffuseVote diffuser)

    allPendingVotes <$> readTVarIO diffuser `shouldReturn` mempty

  describe "VR1-B" $ do
    it "does not vote if block does not extend last seen certificate" $ do
      let blockOnFork = someBlock{parentBlock = arbitrary `generateWith` 41}
          preagreementSelectsFork _ _ _ _ = pure $ Right $ Just (blockOnFork, 1)
      perasState <- newTVarIO steadyState
      diffuser <- newTVarIO $ defaultDiffuser 0

      void $
        voting
          nullTracer
          params
          committeeMember
          perasState
          roundNumber
          preagreementSelectsFork
          (diffuseVote diffuser)

      allPendingVotes <$> readTVarIO diffuser `shouldReturn` mempty

    it "does vote if block is same as the one from last seen certificate" $ do
      let certifiedBlock = head someChain
          preagreementSelectsCertifiedBlock _ _ _ _ = pure $ Right $ Just (certifiedBlock, 1)
      perasState <- newTVarIO steadyState
      diffuser <- newTVarIO $ defaultDiffuser 0

      void $
        voting
          nullTracer
          params
          committeeMember
          perasState
          roundNumber
          preagreementSelectsCertifiedBlock
          (diffuseVote diffuser)

      Set.size . allPendingVotes <$> readTVarIO diffuser `shouldReturn` 1

  it "VR2-A - votes on preagreement's block given last seen certificate is older than cooldown period" $ do
    let cooldownState = steadyState{certPrime = someCertificate{round = roundNumber - fromInteger perasR}, certStar = someCertificate{round = 430 - 2 * 100}}
    perasState <- newTVarIO cooldownState
    diffuser <- newTVarIO $ defaultDiffuser 0

    void $
      voting
        nullTracer
        params
        committeeMember
        perasState
        roundNumber
        preagreement
        (diffuseVote diffuser)

    Set.size . allPendingVotes <$> readTVarIO diffuser `shouldReturn` 1

  it "VR2-B - Cooldown periods have ended." $ do
    let cooldownState =
          steadyState
            { certPrime = someCertificate{round = roundNumber - fromInteger perasR}
            , certStar = someCertificate{round = 430 - 2 * 100}
            }
    perasState <- newTVarIO cooldownState
    diffuser <- newTVarIO $ defaultDiffuser 0

    void $
      voting
        nullTracer
        params
        committeeMember
        perasState
        roundNumber
        preagreement
        (diffuseVote diffuser)

    Set.size . allPendingVotes <$> readTVarIO diffuser `shouldReturn` 1
