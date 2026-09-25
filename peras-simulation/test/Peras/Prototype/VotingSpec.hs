{-# LANGUAGE NamedFieldPuns #-}

module Peras.Prototype.VotingSpec where

import Control.Concurrent.Class.MonadSTM (MonadSTM (readTVarIO), newTVarIO)
import Control.Monad (void)
import Control.Tracer (nullTracer)
import Data.Default (def)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Peras.Arbitraries (generateWith)
import Peras.Block (Block (..), Certificate (..))
import qualified Peras.Conformance.Model as Model
import Peras.Crypto (hash)
import Peras.Prototype.Crypto (mkParty)
import Peras.Prototype.Diffusion (allPendingVotes, defaultDiffuser, diffuseVote)
import Peras.Prototype.Types (PerasParams (..), PerasState (..), initialPerasState)
import Peras.Prototype.Voting (voting)
import Test.Hspec (Spec, describe, it, shouldBe, shouldReturn)
import Test.QuickCheck (arbitrary)
import Prelude hiding (round)

spec :: Spec
spec = do
  let params@MkPerasParams{perasR, perasU} =
        def
          { perasU = 20
          , perasA = 2160
          , perasR = 100
          , perasK = 100
          , perasL = 30
          , perasτ = 75
          , perasB = 100
          , perasΔ = 5
          }
      roundNumber = 430
      slotNumber = fromInteger $ fromIntegral roundNumber * perasU
      someChain = arbitrary `generateWith` 42
      someCertificate = (arbitrary `generateWith` 42){round = roundNumber - 1, blockRef = hash (head someChain)}
      someBlock = (arbitrary `generateWith` 12){parentBlock = blockRef someCertificate}
      selectBlock _ _ _ _ = pure $ Right $ Just (someBlock, 1)
      committeeMember = mkParty (arbitrary `generateWith` 42) [] [roundNumber]
      nonCommitteeMember = mkParty (arbitrary `generateWith` 42) [] []
      steadyState =
        initialPerasState
          { chainPref = someChain
          , certPrime = someCertificate
          , certs = Map.singleton someCertificate (fromInteger ((fromIntegral roundNumber - 1) * perasU))
          , chains = Set.singleton someChain
          }

      checkReceipt label receipt expected = it label $ do
        let received = maybe Map.empty (Map.singleton someCertificate) receipt
            model =
              Model.initialModelState
                { Model.clock = slotNumber
                , Model.protocol = params
                , Model.allSeenCerts = [someCertificate]
                , Model.certSeenSlots = Map.toList received
                }
            selectCertified _ _ _ _ = pure $ Right $ Just (head someChain, 1)
        Model.vr1A model `shouldBe` expected
        perasState <- newTVarIO steadyState{certs = received}
        diffuser <- newTVarIO $ defaultDiffuser 0
        result <- voting nullTracer params committeeMember perasState slotNumber selectCertified (diffuseVote diffuser)
        result `shouldBe` Right ()
        length . allPendingVotes <$> readTVarIO diffuser `shouldReturn` (if expected then 1 else 0)

      certRoundStart = fromInteger $ (fromIntegral roundNumber - 1) * perasU

  describe "VR1-A certificate receipt window" $ do
    checkReceipt "accepts receipt at the start of the certificate's round" (Just certRoundStart) True
    checkReceipt "accepts receipt exactly at the Delta deadline" (Just (certRoundStart + 5)) True
    checkReceipt "rejects receipt one slot after the Delta deadline" (Just (certRoundStart + 6)) False
    checkReceipt "rejects receipt in the voting round" (Just slotNumber) False
    checkReceipt "rejects receipt before the certificate's round" (Just (certRoundStart - 1)) False
    checkReceipt "rejects certificates without a receipt timestamp" Nothing False
    it "accepts the genesis certificate seen at slot zero" $
      Model.vr1A Model.initialModelState{Model.clock = 5} `shouldBe` True

  {- FIXME: Needs a better generator.
    it "votes on selectBlock's block given party is committee member" $ do
      perasState <- newTVarIO steadyState
      diffuser <- newTVarIO $ defaultDiffuser 0

      void $
        voting
          nullTracer
          params
          committeeMember
          perasState
          roundNumber
          selectBlock
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
        slotNumber
        selectBlock
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
        slotNumber
        selectBlock
        (diffuseVote diffuser)

    allPendingVotes <$> readTVarIO diffuser `shouldReturn` mempty

  describe "VR1-B" $ do
    it "does not vote if block does not extend last seen certificate" $ do
      let blockOnFork = someBlock{parentBlock = arbitrary `generateWith` 41}
          selectBlockSelectsFork _ _ _ _ = pure $ Right $ Just (blockOnFork, 1)
      perasState <- newTVarIO steadyState
      diffuser <- newTVarIO $ defaultDiffuser 0

      void $
        voting
          nullTracer
          params
          committeeMember
          perasState
          slotNumber
          selectBlockSelectsFork
          (diffuseVote diffuser)

      allPendingVotes <$> readTVarIO diffuser `shouldReturn` mempty

    it "does vote if block is same as the one from last seen certificate" $ do
      let certifiedBlock = head someChain
          selectBlockSelectsCertifiedBlock _ _ _ _ = pure $ Right $ Just (certifiedBlock, 1)
      perasState <- newTVarIO steadyState
      diffuser <- newTVarIO $ defaultDiffuser 0

      void $
        voting
          nullTracer
          params
          committeeMember
          perasState
          slotNumber
          selectBlockSelectsCertifiedBlock
          (diffuseVote diffuser)

      length . allPendingVotes <$> readTVarIO diffuser `shouldReturn` 1

    it "only vote at beginning of round" $ do
      let certifiedBlock = head someChain
          selectBlockSelectsCertifiedBlock _ _ _ _ = pure $ Right $ Just (certifiedBlock, 1)
      perasState <- newTVarIO steadyState
      diffuser <- newTVarIO $ defaultDiffuser 0

      void $
        voting
          nullTracer
          params
          committeeMember
          perasState
          (slotNumber + 1)
          selectBlockSelectsCertifiedBlock
          (diffuseVote diffuser)

      allPendingVotes <$> readTVarIO diffuser `shouldReturn` mempty

  it "VR2-A - votes on selectBlock's block given last seen certificate is older than cooldown period" $ do
    let cooldownState = steadyState{certPrime = someCertificate{round = roundNumber - fromInteger perasR}, certStar = someCertificate{round = 430 - 2 * 100}}
    perasState <- newTVarIO cooldownState
    diffuser <- newTVarIO $ defaultDiffuser 0

    void $
      voting
        nullTracer
        params
        committeeMember
        perasState
        slotNumber
        selectBlock
        (diffuseVote diffuser)

    length . allPendingVotes <$> readTVarIO diffuser `shouldReturn` 1

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
        slotNumber
        selectBlock
        (diffuseVote diffuser)

    length . allPendingVotes <$> readTVarIO diffuser `shouldReturn` 1
