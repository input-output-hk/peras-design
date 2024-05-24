{-# LANGUAGE NamedFieldPuns #-}

module Peras.Abstract.Protocol.NodeSpec where

import Prelude hiding (round)

import Control.Concurrent.Class.MonadSTM (MonadSTM (readTVarIO), newTVarIO)
import Control.Monad (void)
import Control.Monad.Except
import Control.Monad.State
import Peras.Abstract.Protocol.Crypto (mkParty)
import Peras.Abstract.Protocol.Diffusion (Diffuser (pendingChains), defaultDiffuser, diffuseChain)
import Peras.Abstract.Protocol.Node
import Peras.Abstract.Protocol.Types (PerasParams (..), PerasState (..), defaultParams, initialPerasState)
import Peras.Arbitraries (generateWith)
import Peras.Block (Certificate (..), Party (MkParty))
import Peras.Crypto (VerificationKey (MkVerificationKey), hash)
import Test.Hspec (Spec, it, shouldReturn)
import Test.QuickCheck (arbitrary)

import qualified Data.Serialize as Serialize (encode)
import qualified Data.Set as Set (size)

spec :: Spec
spec = do
  let params = defaultParams
      roundNumber = 430
      slotNumber = fromIntegral $ fromIntegral roundNumber * perasU params
      someChain = arbitrary `generateWith` 42
      someCertificate = (arbitrary `generateWith` 42){round = roundNumber - 1, blockRef = hash (head someChain)}
      --    payload = arbitrary `generateWith` 42
      boring = mkParty (arbitrary `generateWith` 42) [] []
      leaderOnly = mkParty (arbitrary `generateWith` 42) [slotNumber] []
      voterOnly = mkParty (arbitrary `generateWith` 42) [] [roundNumber]
      leaderAndVoter = mkParty (arbitrary `generateWith` 42) [slotNumber] [roundNumber]
      steadyState =
        initialPerasState
          { chainPref = someChain
          , certPrime = someCertificate
          }
  -- FIXME: Work in progress!
  {-
    it "Tick without slot leadership or committee membership" $ do
      nodeState@MkNodeState{stateVar} <- initialNodeState boring (slotNumber - 1)
  --  nodeState' <- execStateT (tick payload) $ nodeState
  -}
  pure ()
