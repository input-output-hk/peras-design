module Peras.Prototype.BlockCreationSpec where

import Prelude hiding (round)

import Control.Concurrent.Class.MonadSTM (MonadSTM (readTVarIO), newTVarIO)
import Control.Monad (void)
import Control.Tracer (nullTracer)
import Data.Default (def)
import Peras.Arbitraries (generateWith)
import Peras.Block (Certificate (..))
import Peras.Crypto (hash)
import Peras.Prototype.BlockCreation (blockCreation)
import Peras.Prototype.Crypto (mkParty)
import Peras.Prototype.Diffusion (allPendingChains, defaultDiffuser, diffuseChain)
import Peras.Prototype.Types (PerasParams (..), PerasState (..), initialPerasState)
import Test.Hspec (Spec, it, shouldReturn)
import Test.QuickCheck (arbitrary)

spec :: Spec
spec = do
  let params = def
      roundNumber = 430
      slotNumber = fromIntegral $ fromIntegral roundNumber * perasU params
      someChain = arbitrary `generateWith` 42
      someCertificate = (arbitrary `generateWith` 42){round = roundNumber - 1, blockRef = hash (head someChain)}
      slotLeader = mkParty (arbitrary `generateWith` 42) [slotNumber] []
      steadyState =
        initialPerasState
          { chainPref = someChain
          , certPrime = someCertificate
          }

  it "Create a block if we are leader" $ do
    perasState <- newTVarIO steadyState
    diffuser <- newTVarIO $ defaultDiffuser 0
    void $
      blockCreation
        nullTracer
        params
        slotLeader
        perasState
        slotNumber
        mempty
        (diffuseChain diffuser)
    length . allPendingChains <$> readTVarIO diffuser `shouldReturn` 1
    length . chainPref <$> readTVarIO perasState `shouldReturn` length someChain + 1
