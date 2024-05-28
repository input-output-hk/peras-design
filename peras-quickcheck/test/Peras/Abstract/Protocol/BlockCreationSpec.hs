module Peras.Abstract.Protocol.BlockCreationSpec where

import Prelude hiding (round)

import Control.Concurrent.Class.MonadSTM (MonadSTM (readTVarIO), newTVarIO)
import Control.Monad (void)
import Peras.Abstract.Protocol.BlockCreation (blockCreation)
import Peras.Abstract.Protocol.Crypto (mkParty)
import Peras.Abstract.Protocol.Diffusion (Diffuser (pendingChains), defaultDiffuser, diffuseChain)
import Peras.Abstract.Protocol.Types (PerasParams (..), PerasState (..), defaultParams, initialPerasState)
import Peras.Arbitraries (generateWith)
import Peras.Block (Certificate (..))
import Peras.Crypto (hash)
import Test.Hspec (Spec, it, shouldReturn)
import Test.QuickCheck (arbitrary)

import qualified Data.Set as Set (size)

spec :: Spec
spec = do
  let params = defaultParams
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
    diffuser <- newTVarIO defaultDiffuser
    void $
      blockCreation
        params
        slotLeader
        perasState
        slotNumber
        mempty
        (diffuseChain diffuser)
    (Set.size . pendingChains <$> readTVarIO diffuser) `shouldReturn` 1
    (length . chainPref <$> readTVarIO perasState) `shouldReturn` (length someChain + 1)
