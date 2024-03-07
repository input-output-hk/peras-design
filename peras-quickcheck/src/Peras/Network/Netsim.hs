{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeApplications #-}

module Peras.Network.Netsim where

import Control.Exception (finally)
import Control.Monad.Random (genWord64, mkStdGen, runRand)
import Control.Monad.Reader (ReaderT (..))
import Data.IORef (modifyIORef', readIORef)
import Peras.IOSim.Network (randomTopology)
import Peras.IOSim.Network.Types (Topology)
import Peras.Message (Message (NextSlot))
import Peras.NetworkModel (RunMonad (..), Simulator (..), parameters)
import Peras.Node.Netsim (marshall, runTest, unmarshall)
import Peras.Node.Netsim.Rust (RustNetwork (..))
import qualified Peras.Node.Netsim.Rust as Rust
import System.Random (StdGen)
import Test.QuickCheck (Property, Testable, ioProperty)
import Test.QuickCheck.Monadic (PropertyM, monadic)

runPropInNetSim :: Testable a => PropertyM (RunMonad IO) a -> Property
runPropInNetSim = monadic (ioProperty . runner)
 where
  runner :: RunMonad IO Property -> IO Property
  runner act =
    withSimulatedNetwork $ \netsim ->
      runMonad act `runReaderT` netsim

withSimulatedNetwork :: (Simulator IO -> IO Property) -> IO Property
withSimulatedNetwork k = do
  let (topology, gen') = runRand (randomTopology parameters) (mkStdGen 42)
  netsim <- startNetwork topology gen'
  runTest k netsim `finally` stop netsim

startNetwork :: Topology -> StdGen -> IO (Simulator IO)
startNetwork topology seed = do
  let randomSeed = fst $ genWord64 seed
  network <- Rust.startNetwork (marshall topology) (marshall $ parameters{randomSeed})
  pure $ mkSimulator network
 where
  mkSimulator network@RustNetwork{tick} =
    Simulator
      { step = do
          modifyIORef' tick (+ 1)
          slot <- fromIntegral <$> readIORef tick
          Rust.broadcast network (marshall $ NextSlot @() slot)
      , preferredChain = fmap unmarshall . Rust.preferredChain network
      , stop = Rust.stopNetwork network
      }
