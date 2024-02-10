module Main (
  main
) where

import Peras.IOSim.Protocol.Types (Protocol(..))
import Peras.IOSim.Simulate (simulate)
import Peras.IOSim.Simulate.Types (Parameters(..))

main :: IO ()
main = simulate exampleParameters examplePraos

exampleParameters :: Parameters
exampleParameters =
  Parameters
  {
    randomSeed = 12345
  , peerCount = 30
  , downstreamCount = 5
  , maximumStake = 1000
  , endSlot = 100
  }

examplePraos :: Protocol
examplePraos =
  PseudoPraos
  {
    activeSlotCoefficient = 1 / 20
  }
