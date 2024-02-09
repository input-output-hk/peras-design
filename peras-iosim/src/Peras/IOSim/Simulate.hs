{-# LANGUAGE OverloadedStrings #-}

module Peras.IOSim.Simulate where

import Control.Monad.Class.MonadSay (MonadSay(say))
import Control.Monad.Class.MonadTime (MonadTime(getCurrentTime))
import Control.Monad.IOSim (ppTrace, runSimTrace)
import Peras.IOSim.Network (emptyTopology, connectNode, createNetwork, runNetwork)
import Peras.IOSim.Node (initializeNodes)

example :: IO ()
example =
  let
    nodeId1 = "Party 1"
    nodeId2 = "Party 2"
    topology =
      connectNode nodeId1 nodeId2
        $ connectNode nodeId2 nodeId1
          emptyTopology 
    result =
      runSimTrace
        $ do
          now <- getCurrentTime
          let states = initializeNodes now topology
          say "Hello"
          network <- createNetwork topology
          runNetwork states network 100
  in
    mapM_ putStrLn . lines
      $ ppTrace result
