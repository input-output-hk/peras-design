{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Peras.IOSim.Network (
  createNetwork,
  emptyTopology,
  randomTopology,
  connectNode,
  getDelay,
  runNetwork,
  stepNetwork,
) where

import Control.Applicative ((<|>))
import Control.Lens ((&), (.~), (^.))
import Control.Monad.Class.MonadTime (MonadTime (..), UTCTime, addUTCTime, diffUTCTime)
import Control.Monad.Class.MonadTimer (MonadDelay (..))
import Control.Monad.Random (MonadRandom, getRandomR)
import Control.Tracer (Tracer, traceWith)
import Data.Foldable (foldrM)
import Data.List (delete)
import Data.Maybe (fromJust, fromMaybe, isNothing)
import Data.Ratio ((%))
import Peras.Event (CpuTime, Event (Drop))
import Peras.IOSim.Experiment (experimentFactory, noVeto)
import Peras.IOSim.Message.Types (InEnvelope (..), OutEnvelope (..), mkUniqueId)
import Peras.IOSim.Network.Types (
  Delay,
  NetworkState,
  NodeLink (NodeLink, latency),
  Topology (..),
  currentStates,
  lastSlot,
  lastTime,
  networkDelay,
  networkStake,
  networkVeto,
  pending,
  reliableLink,
 )
import Peras.IOSim.Node (makeContext, observeNode)
import Peras.IOSim.Node.Types (NodeContext (NodeContext, clock, slot), NodeResult (outputs), PerasNode (..))
import Peras.IOSim.Nodes (SomeNode)
import Peras.IOSim.Protocol.Types (Protocol)
import Peras.IOSim.Simulate.Types (Parameters (..))
import Peras.IOSim.Types (simulationStart)
import Peras.Message (Message (..), NodeId (..))
import Peras.Numbering (SlotNumber)
import System.IO (hPutStr, stderr)
import System.IO.Unsafe (unsafePerformIO)
import System.Random (randomRIO)

import qualified Data.Map.Strict as M
import qualified Data.PQueue.Min as PQ

{-# NOINLINE showProgress #-}
showProgress :: Bool -> SlotNumber -> UTCTime -> Int -> a -> a
showProgress True _slot time size x =
  unsafePerformIO $
    randomRIO (0 :: Int, 99)
      >>= \case
        0 -> do
          hPutStr stderr $
            "\r"
              <> take 15 (show (time `diffUTCTime` simulationStart) <> replicate 15 ' ')
              <> "\t"
              <> show size
              <> " pending"
              <> replicate 5 ' '
          pure x
        _ -> pure x
showProgress False _ _ _ x = x

emptyTopology ::
  [NodeId] ->
  Topology
emptyTopology = Topology . M.fromList . fmap (,mempty)

randomTopology ::
  MonadRandom m =>
  Parameters ->
  m Topology
randomTopology Parameters{..} =
  let nodeIds = MkNodeId . ("N" <>) . show <$> [1 .. peerCount]
      choose 0 _ = pure mempty
      choose n js =
        do
          j <- (js !!) <$> getRandomR (0, length js - 1)
          (j :) <$> choose (n - 1) (j `delete` js)
      randomConnects i topology =
        foldr (connectNode messageLatency (nodeIds !! i) . (nodeIds !!)) topology
          <$> choose downstreamCount (i `delete` [0 .. peerCount - 1])
   in foldrM randomConnects (emptyTopology nodeIds) [0 .. peerCount - 1]

connectNode ::
  Delay ->
  NodeId ->
  NodeId ->
  Topology ->
  Topology
connectNode messageLatency upstream downstream =
  Topology . M.insertWith (<>) upstream (M.singleton downstream (reliableLink messageLatency)) . connections

getDelay ::
  Topology ->
  NodeId ->
  NodeId ->
  Maybe CpuTime
getDelay Topology{connections} from to =
  messageDelay <$> forward <|> messageDelay <$> backward
 where
  messageDelay NodeLink{latency} = fromRational $ fromIntegral latency % 1_000_000
  forward = M.lookup from connections >>= M.lookup to
  backward = M.lookup to connections >>= M.lookup from

createNetwork ::
  Parameters ->
  Topology ->
  M.Map NodeId SomeNode ->
  NetworkState ->
  NetworkState
createNetwork Parameters{endSlot, experiment, totalStake} topology initialStates initialNetwork =
  let controller = MkNodeId "controller"
      delay source destination =
        if source == controller
          then Just 0
          else getDelay topology source destination
      makeNextSlot destination slot =
        OutEnvelope
          { source = controller
          , destination = destination
          , outId = mkUniqueId (controller, destination, slot)
          , outMessage = NextSlot slot
          , outTime = fromIntegral slot `addUTCTime` simulationStart
          , outBytes = 0
          }
      initialMessages = PQ.fromList [makeNextSlot destination slot | destination <- M.keys initialStates, slot <- [0 .. endSlot]]
   in initialNetwork
        & currentStates .~ initialStates
        & networkStake .~ fromMaybe (sum $ getStake <$> initialStates) totalStake
        & networkVeto .~ maybe noVeto experimentFactory experiment
        & networkDelay .~ delay
        & pending .~ initialMessages

stepNetwork ::
  forall m.
  MonadDelay m =>
  MonadTime m =>
  Bool ->
  Tracer m Event ->
  Protocol ->
  NetworkState ->
  m NetworkState
stepNetwork verbose tracer protocol =
  let go network =
        case PQ.minView (network ^. pending) of
          Nothing ->
            do
              let stop' state = stop state =<< makeContext tracer protocol (network ^. networkStake) (getNodeId state)
              states' <- mapM stop' $ network ^. currentStates
              pure $ network & currentStates .~ states'
          Just (Idle, _) -> go network
          Just (outEnvelope@OutEnvelope{..}, pending') ->
            do
              now <- getCurrentTime
              threadDelay . floor . (* 1_000_000) . toRational $ outTime `diffUTCTime` now
              context@NodeContext{slot, clock} <- makeContext tracer protocol (network ^. networkStake) destination
              let endOfSlot (Just OutEnvelope{outMessage = NextSlot slot'}) = slot /= slot'
                  endOfSlot _ = False
                  delay = (network ^. networkDelay) source destination
              network' <-
                showProgress verbose slot clock (PQ.size pending') $
                  if (network ^. networkVeto) outEnvelope slot || isNothing delay -- FIXME: Handle link reliability here.
                    then do
                      traceWith tracer $ Drop outId clock source destination outMessage outBytes
                      pure $
                        network
                          & pending .~ pending'
                          -- FIXME: Remove the following because they are redundant with the new observability.
                          & lastSlot .~ slot
                          & lastTime .~ clock
                    else do
                      let states = network ^. currentStates
                          node = states M.! destination
                          inEnvelope =
                            InEnvelope
                              { origin = source
                              , inId = outId
                              , inMessage = outMessage
                              , inTime = fromJust delay `addUTCTime` outTime
                              , inBytes = outBytes
                              }
                      (result, node') <- handleMessage node context inEnvelope
                      observeNode (traceWith tracer) destination slot clock inEnvelope result
                      pure $
                        network
                          & currentStates .~ M.insert destination node' states
                          & pending .~ foldr PQ.insert pending' (outputs result)
                          -- FIXME: Remove the following because they are redundant with the new observability.
                          & lastSlot .~ slot
                          & lastTime .~ clock
              if endOfSlot . PQ.getMin $ network' ^. pending
                then pure network'
                else go network'
   in go

runNetwork ::
  forall m.
  MonadDelay m =>
  MonadTime m =>
  Bool ->
  Tracer m Event ->
  Protocol ->
  NetworkState ->
  m NetworkState
runNetwork verbose tracer protocol network =
  do
    network' <- stepNetwork verbose tracer protocol network
    if PQ.null $ network' ^. pending
      then pure network'
      else runNetwork verbose tracer protocol network'
