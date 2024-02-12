{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}

module Peras.RandomForks.Simulation (
  History (..),
  advance,
  initialHistory,
  run,
) where

import Control.Monad (replicateM_)
import Control.Monad.State (MonadState, gets, modify)
import Data.Bifunctor (bimap)
import Peras.RandomForks.Peer (nextSlot)
import Peras.RandomForks.Types (
  History (..),
  Message (Message, messageDestination),
  PeerState (pendingMessages),
  Peers (..),
  Protocol,
 )
import System.Random.Stateful (StatefulGen)

import qualified Data.Map.Strict as M

initialHistory ::
  Protocol ->
  Peers ->
  History
initialHistory protocol peers =
  History
    { protocol = protocol
    , peerHistory = M.singleton 0 peers
    }

run ::
  MonadState History m =>
  StatefulGen g m =>
  g ->
  Int ->
  m ()
run gen duration = replicateM_ duration $ advance gen

advance ::
  MonadState History m =>
  StatefulGen g m =>
  g ->
  m ()
advance gen =
  do
    protocol <- gets protocol
    (slot', Peers peers) <- gets $ M.findMax . peerHistory
    let slot = slot' + 1
    -- Advance one slot.
    (peers', messages) <-
      bimap M.fromList mconcat . unzip
        <$> sequence
          [ do
            (state', messages) <- nextSlot gen protocol slot name state
            pure ((name, state'), messages)
          | (name, state) <- M.toList peers -- FIXME: Rewrite as map.
          ]
    -- Deliver any new messages.
    let deliverMessage ps message@Message{messageDestination} =
          M.adjust (\state -> state{pendingMessages = pendingMessages state <> pure message}) messageDestination ps
        peers'' = foldl deliverMessage peers' messages
    modify $ \history -> history{peerHistory = M.insert slot (Peers peers'') (peerHistory history)}
