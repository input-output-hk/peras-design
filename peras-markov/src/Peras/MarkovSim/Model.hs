{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Peras.MarkovSim.Model where

import Control.Arrow ((***))
import Control.Monad.Except (ExceptT (ExceptT), MonadError (throwError), runExceptT)
import Control.Monad.State (MonadState, MonadTrans, StateT (StateT), get, gets, lift, modify')
import Data.Bifunctor
import Data.Default (def)
import Data.Functor.Identity
import Peras.MarkovSim.Transition
import Peras.MarkovSim.Types
import Test.QuickCheck.StateModel (Any (Some), HasVariables (..), Realized, RunModel (perform, postcondition), StateModel (..))

import qualified Peras.Block as Prototype
import qualified Peras.Chain as Prototype
import qualified Peras.Conformance.Params as Prototype
import qualified Peras.Prototype.Node.Model as Prototype

newtype RunMonad m a = RunMonad {runMonad :: StateT (Peras, Chains) m a}
  deriving newtype (Functor, Applicative, Monad, MonadState (Peras, Chains))

instance MonadTrans RunMonad where
  lift = RunMonad . lift

type instance Realized (RunMonad m) () = ()
type instance Realized (RunMonad m) (Maybe Prototype.Chain) = (Maybe Prototype.Chain)
type instance Realized (RunMonad m) (Maybe Prototype.Vote) = (Maybe Prototype.Vote)

instance Monad m => RunModel Prototype.NodeModel (RunMonad m) where
  perform _model action _context =
    case action of
      Prototype.Initialize _party start params ->
        -- Synchronize the parameters and clock.
        runExceptT . modify' $ toPeras params *** (\chains -> chains{slot = fromIntegral start})
      Prototype.Tick ->
        -- Handle a new slot.
        runExceptT . modify' $
          second tick
      Prototype.Fetching _newChains _newVotes ->
        pure $ pure ()
      Prototype.BlockCreation _isLeader _payload ->
        pure $ pure Nothing
      Prototype.Voting _isMember ->
        pure $ pure Nothing
  postcondition (prior, posterior) action _env actual =
    case action of
      Prototype.Initialize _party _start _params ->
        -- There's little point in checking the values explicitly set in `perform`.
        pure True
      Prototype.Tick ->
        -- Check that the clocks match.
        lift . gets $ (fromIntegral (Prototype.clock posterior) ==) . slot . snd
      Prototype.Fetching _newChains _newVotes ->
        pure True -- FIXME
      Prototype.BlockCreation _isLeader _payload ->
        pure True -- FIXME
      Prototype.Voting _isMember ->
        pure True -- FIXME

type MarkovModel = (Peras, Chains)

project :: Prototype.NodeModel -> MarkovModel
project Prototype.MkNodeModel{..} =
  let
   in ( toPeras protocol def
      , MkChains
          { slot = fromIntegral clock
          , prefix = 0 -- FIXME: Address this later. It should be the last common block of the chains tied for highest weight.
          , honest =
              MkChain
                { weight = undefined -- Prototype.chainWeight
                , certPrime = undefined
                , certPrimeNext = undefined
                , certUltimate = undefined
                , certPenultimate = undefined
                , certAntepenultimate = undefined
                , certStar = undefined
                , certStarNext = undefined
                }
          , adversary = def
          }
      )

toPeras :: Prototype.PerasParams -> Peras -> Peras
toPeras Prototype.MkPerasParams{..} peras =
  peras
    { u = fromIntegral perasU
    , a = fromIntegral perasA
    , r = fromIntegral perasR
    , k = fromIntegral perasK
    , b = fromIntegral perasB
    , τ = fromIntegral perasτ
    , c = 3 * fromIntegral perasτ `div` 4
    }
