{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Peras.MarkovSim.Model {-# DEPRECATED "Work in progress." #-} where

import Control.Arrow ((***))
import Control.Monad.Except (runExceptT)
import Control.Monad.State (MonadState, MonadTrans, StateT (StateT), get, gets, lift, modify', put)
import Data.Bifunctor (Bifunctor (second))
import Data.Default (def)
import Peras.MarkovSim.Transition (tick, voting)
import Peras.MarkovSim.Types (Chain (..), Chains (..), Peras (..), pureProbabilities)
import Test.QuickCheck.StateModel (Realized, RunModel (perform, postcondition))

import qualified Data.Map.Strict as Map
import qualified Peras.Block as Prototype
import qualified Peras.Chain as Prototype
import qualified Peras.Conformance.Params as Prototype
import qualified Peras.Numbering as Prototype
import qualified Peras.Prototype.Fetching as Prototype
import qualified Peras.Prototype.Node.Model as Prototype
import qualified Peras.Prototype.Types as Prototype

newtype RunMonad m a = RunMonad {runMonad :: StateT (Peras, Chains) m a}
  deriving newtype (Functor, Applicative, Monad, MonadState (Peras, Chains))

instance MonadTrans RunMonad where
  lift = RunMonad . lift

type instance Realized (RunMonad m) () = ()
type instance Realized (RunMonad m) (Maybe Prototype.Chain) = (Maybe Int)
type instance Realized (RunMonad m) (Maybe Prototype.Vote) = (Maybe Int)

instance Monad m => RunModel Prototype.NodeModel (RunMonad m) where
  perform model action _context =
    case action of
      Prototype.Initialize _party start params ->
        -- Synchronize the parameters and clock.
        runExceptT . modify' $
          toPeras params *** (\chains -> chains{slot = fromIntegral start})
      Prototype.Tick ->
        -- Handle a new slot.
        runExceptT . modify' $
          second tick
      Prototype.Fetching newChains newVotes ->
        -- FIXME: For now, we set the run state based on the model state.
        runExceptT . put . project . snd $ Prototype.fetchingModeled newChains newVotes model
      Prototype.BlockCreation _isLeader _payload ->
        pure $ pure Nothing
      Prototype.Voting isMember ->
        let
          Prototype.MkNodeModel{..} = model
          r = Prototype.slotToRound protocol clock
          next = snd $ Prototype.fetchingModeled mempty mempty model
         in
          if Prototype.round (Prototype.certPrime $ Prototype.state next) == r
            then -- There was a quorum.
            runExceptT $ do
              let prob = pureProbabilities False isMember
              (peras, chains) <- get
              case voting peras prob chains of
                [(chains', _)] -> do
                  modify' . second $ const chains'
                  pure . certPrimeNext $ honest chains'
                _ -> error "Markov projection failed."
            else -- There wasn't a quorum.
              pure $ pure Nothing
  postcondition (_prior, posterior) action _env _actual =
    case action of
      Prototype.Initialize _party _start _params ->
        -- There's little point in checking the values explicitly set in `perform`.
        pure True
      Prototype.Tick ->
        -- Check that the clocks match.
        lift . gets $ (fromIntegral (Prototype.clock posterior) ==) . slot . snd
      Prototype.Fetching _newChains _newVotes ->
        (project posterior ==) <$> lift get
      Prototype.BlockCreation _isLeader _payload ->
        -- FIXME: Not implemented
        pure True
      Prototype.Voting _isMember ->
        (project posterior ==) <$> lift get

type MarkovModel = (Peras, Chains)

project :: Prototype.NodeModel -> MarkovModel
project model@Prototype.MkNodeModel{..} =
  let
    next = snd $ Prototype.fetchingModeled mempty mempty model
    Prototype.MkPerasState{..} = state
    s = fromIntegral clock
    r = Prototype.slotToRound protocol clock
    certsSet = Map.keysSet certs
    certNext f =
      let
        oldCert = f $ Prototype.state model
        newCert = f $ Prototype.state next
       in
        if oldCert == newCert
          then Nothing
          else Just . fromIntegral $ Prototype.round newCert
   in
    ( toPeras protocol def
    , MkChains
        { slot = s
        , prefix = 0 -- FIXME: Address this later. It should be the last common block of the chains tied for highest weight.
        , honest =
            MkChain
              { weight = fromInteger $ Prototype.chainWeight (Prototype.perasB protocol) certsSet chainPref
              , certPrime = fromIntegral $ Prototype.round certPrime
              , certPrimeNext = certNext Prototype.certPrime
              , certUltimate = any ((== r) . Prototype.round) certsSet
              , certPenultimate = any ((== (r - 1)) . Prototype.round) certsSet
              , certAntepenultimate = any ((== (r - 2)) . Prototype.round) certsSet
              , certStar = fromIntegral $ Prototype.round certStar
              , certStarNext = certNext Prototype.certStar
              }
        , adversary = def
        , publicWeight = minBound -- FIXME: Address this later.
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
