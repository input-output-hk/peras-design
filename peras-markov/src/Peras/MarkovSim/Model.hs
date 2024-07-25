{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Peras.MarkovSim.Model {-# DEPRECATED "Only partially tests markov-chain simulator." #-} where

import Control.Arrow ((***))
import Control.Monad.Except (runExceptT)
import Control.Monad.State (MonadState, MonadTrans, StateT (StateT), get, gets, lift, modify', put)
import Data.Bifunctor (Bifunctor (second))
import Data.Default (def)
import Data.Function (on)
import Peras.MarkovSim.Transition (blockCreation, fetching, tick, voting)
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
        runExceptT . modify' $ \(peras, chains) ->
          -- We need to call fetch here in order to update the cert bookkeeping.
          (peras, fetching peras $ tick chains)
      Prototype.Fetching newChains newVotes ->
        -- FIXME: For now, we set the run state based on the model state.
        runExceptT . put . project . snd $ Prototype.fetchingModeled newChains newVotes model
      Prototype.BlockCreation isLeader _payload ->
        runExceptT $ do
          let prob = pureProbabilities isLeader False
          (peras, chains) <- get
          case blockCreation peras prob chains of
            [(chains', _)] -> do
              modify' . second $ const chains'
              pure Nothing
            _ -> error "Markov projection failed."
      Prototype.Voting isMember ->
        let
          Prototype.MkNodeModel{..} = model
          r = Prototype.slotToRound protocol clock
          next = snd $ Prototype.fetchingModeled mempty mempty model
         in
          -- Sadly, we can only test certificates, not votes, and we have to
          -- deal with this mismatch between the state model and the run model.
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
        lift . gets $ on (==) (honest . snd) (project posterior)
      Prototype.BlockCreation _isLeader _payload ->
        lift . gets $ on (==) (honest . snd) (project posterior)
      Prototype.Voting _isMember ->
        lift . gets $ on (==) (honest . snd) (project posterior)

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
              { weight = 1 + fromInteger (Prototype.chainWeight (Prototype.perasB protocol) certsSet chainPref)
              , certPrime = fromIntegral $ Prototype.round certPrime
              , certPrimeNext = certNext Prototype.certPrime
              , certUltimate = any ((== r) . Prototype.round) certsSet || r == 0
              , certPenultimate = any ((== (r - 1)) . Prototype.round) certsSet || r == 1
              , certAntepenultimate = any ((== (r - 2)) . Prototype.round) certsSet || r == 2
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
