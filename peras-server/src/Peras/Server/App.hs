{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.Server.App where

import Control.Concurrent (forkIO)
import Control.Concurrent.Class.MonadSTM (atomically)
import Control.Concurrent.Class.MonadSTM.TVar (modifyTVar', newTVarIO)
import Control.Monad (forever)
import Control.Tracer (Tracer (..), emit)
import Data.Aeson (FromJSON, ToJSON)
import Data.Aeson as A (eitherDecode, encode)
import Data.Default (def)
import Data.Functor (void)
import Data.Text.Lazy.Encoding (decodeUtf8)
import GHC.Generics (Generic)
import qualified Network.WebSockets as WS
import Peras.Prototype.Network (SimControl (delay, pause, stop), simulate)
import Peras.Prototype.Network.Arbitrary (genSimConfigIO)
import Peras.Prototype.Types (PerasParams (..))

data AppControl
  = Simulate
      { duration :: Integer
      , parties :: Integer
      , u :: Integer
      , a :: Integer
      , r :: Integer
      , k :: Integer
      , l :: Integer
      , tau :: Integer
      , b :: Integer
      , t :: Integer
      , committee :: Integer
      , delta :: Integer
      , activeSlots :: Double
      , delayMicroseconds :: Int
      , rngSeed :: Int
      }
  | Pause
  | Resume
  | Stop
  deriving (Eq, Generic, Show)

instance FromJSON AppControl
instance ToJSON AppControl

instance WS.WebSocketsData AppControl where
  fromDataMessage (WS.Text msg _) = either error id $ A.eitherDecode msg
  fromDataMessage (WS.Binary msg) = either error id $ A.eitherDecode msg
  fromLazyByteString = either error id . A.eitherDecode
  toLazyByteString = A.encode

wsapp :: WS.ServerApp
wsapp pending = do
  conn <- WS.acceptRequest pending
  WS.withPingThread conn 30 def $ do
    control <- newTVarIO def
    let modifyControl = atomically . modifyTVar' control
    forever $
      WS.receiveData conn
        >>= \case
          Simulate{..} -> do
            modifyControl $ \c -> c{delay = delayMicroseconds, stop = False, pause = False}
            simConfig <-
              genSimConfigIO
                def{perasU = u, perasA = a, perasR = r, perasK = k, perasL = l, perasτ = tau, perasB = b, perasT = t, perasΔ = delta}
                activeSlots
                parties
                committee
                (fromIntegral duration)
                rngSeed
            let tracer = Tracer . emit $ WS.sendTextData conn . decodeUtf8 . A.encode
            void . forkIO . void $ simulate tracer control simConfig
          Pause -> modifyControl $ \c -> c{pause = True}
          Resume -> modifyControl $ \c -> c{pause = False}
          Stop -> modifyControl $ \c -> c{stop = True}
