{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Peras.Server where

import Control.Concurrent.Class.MonadSTM (
  MonadSTM,
  atomically,
  newBroadcastTChanIO,
  writeTChan,
 )
import Control.Concurrent.Class.MonadSTM.TChan (TChan, dupTChan, readTChan)
import Control.Concurrent.Class.MonadSTM.TQueue
import Control.Concurrent.Class.MonadSTM.TVar (TVar, modifyTVar')
import Control.Monad (forever)
import Control.Monad.Class.MonadAsync (race_)
import Control.Monad.IO.Class (liftIO)
import Control.Tracer (Tracer (Tracer), emit)
import Data.Aeson (FromJSON, ToJSON (toJSON), Value, decode, encode)
import Data.Default (def)
import Data.Functor (void)
import Data.Text.Lazy.Encoding (decodeUtf8)
import GHC.Generics (Generic)
import Network.HTTP.Types (status400)
import qualified Network.Wai as Wai
import qualified Network.Wai.Handler.Warp as Warp
import qualified Network.Wai.Handler.WebSockets as WS
import Network.Wai.Middleware.RequestLogger (logStdoutDev)
import qualified Network.WebSockets as WS
import Peras.Abstract.Protocol.Network (SimConfig (..), SimControl (delay, pause, stop), simulate)
import Peras.Abstract.Protocol.Network.Arbitrary (genSimConfigIO)
import Peras.Abstract.Protocol.Types (PerasParams (..))
import qualified Web.Scotty as Sc

runServer :: Warp.Port -> TQueue IO Value -> TVar IO SimControl -> IO ()
runServer port queue control = do
  let settings = Warp.setPort port Warp.defaultSettings
  sapp <- scottyApp queue control
  clientChannel <- newBroadcastTChanIO
  feedClient queue clientChannel
    `race_` Warp.runSettings
      settings
      (WS.websocketsOr WS.defaultConnectionOptions (wsapp clientChannel) sapp)

feedClient :: MonadSTM m => TQueue m Value -> TChan m Value -> m ()
feedClient input output = forever $ do
  atomically $ do
    readTQueue input >>= writeTChan output

scottyApp :: TQueue IO Value -> TVar IO SimControl -> IO Wai.Application
scottyApp queue control =
  Sc.scottyApp $ do
    Sc.middleware logStdoutDev

    Sc.get "/" $
      Sc.redirect "/index.html"

    Sc.get "/index.html" $
      Sc.file "index.html"

    Sc.get "/index.js" $
      Sc.file "index.js"

    Sc.get "/peras.css" $
      Sc.file "peras.css"

    Sc.post "/simulate" $
      decode <$> Sc.body
        >>= \case
          Nothing -> Sc.status status400
          Just req -> liftIO $ do
            atomically . modifyTVar' control $ \c -> c{delay = delayMicroseconds req, stop = False, pause = False}
            simConfig <- simRequestToConfig req
            void $ simulate (mkTracer queue) control simConfig

    Sc.delete "/stop" $ liftIO $ atomically $ modifyTVar' control $ \c -> c{stop = True}

    Sc.patch "/pause" $ liftIO $ atomically $ modifyTVar' control $ \c -> c{pause = True}

    Sc.patch "/resume" $ liftIO $ atomically $ modifyTVar' control $ \c -> c{pause = False}

mkTracer :: (MonadSTM m, ToJSON a) => TQueue m Value -> Tracer m a
mkTracer events =
  Tracer $
    emit
      ( \a -> atomically . writeTQueue events . toJSON $ a
      )

wsapp :: TChan IO Value -> WS.ServerApp
wsapp queue pending = do
  conn <- WS.acceptRequest pending
  WS.withPingThread conn 30 (pure ()) $ do
    clientQueue <- atomically $ dupTChan queue
    forever $ do
      msg <- atomically $ readTChan clientQueue
      WS.sendTextData conn $ decodeUtf8 $ encode msg

data SimulationRequest = SimulationRequest
  { duration :: Integer
  , parties :: Integer
  , u :: Integer
  , a :: Integer
  , r :: Integer
  , k :: Integer
  , l :: Integer
  , tau :: Integer
  , b :: Integer
  , committee :: Integer
  , delta :: Integer
  , activeSlots :: Double
  , delayMicroseconds :: Int
  }
  deriving (Eq, Generic, Show)

instance FromJSON SimulationRequest
instance ToJSON SimulationRequest

simRequestToConfig :: SimulationRequest -> IO SimConfig
simRequestToConfig SimulationRequest{..} =
  genSimConfigIO
    def{perasU = u, perasA = a, perasR = r, perasK = k, perasL = l, perasτ = tau, perasB = b, perasΔ = delta}
    activeSlots
    parties
    committee
    (fromIntegral duration)
