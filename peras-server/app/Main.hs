{-# LANGUAGE LambdaCase #-}

module Main where

import Control.Concurrent.Class.MonadSTM (TQueue, atomically, newTQueueIO, newTVarIO, writeTQueue)
import Control.Monad.Class.MonadSTM (MonadSTM)
import Control.Monad.Class.MonadSay (MonadSay, say)
import Control.Tracer (Tracer (..), emit)
import Data.Aeson (ToJSON, Value, encode, toJSON)
import Data.Default (def)
import Data.Functor ((<&>))
import Data.Text.Lazy (unpack)
import Data.Text.Lazy.Encoding (decodeUtf8)
import Peras.Server (runServer)
import System.Environment (getArgs)

mkTracer :: (MonadSTM m, ToJSON a, MonadSay m) => TQueue m Value -> Tracer m a
mkTracer events =
  Tracer $
    emit
      ( \a -> do
          say $ unpack $ decodeUtf8 $ encode a
          atomically . writeTQueue events . toJSON $ a
      )

main :: IO ()
main = do
  port <-
    getArgs <&> \case
      [p] -> read p
      _ -> 8091
  events <- newTQueueIO
  control <- newTVarIO def
  runServer port events control
