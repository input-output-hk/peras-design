module Main where

import Control.Concurrent.Class.MonadSTM (TQueue, atomically, newTQueueIO, writeTQueue)
import Control.Monad.Class.MonadAsync (concurrently_)
import Control.Monad.Class.MonadSTM (MonadSTM)
import Control.Monad.Class.MonadSay (MonadSay, say)
import Control.Tracer (Tracer (..), emit)
import Data.Aeson (ToJSON, Value, encode, toJSON)
import Data.Text.Lazy (unpack)
import Data.Text.Lazy.Encoding (decodeUtf8)
import Peras.Server (openUI, runServer)

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
  events <- newTQueueIO
  runServer events
    `concurrently_` openUI
