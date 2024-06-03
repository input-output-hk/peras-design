module Main where

import Control.Concurrent.Class.MonadSTM (TQueue, atomically, newTQueueIO, writeTQueue)
import Control.Monad.Class.MonadAsync (race_)
import Control.Monad.Class.MonadSTM (MonadSTM)
import Control.Monad.Class.MonadSay (MonadSay, say)
import Control.Tracer (Tracer (..), emit)
import Data.Aeson (ToJSON, Value, encode, toJSON)
import Data.Text.Lazy (unpack)
import Data.Text.Lazy.Encoding (decodeUtf8)
import Peras.Abstract.Protocol.Network (SimConfig (..), simConfigExample, simulate)
import Peras.Server (runServer)

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
  let config = simConfigExample{finish = 100000}
  events <- newTQueueIO
  simulate (mkTracer events) config
    `race_` runServer events
