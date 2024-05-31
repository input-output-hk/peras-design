module Main where

import Control.Concurrent.Class.MonadSTM (newTQueueIO, newTVarIO)
import Peras.Abstract.Protocol.Types (defaultParams)
import Peras.Server (runServer)

main :: IO ()
main = do
  params <- newTVarIO defaultParams
  events <- newTQueueIO
  runServer params events
