module Peras.RandomForks (
  execute,
) where

import Control.Monad.State (execStateT)
import Peras.RandomForks.IO.Graphviz (chainGraph, peersGraph, writeGraph)
import Peras.RandomForks.Peer (randomPeers)
import Peras.RandomForks.Protocol (mkProtocol)
import Peras.RandomForks.Simulation (History (..), initialHistory, run)
import Peras.RandomForks.Types (Parameters, PeerState (preferredChain), Peers (getPeers))
import System.Random (StdGen)
import System.Random.Stateful (newIOGenM)

import qualified Data.Map.Strict as M

execute ::
  StdGen ->
  Parameters ->
  Int ->
  FilePath ->
  FilePath ->
  IO ()
execute stdGen parameters duration peerFilename chainFilename =
  do
    gen <- newIOGenM stdGen
    let protocol' = mkProtocol parameters
    peers <- randomPeers gen parameters protocol'
    history <- run gen duration `execStateT` initialHistory protocol' peers
    writeGraph peerFilename $ peersGraph peers
    let chains = preferredChain <$> M.elems (getPeers . snd . M.findMax $ peerHistory history)
    writeGraph chainFilename $ chainGraph chains
