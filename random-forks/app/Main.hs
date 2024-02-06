module Main (
  main
) where

import Control.Monad (void)
import Data.Default (def)
import Peras.RandomForks (run) 
import Peras.RandomForks.IO.Graphviz (writeGraph, peersGraph) 
import Peras.RandomForks.Peer (randomPeers)
import Peras.RandomForks.Protocol (mkProtocol)
import System.Environment (getArgs)
import System.FilePath ((<.>))
import System.Random (getStdGen)
import System.Random.Stateful (newIOGenM)

main :: IO ()
main =
  do
    args <- getArgs
    gen <- newIOGenM =<< getStdGen
    let parameters = def
        protocol = mkProtocol parameters
        peerFile = "peers"
    print parameters
    print protocol
    peers <- randomPeers gen parameters protocol
    writeGraph (peerFile <.> "dot") $ peersGraph peers
    putStrLn $ "Run `circo -Tpng -o '" <> peerFile <> ".png' '" <> peerFile <> ".dot'` to generate the diagram of peers."
    case args of
      ["peers"] -> pure ()
      ["run", duration] -> do
                             void $ run gen protocol (pure "chain-") peers (read duration)
                             putStrLn "Run `for i in chain-*.dot; do j=${i%%.dot}.png; dot -Tpng -o $j $i; done` to generate diagrams of chains."
      _ -> putStrLn "USAGE: random-forks (peers | run DURATION)"
      
