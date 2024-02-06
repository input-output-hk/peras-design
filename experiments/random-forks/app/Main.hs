module Main (
  main
) where

import Control.Monad (void)
import Data.Default (def)
import Peras.RandomForks (writeGraph, run) 
import Peras.RandomForks.Peer (randomPeers, peerGraph)
import Peras.RandomForks.Protocol (mkProtocol)
import System.Environment (getArgs)
import System.FilePath ((<.>))

main :: IO ()
main =
  do
    args <- getArgs
    let parameters = def
        protocol = mkProtocol parameters
        peerFile = "peers"
    print parameters
    print protocol
    peers <- randomPeers parameters protocol
    writeGraph (peerFile <.> "dot") $ peerGraph peers
    putStrLn $ "Run `circo -Tpng -o '" <> peerFile <> ".png' '" <> peerFile <> ".dot'` to generate the diagram of peers."
    case args of
      ["peers"] -> pure ()
      ["run", duration] -> do
                             void $ run protocol (pure "chain-") peers (read duration)
                             putStrLn "Run `for i in chain-*.dot; do j=${i%%.dot}.png; dot -Tpng -o $j $i; done` to generate diagrams of chains."
      _ -> putStrLn "USAGE: random-forks (peers | run DURATION)"
      
