module Main (
  main,
) where

import Data.Default (def)
import Peras.RandomForks (writeGraph)
import Peras.RandomForks.Peer (peerGraph, randomPeers)
import Peras.RandomForks.Protocol (mkProtocol)
import System.FilePath ((<.>))

main :: IO ()
main =
  do
    let parameters = def
        protocol = mkProtocol parameters
        peerFile = "peers"
    print parameters
    print protocol
    peers <- randomPeers parameters protocol
    writeGraph (peerFile <.> "dot") $ peerGraph peers
    putStrLn $ "Run `circo -Tpng -o '" <> peerFile <> ".png' '" <> peerFile <> ".dot'` to generate the diagram of peers."
