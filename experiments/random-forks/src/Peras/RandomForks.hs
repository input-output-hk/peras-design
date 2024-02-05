module Peras.RandomForks where

import qualified Language.Dot.Pretty as G
import qualified Language.Dot.Syntax as G

writeGraph ::
  FilePath ->
  G.Graph ->
  IO ()
writeGraph filename graph = writeFile filename $ G.renderDot graph
