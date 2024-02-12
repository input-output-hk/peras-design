module Peras.Chain where

import Peras.Block (Block)

data Chain t
  = Genesis
  | Cons (Block t) (Chain t)
