module Peras.Chain where

import Peras.Block (Block)

data Chain t = Genesis
             | Cons (Block t) (Chain t)

asList :: Chain t -> [Block t]
asList Genesis = []
asList (Cons x c) = x : asList c

asChain :: [Block t] -> Chain t
asChain [] = Genesis
asChain (x : bs) = Cons x (asChain bs)

