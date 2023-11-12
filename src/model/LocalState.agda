module LocalState where

open import Parameters
open import BlockTree

record LocalState : Set₁ where
  field tree : BlockTree
        pk : Party
