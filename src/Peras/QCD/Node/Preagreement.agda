module Peras.QCD.Node.Preagreement where

open import Data.Nat using (ℕ)
open import Haskell.Prelude
open import Peras.QCD.Crypto
open import Peras.QCD.Crypto.Placeholders
open import Peras.QCD.Node.Model
open import Peras.QCD.Protocol
open import Peras.QCD.State
open import Peras.QCD.Types
open import Peras.QCD.Types.Instances
open import Peras.QCD.Util

{-# FOREIGN AGDA2HS
import Peras.QCD.Types.Instances ()
#-}

-- Select a block to vote for, using preagreement.
preagreement : NodeState (Maybe Block)
preagreement =
  do
    l ← peras L
    now ← use currentSlot
    -- FIXME: To be implemented.
    pure Nothing
{-# COMPILE AGDA2HS preagreement #-}

