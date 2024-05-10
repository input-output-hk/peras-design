module Peras.QCD.Protocol where

open import Data.Nat using (ℕ)
open import Haskell.Prelude

{-# FOREIGN AGDA2HS
{-# LANGUAGE DeriveGeneric #-}
import Data.Default (Default(..))
import GHC.Generics (Generic)
#-}

-- Protocol parameters.

data ParamSymbol : Set where
  U : ParamSymbol  -- the length (in slots) of a voting round
  A : ParamSymbol  -- max. age for including vote certificate
  W : ParamSymbol  -- weight to cut off for common prefix
  L : ParamSymbol  -- the cutoff window (in slots) which is ignored to select block to vote for in a round
  B : ParamSymbol  -- weight boost per vote certificate
  Τ : ParamSymbol  -- number of votes required for quorum
  R : ParamSymbol  -- chain-ignorance period
  K : ParamSymbol  -- the length of a cooldown period (in voting rounds)
{-# COMPILE AGDA2HS ParamSymbol #-}

τ : ParamSymbol  -- number of votes required for quorum
τ = Τ
{-# COMPILE AGDA2HS τ #-}

record Params : Set where
  field paramU : ℕ  -- the length (in slots) of a voting round
        paramA : ℕ  -- max. age for including vote certificate
        paramW : ℕ  -- weight to cut off for common prefix
        paramL : ℕ  -- the cutoff window (in slots) which is ignored to select block to vote for in a round
        paramB : ℕ  -- weight boost per vote certificate
        paramΤ : ℕ  -- number of votes required for quorum
        paramR : ℕ  -- chain-ignorance period
        paramK : ℕ  -- the length of a cooldown period (in voting rounds)
        
open Params public
{-# COMPILE AGDA2HS Params deriving (Eq, Generic, Show) #-}

defaultParams : Params
defaultParams =
  record {
    paramU = 120
  ; paramA = 240
  ; paramW = 3600
  ; paramL = 120
  ; paramB = 10
  ; paramΤ = 300
  ; paramR = 120
  ; paramK = 600
  }
{-# COMPILE AGDA2HS defaultParams #-}
{-# FOREIGN AGDA2HS
instance Default Params where
  def = defaultParams
#-}

-- FIXME: Use a proxy so that parameters may have types other than ℕ.
perasParam : ParamSymbol → Params → ℕ
perasParam U = paramU
perasParam A = paramA
perasParam W = paramW
perasParam L = paramL
perasParam B = paramB
perasParam Τ = paramΤ
perasParam R = paramR
perasParam K = paramK
{-# COMPILE AGDA2HS perasParam #-}
