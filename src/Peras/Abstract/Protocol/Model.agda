
module Peras.Abstract.Protocol.Model where

open import Haskell.Prelude
open import Peras.SmallStep
open import Peras.Block
open import Peras.Chain
open import Peras.Crypto
open import Peras.Numbering
open import Peras.Abstract.Protocol.Params

{-# FOREIGN AGDA2HS
  import Peras.Orphans
#-}

record NodeModel : Set where
  field
    clock            : SlotNumber
    protocol         : PerasParams
    allChains        : List (RoundNumber × Chain)
    allVotes         : List Vote
    allSeenCerts     : List (Certificate × SlotNumber)

open NodeModel public
{-# COMPILE AGDA2HS NodeModel deriving (Eq, Show) #-}

data EnvAction : Set where
  Tick     : EnvAction
  NewChain : Chain → EnvAction
  NewVote  : Vote → EnvAction

{-# COMPILE AGDA2HS EnvAction #-}

genesisHash : Hash Block
genesisHash = MkHash (replicateBS 8 0)
{-# COMPILE AGDA2HS genesisHash #-}

genesisChain : Chain
genesisChain = []
{-# COMPILE AGDA2HS genesisChain #-}

genesisCert : Certificate
genesisCert = MkCertificate 0 genesisHash
{-# COMPILE AGDA2HS genesisCert #-}

initialModelState : NodeModel
initialModelState = record
  { clock            = 1
  ; protocol         = record defaultPerasParams
                       { perasU = 5
                       ; perasR = 1
                       ; perasK = 1
                       ; perasL = 1
                       ; perasT = 1
                       ; perasΔ = 1
                       ; perasτ = 1
                       }
  ; allChains        = (0 , genesisChain) ∷ []
  ; allVotes         = []
  ; allSeenCerts     = (genesisCert , 0) ∷ []
  }
{-# COMPILE AGDA2HS initialModelState #-}

transition : NodeModel → EnvAction → Maybe (List Vote × NodeModel)
transition s Tick = {!!}
transition s (NewChain x) = {!!}
transition s (NewVote v) = Just ([] , record s { allVotes = v ∷ allVotes s })
