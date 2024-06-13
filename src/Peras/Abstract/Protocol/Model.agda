
module Peras.Abstract.Protocol.Model where

open import Haskell.Prelude
open import Agda.Builtin.Maybe hiding (Maybe)
open import Data.Nat using (ℕ; _/_; NonZero)
open import Peras.SmallStep
open import Peras.Block renaming (certificate to blockCert)
open import Peras.Chain
open import Peras.Crypto
open import Peras.Numbering
open import Peras.Abstract.Protocol.Params

{-# FOREIGN AGDA2HS
  import Peras.Orphans
  import Peras.Block (certificate)
#-}

-- Hoop-jumping ---

div : ℕ → (n : ℕ) → .⦃ NonZero n ⦄ → ℕ
div = _/_

uneraseNonZero : ∀ {n} → @0 NonZero n → NonZero n
uneraseNonZero {zero} ()
uneraseNonZero {suc n} _ = _

certificate : Block → Maybe Certificate
certificate record{certificate = just c}  = Just c
certificate record{certificate = nothing} = Nothing

-- The actual model ---

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
{-# COMPILE AGDA2HS EnvAction deriving (Eq, Show) #-}

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
                       ; perasNonZeroU = _
                       }
  ; allChains        = (0 , genesisChain) ∷ []
  ; allVotes         = []
  ; allSeenCerts     = (genesisCert , 0) ∷ []
  }
{-# COMPILE AGDA2HS initialModelState #-}

slotToRound : PerasParams → SlotNumber → RoundNumber
slotToRound protocol (MkSlotNumber n) = MkRoundNumber (div n (perasU protocol) ⦃ uneraseNonZero (perasNonZeroU protocol) ⦄)
{-# COMPILE AGDA2HS slotToRound #-}

nextSlot : SlotNumber → SlotNumber
nextSlot (MkSlotNumber n) = MkSlotNumber (1 + n)
{-# COMPILE AGDA2HS nextSlot #-}

insertCert : SlotNumber → Maybe Certificate → List (Certificate × SlotNumber) → List (Certificate × SlotNumber)
insertCert slot Nothing certs = certs
insertCert slot (Just cert) [] = (cert , slot) ∷ []
insertCert slot (Just cert) ((cert' , slot') ∷ certs) =
  if cert == cert'
  then (cert' , slot') ∷ certs
  else (cert' , slot') ∷ insertCert slot (Just cert) certs
{-# COMPILE AGDA2HS insertCert #-}

transition : NodeModel → EnvAction → Maybe (List Vote × NodeModel)
transition s Tick = Nothing
transition s (NewChain chain) =
  Just ([] , record s
             { allChains = (slotToRound (protocol s) (clock s) , chain) ∷ allChains s
             ; allSeenCerts = foldr (insertCert (nextSlot (clock s)) ∘ certificate) (allSeenCerts s) chain
             })
transition s (NewVote v) = Just ([] , record s { allVotes = v ∷ allVotes s })
{-# COMPILE AGDA2HS transition #-}
