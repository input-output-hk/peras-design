
module Peras.Abstract.Protocol.Model where

open import Haskell.Prelude
open import Haskell.Control.Monad
open import Agda.Builtin.Maybe hiding (Maybe)
open import Data.Nat using (ℕ; _/_; _%_; NonZero)
open import Peras.SmallStep
open import Peras.Block renaming (certificate to blockCert)
open import Peras.Chain
open import Peras.Crypto
open import Peras.Numbering
open import Peras.Abstract.Protocol.Params
open import Protocol.Peras using ()

{-# FOREIGN AGDA2HS
{-# LANGUAGE RecordWildCards #-}
#-}

{-# FOREIGN AGDA2HS
  import Peras.Orphans
  import Peras.Block (certificate, blockRef)
  import Peras.Crypto (hash)
  import Data.Maybe (catMaybes, listToMaybe, maybeToList)
  import Data.List (maximumBy)
  import Data.Function (on)
  import qualified Data.Set as Set
  import Data.Set (Set)
#-}

-- Hoop-jumping ---

div : ℕ → (n : ℕ) → .⦃ NonZero n ⦄ → ℕ
div = _/_

mod : ℕ → (n : ℕ) → .⦃ NonZero n ⦄ → ℕ
mod = _%_

uneraseNonZero : ∀ {n} → @0 NonZero n → NonZero n
uneraseNonZero {zero} ()
uneraseNonZero {suc n} _ = _

certificate : Block → Maybe Certificate
certificate record{certificate = just c}  = Just c
certificate record{certificate = nothing} = Nothing

catMaybes : List (Maybe a) → List a
catMaybes [] = []
catMaybes (Nothing ∷ xs) = catMaybes xs
catMaybes (Just x ∷ xs) = x ∷ catMaybes xs

maybeToList : Maybe a → List a
maybeToList Nothing = []
maybeToList (Just x) = x ∷ []

listToMaybe : List a → Maybe a
listToMaybe [] = Nothing
listToMaybe (x ∷ _) = Just x

postulate
  -- FIXME (change model so we don't need it?)
  maximumBy : (a → a → Ordering) → List a → a

comparing : ⦃ Ord b ⦄ → (a → b) → a → a → Ordering
comparing f x y = compare (f x) (f y)


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

slotInRound : PerasParams → SlotNumber → SlotNumber
slotInRound protocol slot = MkSlotNumber (mod (getSlotNumber slot) (perasU protocol) ⦃ uneraseNonZero (perasNonZeroU protocol) ⦄)
{-# COMPILE AGDA2HS slotInRound #-}

nextSlot : SlotNumber → SlotNumber
nextSlot (MkSlotNumber n) = MkSlotNumber (1 + n)
{-# COMPILE AGDA2HS nextSlot #-}

insertCert : SlotNumber → Certificate → List (Certificate × SlotNumber) → List (Certificate × SlotNumber)
insertCert slot cert [] = (cert , slot) ∷ []
insertCert slot cert ((cert' , slot') ∷ certs) =
  if cert == cert'
  then (cert' , slot') ∷ certs
  else (cert' , slot') ∷ insertCert slot cert certs
{-# COMPILE AGDA2HS insertCert #-}

seenBeforeStartOfRound : PerasParams → RoundNumber → Certificate × SlotNumber → Bool
seenBeforeStartOfRound params r (c , s) =
  getSlotNumber s <= getRoundNumber r * perasU params
{-# COMPILE AGDA2HS seenBeforeStartOfRound #-}

postulate
  preferredChain : PerasParams → List Certificate → List Chain → Chain

{-# FOREIGN AGDA2HS
preferredChain :: PerasParams -> [Certificate] -> [Chain] -> Chain
preferredChain MkPerasParams{..} certs chains =
  maximumBy (compare `on` chainWeight perasB (Set.fromList certs)) (genesisChain : chains)

chainWeight :: Integer -> Set Certificate -> Chain -> Integer
chainWeight boost certs blocks =
  let
    -- Block hashes certified by any certificate.
    certifiedBlocks = Set.map blockRef certs :: Set (Hash Block)
    -- Block hashes on the chain.
    chainBlocks = Set.fromList $ hash <$> blocks :: Set (Hash Block)
   in
    -- Length of the chain plus the boost times the count of certified blocks.
    fromIntegral (length blocks)
      + boost * fromIntegral (Set.size $ certifiedBlocks `Set.intersection` chainBlocks)
#-}

blockOldEnough : PerasParams → SlotNumber → Block → Bool
blockOldEnough params clock record{slotNumber = slot} = getSlotNumber slot + perasL params + perasT params <= getSlotNumber clock

votesInState : NodeModel → List (RoundNumber × Block)
votesInState s = maybeToList do
  guard (slotInRound params slot == MkSlotNumber (perasT params))
  block ← listToMaybe (dropWhile (not ∘ blockOldEnough params slot) pref)
  -- guard VR-1A and friends
  pure (r , block)
  where
    params = protocol s
    slot   = clock s
    r      = slotToRound params slot

    -- This is to deal with the fact that the information
    -- available is out of step
    allChains' = map snd $ filter ((_< r) ∘ fst) (allChains s)

    allSeenCerts' : List (Certificate × SlotNumber)
    allSeenCerts' = filter (seenBeforeStartOfRound params r) (allSeenCerts s)

    pref = preferredChain params (map fst allSeenCerts') allChains'

    certAndSlot' = maximumBy (comparing snd) allSeenCerts'
    cert'        = fst certAndSlot'
    cert'Slot    = snd certAndSlot'

    certS = maximumBy (comparing round) (genesisCert ∷ catMaybes (map certificate pref))

{-# COMPILE AGDA2HS votesInState #-}

transition : NodeModel → EnvAction → Maybe (List (RoundNumber × Block) × NodeModel)
transition s Tick =
  Just (sutVotes , record s' { allVotes = sutVotes ++ allVotes s'
                             ; allSeenCerts = foldr (insertCert (clock s')) (allSeenCerts s') certsFromQuorum
                             })
  where s' = record s { clock = nextSlot (clock s) }
        sutVotes = votesInState s'
        certsFromQuorum = []
transition s (NewChain chain) =
  Just ([] , record s
             { allChains = (slotToRound (protocol s) (clock s) , chain) ∷ allChains s
             ; allSeenCerts = foldr (insertCert (nextSlot (clock s))) (allSeenCerts s) (catMaybes $ map certificate chain)
             })
transition s (NewVote v) = Just ([] , record s { allVotes = v ∷ allVotes s })
{-# COMPILE AGDA2HS transition #-}
