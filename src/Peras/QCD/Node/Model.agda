module Peras.QCD.Node.Model where

open import Data.Nat using (ℕ)

open import Haskell.Prelude

open import Peras.Block using (Block; Certificate; PartyId; Slot)
open import Peras.Chain using (Chain; MkRoundNumber; RoundNumber; Vote)
open import Peras.Crypto using (Hash; Hashable)
open import Peras.Message using (Message)

{-# FOREIGN AGDA2HS
import Control.Lens (Lens', lens)
import Data.Default (Default(..))
import GHC.Generics (Generic)
#-}

record Params : Set where
  field paramU : ℕ  -- round length
        paramL : ℕ  -- cutoff window
open Params public
{-# COMPILE AGDA2HS Params deriving (Eq, Generic, Ord, Show) #-}

defaultParams : Params
defaultParams =
  record {
    paramU = 120
  ; paramL = 10
  }
{-# COMPILE AGDA2HS defaultParams #-}
{-# FOREIGN AGDA2HS
instance Default Params where
  def = defaultParams
#-}

HashBlock = Block → Hash Block
{-# COMPILE AGDA2HS HashBlock #-}

HashTip = Chain → Hash Block
{-# COMPILE AGDA2HS HashTip #-}

IsHonest = Bool
{-# COMPILE AGDA2HS IsHonest #-}

record NodeModel : Set where
  field protocol : Params
        self : PartyId
        nowSlot : Slot
        nowRound : RoundNumber
        honest : IsHonest
        preferredChain : Chain
        preferredCerts : List Certificate
        preferredVotes : List Vote
open NodeModel public
{-# COMPILE AGDA2HS NodeModel deriving (Eq, Generic, Ord, Show) #-}

emptyNode : NodeModel
emptyNode =
  record {
    protocol = defaultParams
  ; self = 0
  ; nowSlot = 0
  ; nowRound = MkRoundNumber 0
  ; honest = True
  ; preferredChain = []
  ; preferredCerts = []
  ; preferredVotes = []
  }
{-# COMPILE AGDA2HS emptyNode #-}

{-# FOREIGN AGDA2HS
instance Default NodeModel where
  def = emptyNode
#-}

MakeBlock = Slot → PartyId → Hash Block → Maybe Certificate → Block
{-# COMPILE AGDA2HS MakeBlock #-}

MakeVote = RoundNumber → PartyId → Hash Block → Vote
{-# COMPILE AGDA2HS MakeVote #-}

-- State transition.

data Signal : Set where
  Initialize : Params → PartyId → IsHonest → Signal
  NewSlot : Signal
  NewRound : Signal
  ForgeBlock : MakeBlock → Signal
  CastVote : MakeVote → Signal
  ReceiveBlock : Block → Signal
  ReceiveVote : Vote → Signal
  ReceiveCertificate : Certificate → Signal
{-# COMPILE AGDA2HS Signal deriving (Eq, Generic, Ord, Show) #-}

-- Executable specification.

initialize : NodeModel → Params → PartyId → IsHonest → NodeModel × List Message
initialize node params party honesty =
  record node {
    protocol = params
  ; self = party
  ; honest = honesty
  } , []
{-# COMPILE AGDA2HS initialize #-}

newSlot : NodeModel → NodeModel × List Message
newSlot node = record node {nowSlot = nowSlot node + 1} , []
{-# COMPILE AGDA2HS newSlot #-}

newRound : NodeModel → NodeModel × List Message
newRound node = record node {nowRound = MkRoundNumber $ RoundNumber.roundNumber (nowRound node) + 1} , []
{-# COMPILE AGDA2HS newRound #-}

forgeBlock : NodeModel → HashTip → MakeBlock → NodeModel × List Message
forgeBlock node hashTip makeBlock =
  record node {preferredChain = chain'; preferredCerts = snd certs}, Message.NewChain chain' ∷ []
  where
    certs : Maybe Certificate × List Certificate
    certs = case preferredCerts node of λ where
      [] → Nothing , []
      (cert' ∷ certs) → Just cert' , certs
    prior = preferredChain node
    block = makeBlock (nowSlot node) (self node) (hashTip prior) (fst certs)
    chain' = block ∷ prior
{-# COMPILE AGDA2HS forgeBlock #-}

buildCert : NodeModel → List Message → NodeModel × List Message
buildCert node messages = node , messages -- FIXME

castVote : NodeModel → HashBlock → MakeVote → NodeModel × List Message
castVote node hashBlock makeVote =
  buildCert
    (record node {preferredVotes = preferredVotes node ++ vote})
    (map Message.SomeVote vote)
  where
    eligible : Block → Bool
    eligible block = Block.slotNumber block + paramL (protocol node) <= nowSlot node
    vote = case filter eligible (preferredChain node) of λ where
      [] → []
      (block ∷ _) → makeVote (nowRound node) (self node) (hashBlock block) ∷ []
{-# COMPILE AGDA2HS castVote #-}


record State (s : Set) (a : Set) : Set where
  field runState : s → a × s
open State public
{-# COMPILE AGDA2HS State newtype #-}

makeState : {s : Set} → {a : Set} → (s → a × s) → State s a
makeState f = record {runState = f}
{-# COMPILE AGDA2HS makeState #-}

execState : {s : Set} → {a : Set} → State s a → s → s
execState m x = snd (runState m x)
{-# COMPILE AGDA2HS execState #-}

evalState : {s : Set} → {a : Set} → State s a → s → a
evalState m x = fst (runState m x)
{-# COMPILE AGDA2HS evalState #-}

getState : {s : Set} → State s s
getState = record {runState = λ s → s , s}
{-# COMPILE AGDA2HS getState #-}

putState : {s : Set} → s → State s ⊤
putState s = record {runState = λ _ → tt , s}
{-# COMPILE AGDA2HS putState #-}

fmapState : {s : Set} → {a : Set} → {b : Set} → (a → b) → State s a → State s b
fmapState f m =
  record {runState = λ s →
    let xs = runState m s
    in f (fst xs) , snd xs
  }
{-# COMPILE AGDA2HS fmapState #-}

instance
  iFunctorState : {s : Set} → Functor (State s)
  iFunctorState .fmap f m = fmapState f m
  iFunctorState ._<$>_ f m = fmapState f m
  iFunctorState ._<&>_ m f = fmapState f m
  iFunctorState ._<$_ x m = fmapState (λ y → x ⦃ y ⦄) m
  iFunctorState ._$>_ m x = fmapState (λ y → x ⦃ y ⦄) m
  iFunctorState .void m = fmapState (const tt) m
{-# COMPILE AGDA2HS iFunctorState #-}
  
pureState : {s : Set} → {a : Set} → a → State s a
pureState x = record {runState = λ s → x , s}
{-# COMPILE AGDA2HS pureState #-}

apState : {s : Set} → {a : Set} → {b : Set} → State s (a → b) → State s a → State s b
apState m n =
  record {runState = λ s →
    let fs = runState m s
        xs = runState n (snd fs)
        y = (fst fs) (fst xs)
    in y , snd xs
  }
{-# COMPILE AGDA2HS apState #-}

instance
  iApplicativeState : {s : Set} → Applicative (State s)
  iApplicativeState .pure x = pureState x
  iApplicativeState ._<*>_ f x = apState f x
  iApplicativeState ._<*_ x y = apState (fmapState const x) y
  iApplicativeState ._*>_ x y = apState (fmapState (const id) x) y
{-# COMPILE AGDA2HS iApplicativeState #-}

bindState : {s : Set} → {a : Set} → {b : Set} → State s a → (a → State s b) → State s b
bindState m f =
  record {runState = λ s →
    let xs = runState m s
        xs' = runState (f (fst xs)) (snd xs)
    in fst xs' , snd xs'
  }
{-# COMPILE AGDA2HS bindState #-}

instance
  iMonadState : {s : Set} → Monad (State s)
  iMonadState .return x = pureState x
  iMonadState ._>>=_ m f = bindState m f
  iMonadState ._>>_ m x = bindState m (λ y → x ⦃ y ⦄)
  iMonadState ._=<<_ f m = bindState m f
{-# COMPILE AGDA2HS iMonadState #-}

Lens' : Set → Set → Set₁
Lens' s a = {f : Set → Set} → ⦃ _ : Functor f ⦄ → (a → f a) → s → f s

lens : {s : Set} → {a : Set} → (s → a) → (s → a → s) → Lens' s a
lens sa sbt afb s = sbt s <$> afb (sa s)

nowSlotLens : Lens' NodeModel Slot
nowSlotLens = lens nowSlot (λ s' b → record s' {nowSlot = b})
{-# COMPILE AGDA2HS nowSlotLens #-}

--use' : {s : Set} → {a : Set} → Lens' s a → State s a
--use' l = l pureState _

--use'' : Lens' NodeModel Slot → State NodeModel Slot
--use'' l = l pureState emptyNode

record Const (a : Set) (b : Set) : Set where
  constructor MkConst
  field getConst : a

fmapConst : {a : Set} → {b : Set} → {b' : Set} → (b → b') → Const a b → Const a b'
fmapConst _ x = record {getConst = Const.getConst x}

instance
  iFunctorConst : {a : Set} → Functor (Const a)
  iFunctorConst .fmap m x = fmapConst m x
  iFunctorConst ._<$>_ m x = fmapConst m x
  iFunctorConst ._<&>_ x m = fmapConst m x
  iFunctorConst ._<$_ x m = fmapConst (λ y → x ⦃ y ⦄) m
  iFunctorConst ._$>_ m x = fmapConst (λ y → x ⦃ y ⦄) m
  iFunctorConst .void m = fmapConst (λ _ → tt) m

getField : {s : Set} → {a : Set} → Lens' s a → s → a
getField l s = Const.getConst (l MkConst s)

use : {s : Set} → {a : Set} → Lens' s a → State s a
use l = getField l <$> getState

record Identity (a : Set) : Set where
  constructor MkIdentity
  field runIdentity : a

fmapIdentity : {a : Set} → {b : Set} → (a → b) → Identity a → Identity b
fmapIdentity f x = MkIdentity $ f $ Identity.runIdentity x

instance
  iFunctorIdentity : Functor Identity
  iFunctorIdentity .fmap m x = fmapIdentity m x
  iFunctorIdentity ._<$>_ m x = fmapIdentity m x
  iFunctorIdentity ._<&>_ x m = fmapIdentity m x
  iFunctorIdentity ._<$_ x m = fmapIdentity (λ y → x ⦃ y ⦄) m
  iFunctorIdentity ._$>_ m x = fmapIdentity (λ y → x ⦃ y ⦄) m
  iFunctorIdentity .void m = fmapIdentity (λ _ → tt) m
  
setField : {s : Set} → {a : Set} → Lens' s a → a → s → s
setField l x s = Identity.runIdentity (l (λ _ → MkIdentity x) s)

assign : {s : Set} → {a : Set} → Lens' s a → a → State s ⊤
assign l x = (putState ∘ setField l x) =<< getState

_࠺_ : {s : Set} → {a : Set} → Lens' s a → a → State s ⊤
_࠺_ = assign
{-# COMPILE AGDA2HS _࠺_ #-}

test1 : State NodeModel Slot
test1 = do
      i <- use nowSlotLens
      nowSlotLens ࠺ (i + 1)
      use nowSlotLens
{-# COMPILE AGDA2HS test1 #-}
