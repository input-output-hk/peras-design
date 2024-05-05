module Peras.QCD.State where

open import Haskell.Prelude

{-# FOREIGN AGDA2HS
{-# LANGUAGE RankNTypes #-}
import Control.Lens (Getting, assign, modifying)
import qualified Control.Lens as L (Lens', use)
import Control.Monad.State (MonadState)
import qualified Control.Monad.State as S (State)
#-}

record State (s : Set) (a : Set) : Set where
  field runState : s → a × s
open State public
{-# FOREIGN AGDA2HS
type State s a = S.State s a
#-}

makeState : {s : Set} → {a : Set} → (s → a × s) → State s a
makeState f = record {runState = f}

execState : {s : Set} → {a : Set} → State s a → s → s
execState m x = snd (runState m x)

evalState : {s : Set} → {a : Set} → State s a → s → a
evalState m x = fst (runState m x)

getState : {s : Set} → State s s
getState = record {runState = λ s → s , s}

putState : {s : Set} → s → State s ⊤
putState s = record {runState = λ _ → tt , s}

private

  fmapState : {s : Set} → {a : Set} → {b : Set} → (a → b) → State s a → State s b
  fmapState f m =
    makeState $ λ s →
      let xs = runState m s
      in f (fst xs) , snd xs

  pureState : {s : Set} → {a : Set} → a → State s a 
  pureState x = record {runState = λ s → x , s}

  apState : {s : Set} → {a : Set} → {b : Set} → State s (a → b) → State s a → State s b
  apState m n =
    makeState $ λ s →
      let fs = runState m s
          xs = runState n (snd fs)
          y = (fst fs) (fst xs)
      in y , snd xs

  bindState : {s : Set} → {a : Set} → {b : Set} → State s a → (a → State s b) → State s b
  bindState m f =
    makeState $ λ s →
      let xs = runState m s
          xs' = runState (f (fst xs)) (snd xs)
      in fst xs' , snd xs'

private
  fmap=_ : (∀ {a b} → (a → b) → f a → f b) → Functor f
  fmap= x = record {DefaultFunctor (record {fmap = x})}

instance
  iFunctorState : {s : Set} → Functor (State s)
  iFunctorState = fmap= fmapState

instance
  iApplicativeState : {s : Set} → Applicative (State s)
  iApplicativeState .pure x = pureState x
  iApplicativeState ._<*>_ f x = apState f x
  iApplicativeState ._<*_ x y = apState (fmapState const x) y
  iApplicativeState ._*>_ x y = apState (fmapState (const id) x) y

instance
  iMonadState : {s : Set} → Monad (State s)
  iMonadState .return x = pureState x
  iMonadState ._>>=_ m f = bindState m f
  iMonadState ._>>_ m x = bindState m (λ y → x ⦃ y ⦄)
  iMonadState ._=<<_ f m = bindState m f

Lens' : Set → Set → Set₁
Lens' s a = ∀ {f : Set → Set} → ⦃ _ : Functor f ⦄ → (a → f a) → s → f s
{-# FOREIGN AGDA2HS
type Lens' s a = L.Lens' s a
#-}

lens' : {s : Set} → {a : Set} → (s → a) → (s → a → s) → Lens' s a
lens' sa sbt afb s = sbt s <$> afb (sa s)
{-# COMPILE AGDA2HS lens' #-}

record Const (a : Set) (b : Set) : Set where
  constructor MakeConst
  field getConst : a

private

  fmapConst : {a : Set} → {b : Set} → {b' : Set} → (b → b') → Const a b → Const a b'
  fmapConst _ x = MakeConst $ Const.getConst x

instance
  iFunctorConst : {a : Set} → Functor (Const a)
  iFunctorConst = fmap= fmapConst

getField : {s : Set} → {a : Set} → Lens' s a → s → a
getField l s = Const.getConst $ l MakeConst s

use : {s : Set} → {a : Set} → Lens' s a → State s a
use l = getField l <$> getState
{-# FOREIGN AGDA2HS
use :: MonadState s m => Getting a s a -> m a
use = L.use
#-}

record Identity (a : Set) : Set where
  constructor MakeIdentity
  field runIdentity : a

private

  fmapIdentity : {a : Set} → {b : Set} → (a → b) → Identity a → Identity b
  fmapIdentity f x = MakeIdentity ∘ f $ Identity.runIdentity x

instance
  iFunctorIdentity : Functor Identity
  iFunctorIdentity = fmap= fmapIdentity

setField : {s : Set} → {a : Set} → Lens' s a → a → s → s
setField l x s = Identity.runIdentity (l (λ _ → MakeIdentity x) s)

assign : {s : Set} → {a : Set} → Lens' s a → a → State s ⊤
assign l x = (putState ∘ setField l x) =<< getState

_≔_ : {s : Set} → {a : Set} → Lens' s a → a → State s ⊤
_≔_ = assign
-- FIXME: Set associativity and precedence (Agda and Haskell).
{-# COMPILE AGDA2HS _≔_ #-}

modifying : {s : Set} → {a : Set} → Lens' s a → (a → a) → State s ⊤
modifying l f = (assign l ∘ f) =<< use l

_≕_ : {s : Set} → {a : Set} → Lens' s a → (a → a) → State s ⊤
_≕_ = modifying
-- FIXME: Set associativity and precedence (Agda and Haskell).
{-# COMPILE AGDA2HS _≕_ #-}
