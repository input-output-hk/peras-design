
<!--
```agda
module Overview where

open import Agda.Builtin.List
open import Data.Nat
open import Data.Product using (_×_; _,_)
open import Haskell.Prelude hiding (a; b) renaming (_<_ to _<ʰ_; _×_ to _×ʰ_; _,_ to _,ʰ_)
open import CommonTypes
open import ProofPrelude

postulate
  …… : {A : Set} → A
```
-->

# Connecting random testing and formal specification

The objective of this exercise is to have a protocol with

- a formal declarative Agda specification,
- a QuickCheck Dynamic model for testing an implementation of one
  party of the protocol, and
- a proof that any test sequence run by the QuickCheck model
  corresponds to a valid trace in the formal specification.

The way we achieve this is to write the business logic of the
QuickCheck model in Agda and compile it to Haskell with `agda2hs`.

## Informal protocol definition

In this example we use a very simply protocol between two parties
Alice and Bob.

```agda
a b : Party
a = Alice
b = Bob
```

Alice and Bob take turns producing blocks containing consecutive
natural numbers.

```agda
_ : Block
_ = Blk 5
```

Time is modelled as slots, where Alice produces blocks in even numbered
slots and Bob produces blocks in odd numbered slots.

```agda
_ : Slot
_ = 3
```

If a party fails to produce a block in their slot the other party should produce
the missing block when it's their turn.

## Formal specification

```agda
open import FormalSpec
```

The formal specification gives a declarative small-step semantics for
how the state of the world evolves during the course of the protocol.

```agda
singleStep : h ⊢ s₀ ↝ s₁
manySteps  : h ⊢ s₀ ↝* s₁
```

<!--
```agda
singleStep = ……
manySteps = ……
```
-->

### Honesty

It's important to specify (and test), not only how parties behave in
the ideal happy-path scenario, but also how they behave in the
presence of adversarial behaviour from the other parties or the
environment. This is modelled by an honesty parameter (`h`) above,
that dictates who, if anyone, can take dishonest actions.

```agda
honestyModels : List Honesty
honestyModels = happyPath ∷ badAlice ∷ badBob ∷ []
```

Any dishonest action by a party is accompanied by evidence that the
party is allowed to behave adversarially in the given honesty
model.

```agda
dishonestBob : Dishonest badBob Bob
dishonestBob = badBob

noDishonestHappyPath : Dishonest happyPath p → ⊥
noDishonestHappyPath ()
```

## Test model

```agda
open import TestModel
```

The formal specification tells you what the valid interactions are in
the protocol, but it doesn't tell you how to run tests. For this we define
a test model. In this case we want to test an implementation of Alice
and have the test framework act as Bob (and the network environment).

This is the part that we compile to Haskell with `agda2hs` and turn into
a QuickCheck Dynamic `StateModel`. For this we need to define the state
type (`EnvState`) modelling the state of the environment, the action type
(`Signal h`) of possible actions the environment can take, and the business
logic of the state transition system. The latter is wrapped up in the `step`
function

```agda
_ : EnvState → Signal h → Maybe (EnvState ×ʰ List Block)
_ = step
```

that encodes the `precondition`, `nextState`, and `postcondition` functions
from QuickCheck Dynamic. Note that in this example we know exactly what
blocks Alice should produce at any point in the protocol, so the postcondition
can be captured by the list of expected blocks produced by Alice.

The `Signal` type is parameterised by the honesty model (`@0` marks it to be erased
by `agda2hs`)

```agda
_ : (@0 h : Honesty) → Set
_ = Signal
```

which lets us distinguish honest and dishonest actions. For instance, the tests can
have Bob produce an incorrect block (wrong number, or in Alice's slot) if we are in
the `badBob` honesty model.

```agda
_ : Block → Signal badBob
_ = DishonestProduceBlock
```

### Erased evidence

A neat trick to make the proofs easier is to encode complex
conditionals in the "Haskell" code using proof-carrying data types. In
our case, there are three cases when we can honestly move to the next
slot: we are in slot 0, we are in Alice's slot, or we are in Bob's
slot and Bob has produced his block. We can encode this in the following
data type:

```agda
data WhenTick′ (@0 s : EnvState) : Set where
  GenesisTick      : @0 time s ≡ 0 → WhenTick′ s
  TickAfterBobSend : @0 SlotOf (time s) Bob
                   → @0 lastBlockTime s ≡ time s
                   → WhenTick′ s
  AliceSendAndTick : @0 SlotOf (time s) Alice → WhenTick′ s
  NoTick           : WhenTick′ s
```

When compiling to Haskell the proofs get erased and we're left with a
simple enumeration type. The `if_then_else_` function provided by
`agda2hs` provides evidence for the value of condition in the
respective branches which lets us supply the required proofs for each
case.

```agda
whenTick′ : (s : EnvState) → WhenTick′ s
whenTick′ s =
       if whoseSlot s == Bob && lastBlockTime s == time s
                               then TickAfterBobSend …… ……
  else if time s == 0          then GenesisTick ……
  else if whoseSlot s == Alice then AliceSendAndTick ……
  else NoTick
```

### Opaque functions

For simpler conditions defining a data type can be overkill. A more lightweight
approach is to wrap the condition in an opaque function. For instance, a dishonest
tick has only two preconditions:

```agda
opaque
  dishonestTickOk′ : EnvState → Bool
  dishonestTickOk′ s = whoseSlot s == Bob && lastBlockTime s <ʰ time s
```

For compilation to Haskell the `opaque` block has no effect, but when
doing the proofs Agda will not unfold `dishonestTickOk′` leading to
much cleaner looking goals. We can prove all the properties we need
for it in another `opaque` block explicitly allowing `unfolding` of
the function:

```agda
module _ {s : EnvState} (h : dishonestTickOk′ s ≡ True) where
  opaque
    unfolding dishonestTickOk′

    dishonestTickOk⇒bobSlot : SlotOf (time s) Bob
    dishonestTickOk⇒bobSlot = ……

    dishonestTickOk⇒noBlockThisSlot : lastBlockTime s < time s
    dishonestTickOk⇒noBlockThisSlot = ……
```

## Soundness proof

```agda
open import SoundnessProof
```

So far, we have not established any connection between the formal
specification and the test model. The property we care about is
*soundness*; informally, that any test sequence corresponds to a valid
trace in the formal specification. Formally we define

```agda
record Soundness′ (h : Honesty) (s : State) (endEnv : EnvState) (ms : List (Slot × Block)) : Set where
  field
    endState   : State
    invariant₀ : Invariant s
    invariant₁ : Invariant endState
    trace      : h ⊢ s ↝* endState
    envOk      : envState endState ≡ endEnv
    blocksOk   : aliceBlocks trace ≡ ms
```

where

```agda
_ : State → EnvState
_ = envState

_ : h ⊢ s₁ ↝* s₂ → List (Slot × Block)
_ = aliceBlocks
```

`Soundness h s endEnv bs` states that (in honesty model `h`), there is
a valid formal trace starting in state `s` and ending in a state
corresponding to the test model state `endEnv` in which Alice produces
the blocks `ms`.

The extra piece of machinery we need is the `Invariant` on the formal
state. The reason we need this is that the test model visits only
certain states, and soundness simply doesn't hold if we allow the
starting state to be completely arbitrary. For instance, in the test
model Alice and Bob have the same view of the world, but in the formal
specification they can disagree.

The main soundness theorem is

```agda
@0 _ : ∀ {env₁ bs} (s : State) (sig : Signal h)
     → Invariant s
     → step (envState s) sig ≡ Just (env₁ ,ʰ bs)
     → Soundness h s env₁ (map (clock s ,_) bs)
_ = soundness
```

and states that in a formal state `s`, if the `step` function succeeds
for an action `sig` and produces a next state `env₁` and expected
Alice blocks `bs`, then `env₁` and `bs` are sound. That is, there is a
corresponding formal trace in which Alice sends the blocks `bs` in the
current slot.

## Lifting honest soundness to full soundness

Tagging actions with the honesty model lets us write the soundness proof
compositionally. It is easy to prove that soundness in the `happyPath` model
implies soundness in any other honesty model (any trace in the `happyPath` is
also valid for other honesty models). This means that we can first prove

```agda
@0 _ : ∀ {env₁ bs} (s : State) (sig : Signal happyPath)
     → Invariant s
     → step (envState s) sig ≡ Just (env₁ ,ʰ bs)
     → Soundness happyPath s env₁ (map (clock s ,_) bs)
_ = honest-soundness
```

where we only need to worry about the honest action. And then appeal
to `honest-soundness` in the full soundness proof for the honest
action cases. Another important thing to note is that `honest-soundness`
is *stronger* than soundness for honest actions. We are saying that
for honest actions, there is a corresponding *honest* trace!
