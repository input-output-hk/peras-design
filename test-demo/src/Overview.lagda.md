
<!--
```agda
module Overview where

open import Agda.Builtin.List
open import Data.Empty using (⊥)
open import CommonTypes

postulate
  no-def : {A : Set} → A
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

The formal specification is defined in the `FormalSpec` module:

```agda
open import FormalSpec
```

and gives a small-step semantics for how the state of the world evolves during the
course of the protocol.

```agda
singleStep : h ⊢ s₀ ↝ s₁
manySteps  : h ⊢ s₀ ↝* s₁
```

<!--
```agda
singleStep = no-def
manySteps = no-def
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
model. For instance,

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

## Soundness proof

```agda
open import SoundnessProof
```
