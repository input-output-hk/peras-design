## 2024-02-26

### BB - Simulation experiment

Tracking and reporting of rollbacks has been added to `peras-iosim`:

1. Which nodes rolled back
2. At what slot this occurred
3. How many slots were rolled back
4. How many blocks were rolled back
5. The weight/length of the old and new chains

Voting propagation and graphics were also improved.

A reasonable set of [protocol parameters](peras-iosim/analyses/parameters-v1/protocol.yaml) and [network configuration](peras-iosim/analyses/parameters-v1/network.yaml) was set for a 100-node network with a mean committee size of 10. Here is the formula for setting the mean committee size:
$$
P_\text{lottery} = (1 - 1 / C)^(C / S)
$$
where $C$ is the mean committee size and $S$ is the total stake in the system.

Findings from the simulation runs highlight the impracticality of blindly running simulations with realistics parameters and then mining the data:

- The simulation results are strongly dependent upon the speed of diffusion of messages throught the network, so I high fidelity model for that is required.
- Both Peras and Praos are so stable that one would need very long simulations to observe forks of more than one or two blocks.
- Only in cases of very sparse connectivity or slow message diffusion are longer forks seen.
- Peras quickly stabilizes the chain at the first block or two in each round, so even longer forks typically never last beyond then.
- Hence, even for honest nodes, we need a mechanism to inject rare events such as multi-block forks, so that the effect of Peras can be studied efficiently.


### YH - Agda formalization

* Refactoring of the data model in Agda. This requires to adjust all dependent modules

## 2024-02-23

### BB - Metric and visualization

- Added observation of the whole tree of blocks to `peras-iosim`.
- Revised chain visualization to use tree data type of observed blocks.
- Design for computing metrics such as frequency of forks.

### AB - Rust Node

Writing custom setup file to automatically build the `peras-rust` projet with cargo, inspired by: https://github.com/CardanoSolutions/cardano-node/blob/release/8.1.2/cddl/Setup.hs
* Curiously it cannot find the `peras.h` header file even though I have added it in the `includeDirs`? -> the correct parameter to use is `includes` not `includeDirs`: https://cabal.readthedocs.io/en/3.4/cabal-package.html#pkg-field-includes
* Need move FFI code to the `library` component of the package, not the `test` component as it's the former that will depend on rUst code. This is debatable and perhaps I should stick to have the code in `test/`?

Need to restrict the scope of the state that's returned in the `Idle` message in order to avoid sneaking in implementation details from the Haskell node.
The fact that `Idle` is part of `OutEnvelope` type and therefore of the interface between the network simulator and the node is problematic. Or is it just an artefact stemming from the fact the `NodeModelSpec` is trying to test at too low a level for its own good?

Annoyingly default JSON serialisation provided by serde is not compatible with Aeson's :
```
Failed to deserialise received message ("{\"Idle\":{\"timestamp\":1708594079,\"source\":\"N1\",\"currentState\":{}}}"): Error in $: key "timestamp" not found
```

Trying to remove the `NodeState` from the `Idle` message but it does not work as expected: I use the `chainsSeen` in the `NetworkState` to store a map from nodes to preferred chain, but it's not updated for all nodes, eg. nodes which don't have downstream consumers won't send a `NewChain` message! I need to change the way the `NetworkState`'s  `chainsSeen` is updated: It's now updated in the `Idle`  handler _also_ and is a map from `NodeId` to `Chain`. This should not be a problem for plotting the end graph, but it will lose forks that get abandoned by a node in favor of a longer/better chain which might not be what we want.

After changes in the `Setup.hs` file, `cabal build peras-quickcheck` fails with:

```
% cabal build peras-quickcheck
Build profile: -w ghc-9.6.3 -O0
In order, the following will be built (use -v for more details):
 - peras-quickcheck-0.1.0.0 (lib:peras-quickcheck, test:peras-quickcheck-test) (configuration changed)
Warning: peras-quickcheck.cabal:55:1: Ignoring trailing fields after sections:
"extra-doc-files"
Configuring peras-quickcheck-0.1.0.0...
Error: setup: Missing dependency on a foreign library:
* Missing (or bad) C library: peras_rust
This problem can usually be solved by installing the system package that
provides this library (you may need the "-dev" version). If the library is
already installed but in a non-standard location then you can use the flags
--extra-include-dirs= and --extra-lib-dirs= to specify where it is.If the
library file does exist, it may contain errors that are caught by the C
compiler at the preprocessing stage. In this case you can re-run configure
with the verbosity flag -v3 to see the error messages.

Error: cabal: Failed to build peras-quickcheck-0.1.0.0. The failure occurred
during the configure step.
```

eg. it cannot find the DLL built by the `peras-rust` project.

Seems like the `confHook` of cabal checks the existence of the library
and fails if it does not exist ->
[this](https://blog.michivi.com/posts/2022-08-cabal-setup/#build-using-cargo-from-cabal)
blog post uses the `preconfigure` hook to ensure the Rust dependency
is built.

## 2024-02-22

### YH - Formalisation in Agda

* Added new property to block tree asserting that equivocal votes can not be added

### BB - Nix maintenance

- Fixed Nix derivations for Rust-Haskell linkages.
- Added quickcheck test to CI.

## 2024-02-21

### YH - Formalisation in Agda

* Refactored `CollisionFree` predicate and adjusted proof for the property that if the global state is collision-free, all previous state have been collision-free as well.
* Initial model of Peras in Agda (currently in separate branch)

### BB - Peras IOSim

- Implemented quorum logic in `PseudoPeras` protocol.
- Fixed orphan JSON instance for bytes.
- Main returns exit code explicitly.
- Cleaned up github CI.
- Activity and sequence diagrams.

### Meeting on ΔQ

ΔQ is not static, can be a function of load of the system for example, or adversarial behaviour, eg. one can Transform ΔQ by some function and parameterised. Could even extend operators if needed. If we can model an adversary as a ΔQ and then hypothesis about adversarial power, we can construct a new ΔQ with probabilistic alternative of being connected to an adversary or not.

PT did recent experimental work on how to represent probability distrubtions as [piecewise polynomials](https://github.com/DeltaQ-SD/dqsd-piecewise-poly), it needs a proper project to get momentum and concrete work. There's embryonic library representing [ΔQ algebra](https://github.com/DeltaQ-SD/dqsd-classes).

Cardano ΔQ model in Neil's head => being able to answer questions about the network behaviour

Several ways of using ΔQ:
* ΔQ distribution in the simulation
* Using for design/screening => ex-ante analysis, we have a 10-12 dimensional space => sampling for scenario
* Exposing infeasability => fail early

**Next steps**:
* Outcome model for Peras => whiteboarding session
* Plug in some estimates (uniform distribution)
* Build a model with a tool

### AB - Rust node

Fleshing out the interface of the `RustNode`, eg. how it handles messages.
* Need to understand how to pass ByteString to/from FFI, looking at: https://hackage.haskell.org/package/bytestring-0.12.1.0/docs/Data-ByteString-Internal.html#toForeignPtr which provides a way to pack/unpack a BS as a pointer to `Word8`, but a `ForeignPtr` cannot be passed to a C call
* Can use `withForeignPtr` to pass the data: https://hackage.haskell.org/package/base-4.18.1.0/docs/Foreign-ForeignPtr-Safe.html#t:withForeignPtr
* Now need to encode `InEnvelope` and `OutEnvelope` messages, going for JSON encoding for the moment but we said we would settle on CBOR. Need to find a good way to generate Rust types from Agda/Haskell types as these will be tedious to maintain in the long run


Writing the FFI functions on the Rust side, trying to build a library without any implementation
* How can I return a pointer to an opaque handle from Rust code?
* Obviously, borrow checker prevents from returning non-owned values and references: https://bryce.fisher-fleig.org/strategies-for-returning-references-in-rust/ so it's simply a matter of returning a `Box<T>` in the Rust code

Managed to call into the Rust library:
```
Peras.NodeModel
  Netsim Honest node
    mints blocks according to stakes [ ]thread '<unnamed>' panicked at src/lib.rs:10:5:
not implemented
note: run with `RUST_BACKTRACE=1` environment variable to display a backtrace
fatal runtime error: failed to initiate panic, error 5
```
Not sure how to handle the dependency between the peras-quickcheck and peras-rust library at build time :thinking:? The latter would need to be installed somewhere and accessible for use by the former, perhaps provide some extra flags at build time?

## 2024-02-20

### BB - Pseudo-Peras Protocol

Finished migrating the pseudo-Peras protocol from `random-forks` to `peras-iosim`.

- Updated `peras-iosim` to track voting.
- Implemented voting logic.
- Flagged potential ambiguities in Peras specification.
    - Clarification needed before implementing quorums.
- Revised visualization to display each vote.
- Added simulation execution to CI.

### AB - Implement Rust Node

Starting work to implement a simple honest Peras node in Rust that I can connect to the `NodeModel`. As usual, I would like to start from the top so I need to decouple the `NodeModel` from the actual implementation of a `Node` in Haskell, and then implement a Haskell driver connecting to a Rust node through `netsim`'s FFI.

Trying to generalise `runPropInIOSim` as used in the tests to an arbitrary runner, typechecker does not like the `forall s. PropertyM (IOSim s) a` type and cannot unify with ``Property m ()`.  Gave up trying to parameterise the `Actions -> Property` function with a monadic function, will just implement 2 functions in 2 different properties which will be just fine

Trying to introduce a `runPropInNetsim` function which would run in some `Netsim m` monad transformer. This does not work because there are still `MonadSTM` constraints on the `RunModel` for `NodeModel` so I first need to cut a proper interface that's independent of io-classes.

Scaffolded test runner in netsim and some simple Rust code, not linked still.
Looking at waht are the good practices for Cargo.lock on https://doc.rust-lang.org/cargo/guide/cargo-toml-vs-cargo-lock.html, seems like it's a good idea at first to commit it.

Revisiting Rust code and how to connect with Haskell code through C FFI. I probably don't need `netsim.h` directly to interact with a rust node through q-d. I should rather define my own interface, expose that and _use_ `netsim` under the hood to orchestrate the process, but there's no value in using `netsim-ffi` directly.

What I need is an interface that exposes these functions:

```
  , sendMessage :: InEnvelope -> m ()
  , receiveMessage :: m OutEnvelope
```

but for Rust

Got sidetracked while setting up peras-rust project as rust-analyser failed to run properly with LSP => Needed a `rustup update` which gave me rustc 1.76.0
Worked out a test runner that takes a `PropertyM (RunMonad IO) a` and runs actions, creating and destroying and internal node in the process. Given we are working in IO it's good hygiene to ensure that we don't leak resources when start/stop nodes living in Rust, so better wrap everything in some kind of simple bracket-style function

Reading again CAPI guide: https://downloads.haskell.org/ghc/9.0.1/docs/html/users_guide/exts/ffi.html?highlight=capiffi#extension-CApiFFI

### Pairing on Agda Network Model

Pairing on the Agda network model, we want to prove that `a ⊆ b -> a ⨉ a  ⊆ b ⨉ b`. It turned out to be surprisingly challenging, because of the functions and types used which did not lend themselves to nice reduction. YH finally found a solution later using some existing property of list membership:

```
   open import Data.List.Membership.Propositional.Properties

    ⊆→⊆-cartesianProduct : ∀ {a b} → a ⊆ₘ b → cartesianProduct a a ⊆ₘₓ cartesianProduct b b
    ⊆→⊆-cartesianProduct {a} a⊆b x =
      let x₁ , x₂ = ∈-cartesianProduct⁻ a a x
       in ∈-cartesianProduct⁺ (a⊆b x₁) (a⊆b x₂)
```

which replaced 20+ lines of complicated and unfinished proof by induction over various cases of `a` and `b`.

Made me think that perhaps we could use `postulate` or `trustMe` more
liberally at this stage of the code, to focus on types that matter. I
have the feeling that spending an afternoon to prove that `a ⊆ b -> (a
x a ) ⊆ (b x b)` is not the best use of our time, just like spending
time to define what a transaction is or implementing real VRF in the
prototype

## 2024-02-19

### BB - Nix CI and Development Environment

Fixed Nix CI and development environment to handle literate Agda and an Agda dependency on `agda2hs`.

### AB fixing Common Prefix

Trying to fix error in `NetworkModelSpec`, I first struggle with shrinking problems as I end up with traces without any `Tick` which is problematic as this means there won't be anything but a `Genesis` chain in all nodes.
* Fix it by adding a clause in the property, namely that if all nodes' chains are Genesis, this is fine as this means noone made progress. Anyhow, this is not the correct `commonPrefix` property.
* Tried to fiddle with `DynLogicModel` instance and function `restricted` which _restricts_ which value is generated with `anyAction` (I think).

Ended up with a chain that's supposed to fail the property but is apparently not, problem being that the `Show` instance yields something that's not `Read`able again:

```
err =
  [ Cons (Block{slotNumber = 49, creatorId = 7392 b2bd2853, includedVotes = (), leadershipProof = f2a6ab5f8122, payload = [], signature = 06 f34b7da9fd}) (Cons (Block{slotNumber = 44, creatorId = ece20dec9edc, includedVotes = (), leadershipProof = 0 faf57e3c126, payload = [], signature = c63cff5266ee}) Genesis)
  , Cons (Block{slotNumber = 44, creatorId = ece20dec9edc, includedVotes = (), leadershipProof = 0 faf57e3c126, payload = [], signature = c63cff5266ee}) Genesis
  , Cons (Block{slotNumber = 49, creatorId = 7392 b2bd2853, includedVotes = (), leadershipProof = f2a6ab5f8122, payload = [], signature = 06 f34b7da9fd}) (Cons (Block{slotNumber = 44, creatorId = ece20dec9edc, includedVotes = (), leadershipProof = 0 faf57e3c126, payload = [], signature = c63cff5266ee}) Genesis)
  , Cons (Block{slotNumber = 49, creatorId = 7392 b2bd2853, includedVotes = (), leadershipProof = f2a6ab5f8122, payload = [], signature = 06 f34b7da9fd}) (Cons (Block{slotNumber = 44, creatorId = ece20dec9edc, includedVotes = (), leadershipProof = 0 faf57e3c126, payload = [], signature = c63cff5266ee}) Genesis)
  , Cons (Block{slotNumber = 49, creatorId = 7392 b2bd2853, includedVotes = (), leadershipProof = f2a6ab5f8122, payload = [], signature = 06 f34b7da9fd}) (Cons (Block{slotNumber = 44, creatorId = ece20dec9edc, includedVotes = (), leadershipProof = 0 faf57e3c126, payload = [], signature = c63cff5266ee}) Genesis)
  , Cons (Block{slotNumber = 44, creatorId = ece20dec9edc, includedVotes = (), leadershipProof = 0 faf57e3c126, payload = [], signature = c63cff5266ee}) Genesis
  , Cons (Block{slotNumber = 49, creatorId = 7392 b2bd2853, includedVotes = (), leadershipProof = f2a6ab5f8122, payload = [], signature = 06 f34b7da9fd}) (Cons (Block{slotNumber = 44, creatorId = ece20dec9edc, includedVotes = (), leadershipProof = 0 faf57e3c126, payload = [], signature = c63cff5266ee}) Genesis)
  , Cons (Block{slotNumber = 49, creatorId = 7392 b2bd2853, includedVotes = (), leadershipProof = f2a6ab5f8122, payload = [], signature = 06 f34b7da9fd}) (Cons (Block{slotNumber = 44, creatorId = ece20dec9edc, includedVotes = (), leadershipProof = 0 faf57e3c126, payload = [], signature = c63cff5266ee}) Genesis)
  , Cons (Block{slotNumber = 49, creatorId = 7392 b2bd2853, includedVotes = (), leadershipProof = f2a6ab5f8122, payload = [], signature = 06 f34b7da9fd}) (Cons (Block{slotNumber = 44, creatorId = ece20dec9edc, includedVotes = (), leadershipProof = 0 faf57e3c126, payload = [], signature = c63cff5266ee}) Genesis)
  , Cons (Block{slotNumber = 49, creatorId = 7392 b2bd2853, includedVotes = (), leadershipProof = f2a6ab5f8122, payload = [], signature = 06 f34b7da9fd}) (Cons (Block{slotNumber = 44, creatorId = ece20dec9edc, includedVotes = (), leadershipProof = 0 faf57e3c126, payload = [], signature = c63cff5266ee}) Genesis)
  ]
```

First issue: There are missing double-quotes in the `Show` instance for `Bytes`

Trying to have lawful Read/Show instance for Chain in order to
investigate with copy/paste why the sample chains do not validate
`commonPrefix` property, got hit by a weird error when trying to
`derive via Bytes` TX instances:

```
src/Peras/Orphans.hs:221:1: error: [GHC-18872]
    • Couldn't match representation of type ‘BS8.ByteString’
                               with that of ‘Tx’
        arising from a use of ‘ghc-prim-0.10.0:GHC.Prim.coerce’
    • In the expression:
        ghc-prim-0.10.0:GHC.Prim.coerce
          @(Int -> ReadS Bytes) @(Int -> ReadS Tx) (readsPrec @Bytes)
      In an equation for ‘readsPrec’:
          readsPrec
            = ghc-prim-0.10.0:GHC.Prim.coerce
                @(Int -> ReadS Bytes) @(Int -> ReadS Tx) (readsPrec @Bytes)
      When typechecking the code for ‘readsPrec’
        in a derived instance for ‘Read Tx’:
        To see the code I am typechecking, use -ddump-deriv
      In the instance declaration for ‘Read Tx’
    |
221 | deriving via Bytes instance Read Tx
    | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

Found the issue: `Tx` was declared as `data Tx` which breaks the representation equivalence of `newtype`s.
* Need to add an annotation on Agda code to ensure it produces a `newtype`

Looks like the `IsString` instance for some types are invalid!
* Finally got to the bottom of the problem: The `fromString` function was delegating to `read` but this is wrong as `read` for a `String` would expect double-quotes but `fromSTring` would be given directly the `String` value _without_ the double-quotes!

Getting back to the main problem, there's definitely something wrong with my `commonPrefix` function as demonstrated by some unit tests I copy/pasted from the failures observed in `NetworkModelSpec`!

Fixed the `commonPrefix` computation: The Agda code was not recursing when the 2 values were inequal, which was a remainder of the previous Haskell computation where the prefix was computed by first `reverse`ing the block list :facepalm:

## 2024-02-16

### BB - Odds & Ends

- Added CLI interface to `peras_topology`.
- Refactored and cleanly isolated random-number generation in `peras-iosim`.

### YH code extraction for property based tests

* For extracting properties from Agda to Haskell we can use as similar type as the `Equal` type from the agda2hs examples. The constructor for `Equal` takes a pair of items and a proof that those are equal. When extracting to Haskell the proof gets erased. We can use this idea for extracting properties to be used with quick-check.

```agda
prop-genesis-in-slot0 : ∀ {c : Chain} → (v : ValidChain c) → slot (last c) ≡ 0
prop-genesis-in-slot0 = ...

propGenesisInSlot0 : ∀ (c : Chain) → (@0 v : ValidChain c) → Equal ℕ
propGenesisInSlot0 c v = MkEqual (slot (last c) , 0) (prop-genesis-in-slot0 v)
```

### Notes on serialization

Serialisation from Agda
* serde can mimick Aeson serialisation -> configuration on the rust side
* serialisation should be CBOR
* should we start from the CDDL or the code? Probably want to be both, as long as we respect the specification

### AB - commonPrefix in Agda

Trying again to implement `commonPrefix` in Agda, this time depending on Haskell equality instances
* need to add `--erasure` in the agda-lib as a flag to be able to import agda2hs

Looks like the Agda version of `commonPrefix` does not work as expected, investigating what's wrong...
It's an interesting exercise as I would like to write properties about that code, eg. something like:

```
commonPrefixEq : {t : Set } -> ⦃ eqt : Eq t ⦄ -> (c₁ c₂ : Chain t) ->  (c₁ ≡ c₂) -> (commonPrefix (c₁ ∷ c₂ ∷ []) ≡ c₁)
commonPrefixEq = {!!}
```

where c1 and c2 would be `Arbitrary` on the Haskell side.

Here is the property I write in QC:

```
spec :: Spec
spec =
  prop "(c₁ ≡ c₂) -> (commonPrefix (c₁ ∷ c₂ ∷ []) ≡ c₁)" propCommonPrefixSelf

propCommonPrefixSelf :: Property
propCommonPrefixSelf =
  forAllShrink arbitrary shrink $ \c ->
    commonPrefix @() [c, c] == c
```


I am not too far but still stuck with scope of type varilables in  `where` clause, don't know how to generate the needed `forall t. ` for nested definitinos in `where` clause. Alternatively, erasing the type ascriptions could work :thinking:
* Found the issue after adding some property to check `asChain (asList c) == c` which would also be great to guarantee in Agda!
* There was an additional `reverse` when returning the list of blocks prefix which did not make sense!

Now I have an interesting error in the properties!

```
Test suite quickcheck-model-test: RUNNING...

Peras.NetworkModel
  Chain progress [✘]

Failures:

  test/Peras/NetworkModelSpec.hs:40:33:
  1) Peras.NetworkModel Chain progress
       Falsified (after 4 tests and 3 shrinks):
         do action $ ChainsHaveCommonPrefix [var3,var4,var5,var6,var7,var8,var9,var10,var11,var12]
            pure ()

         FailureEvaluation Variable var12 is not bound!
         CallStack (from HasCallStack):
           error, called at src/Test/QuickCheck/StateModel.hs:252:14 in qckchck-dynmc-3.3.1-99b3f6b4:Test.QuickCheck.StateModel
         Exception thrown while showing test case:
           Variable var12 is not bound!
           CallStack (from HasCallStack):
             error, called at src/Test/QuickCheck/StateModel.hs:252:14 in qckchck-dynmc-3.3.1-99b3f6b4:Test.QuickCheck.StateModel
```

This error was caused by the lack `HasVariables` instance to properly shrink, now I have another error:
```
Peras.NetworkModel
  Chain progress [✘]

Failures:

  test/Peras/NetworkModelSpec.hs:40:33:
  1) Peras.NetworkModel Chain progress
       Falsified (after 19 tests and 8 shrinks):
         do var62 <- action $ ObserveBestChain N1
            var63 <- action $ ObserveBestChain N2
            var64 <- action $ ObserveBestChain N3
            var65 <- action $ ObserveBestChain N4
            var66 <- action $ ObserveBestChain N5
            var67 <- action $ ObserveBestChain N6
            var68 <- action $ ObserveBestChain N7
            var69 <- action $ ObserveBestChain N8
            var70 <- action $ ObserveBestChain N9
            var71 <- action $ ObserveBestChain N10
            action $ ChainsHaveCommonPrefix [var62,var63,var64,var65,var66,var67,var68,var69,var70,var71]
            pure ()

         FailureEvaluation Map.!: given key is not an element in the map
         CallStack (from HasCallStack):
           error, called at libraries/containers/containers/src/Data/Map/Internal.hs:617:17 in containers-0.6.7:Data.Map.Internal
         Exception thrown while showing test case:
           Map.!: given key is not an element in the map
           CallStack (from HasCallStack):
             error, called at libraries/containers/containers/src/Data/Map/Internal.hs:617:17 in containers-0.6.7:Data.Map.Internal

```

Which seems to mean the nodes are not available to observe. Given the number of variables involved the trace took a while to shrink!

>>>>>>> ea736c0 (Updated Logbook)
## 2024-02-15

### BB - Rust-based generator of randomized network topologies

The [peras\_topology](peras_topology/ReadMe.md) Rust crate contains a rudimentary implementation of a randomized network generator, like that in the `peras-iosim` Haskell package.
- Reads YAML-formatted `Parameters` describing the network.
- Outputs a JSON file with the `Topology`.
- The serialization formats are compatible with `peras-iosim`.
- Added build of `peras_topology` to the CI.

This raises several issues related to Rust:
1. How do we want to organize our Rust crate structure?
2. Should we try to generate the Rust types directly from Agda?
    - How mature is IOG's work on `agda2rust`?
3. Which tools do we want to code in Rust vs Haskell?
4. Is the default `rustfmt` sufficient as a code-style standard, for the time being?

### YH working on code extraction using agda2hs

* In the agda2hs documentation there are good examples guiding on how to extract properties (i.e. equality) from Agda to Haskell: https://github.com/agda/agda2hs/blob/02f495cdbc45874749665917f8a3f0bd7db5a158/docs/source/features.md?plain=1#L353-L410
* In agda2hs there is the module `Haskell.Law` providing helpers for that
* Currently I'm using a simple toy chain for experimenting with code extraction

### ΔQ library

Did some brushing up of PNSol's
[DeltaQ](https://github.com/DeltaQ-SD/pnsol-deltaq-clone) library as
it's easier for me to understand things once they are written down as
code. Would be interesting to have a look at how they manage the
probability distributions and integrate that in our network modelling.

### AB on `NetworkModel`ing

Shaving some yaks while trying to implement "common prefix"  property for the `NetworkModel`.
I implemented a couple of functions for `Chain` types in Agda, got sidetracked into looking for shortcuts to do some goal-driven development and could not find one to fill in the body of a function given its type.
* Wrote `asChain` and `asList` functions to convert between `Chain` and `[Block]` as the two types are isomorphic.
* I would like to implement all pure functions related to chain manipulation in Agda. Going to not waste time right now to do that but something to keep in mind

There is something mind boggling with the `runNetwork` function that mesmerizes me!
I can't find a good way to start cutting it in pieces to be able to separate the step, stop and observation functions!

_(few hours later)_

Managed to connect the network model to the network runner at least for the step part, now need to retrieve the preferred chain from each node.
The problem is that nodes' state is pretty much opaque, eg. it's initialised and then updated in a separate thread, need a new kind of message ?

### Pairing on NetworkModel's last mile

Thinking about time, we realise that time management and messages delivery are tricky.
The `Network` code  ransforms individual delays of messages into a statistical delivery of messages which is currently very simple, eg. 300ms delay over a 1s slot => 30% of messages got delayed to next slot.

This seems to be a nicelink to ΔQ formalism because we could put a (partial) CDF as a function to manager the dealys of messages and then use q-d to check the behaviour of the model under various assumptions.
* no need to reinvent the wheel, we could leverage their formalism for handling statistical distributions

We have some nice monitoring in place to report what the chain look like after a quickcheck test run. Here is a report for 10 samples with 1/20 active slot coefficient which demonstrates the observed behaviour is consistent with what we expect from Praos chain:

```
Peras.NetworkModel
  Chain progress [✔]
    +++ OK, passed 10 tests.

    Action polarity (360 in total):
    100.0% +

    Actions (360 in total):
    64.7% +Tick
    32.5% +ObserveBestChain
     2.8% +ChainsHaveCommonPrefix

    Prefix density (10 in total):
    50% <= 6%
    40% <= 5%
    10% <= 10%

    Prefix length (10 in total):
    70% <= 100
    20% <= 400
    10% <= 300
```

Struggling again to convert the `commonPrefix` function as an Agda function, forgot that scope of implicit variables comes from pattern matching on the LHS.
Now need to understand equality...

Seems like porting my simple prefix function to Agda is a non-trivial effort:
* Agda does not have builtin structural equality (?) nor typeclasses so one needs to define equality for specific types
* There is a decidable equality provided by the builtins but it's not erased. According to Orestis one needs _erased decidability which is like https://github.com/agda/agda2hs/blob/master/lib/Haskell/Extra/Dec.agda
* it's a bit sad as this function seems simple enough :(

## 2024-02-14

### BB on testing statistical properties

1. Ran and statistically analyzed an experiment [using this Jupyter notebook](peras-iosim/analyses/block-production/ReadMe.ipynb) to verify the correctness of slot leadership and block production for the `PseudoPraos` protocol.
2. Research QuickCheck-based approaches for handling approximate equality and statistical properties.
    - There don't seem to be special-purpose libraries of this.
    - QuickCheck and its extension provide some control over coverage and sampling, but this doesn't address the fundamental problem of determining when a failure is a valid statistical outlier vs an error.
3. Revised QuickCheck test for block production to use a three-sigma confidence interval. Eventually, we'll need to make the sigma level tunable.

Other revisions to `peras-iosim`:
- Added an explicit parameter for total stake to `Peras.IOSim.Simulate.Types.Parameters`.
- Changed serialization of `Peras.Chain` so that it doesn't keeply next JSON, since that causes most JSON parsers to crash for long chains.

### AB on Network Modeling

Reading about Rust's FFI: https://www.michaelfbryan.com/rust-ffi-guide/setting_up.html
* `ByteBuffer` is a type exported from `ffi_support` library which means foreign code will need to link to this library too, which is annoying.
* There's a [PR #9](https://github.com/input-output-hk/ce-netsim/pull/9) baking to build a proper FFI library

Looking at `runNetwork` code to understand how I can instrument it for inclusion in a quickcheck model. `runNetwork` is opaque, eg. it runs a predefined network until some slot is reached.

### AB on ΔQ

Trying to (again) understand what ΔQ is and how to use it, found [this paper](https://www.broadband-forum.org/pdfs/mr-452.2-1-0-0.pdf) on PnSOL's website that sheds some light on it: The idea is to relate SLAs to _Quantitative Timeliness Attenuation_ which is then expressed as an "improper CDF" incorporating expectations about delivery time and loss probability. For example, one can say:
* 50% delivered under 100ms
* 95% delivered under 200ms
* 2% packet loss

This defines a crude distribution function with steps and then ΔQ actual measurements can be done to assess whethere these are met.

Also, individual components' ΔQ profiles can be composed to yield global measure.

#### Original paper

Going through the first sections of https://www.mdpi.com/2073-431X/11/3/45 to understand how it's been applied to Cardano block diffusion

Problem is stated as:

> Starting from blockchain node A, what is the probability distribution of the time taken for a block to reach a different node Z when A and Z are picked at random from the graph?

Then the next paragraph says the "the graph is random with some
limited node degree N" which seems to imply we assume a _random
graph_. But is it really the case? Is the graph really a _random
graph_ (with all the properties as defined by Barabasi et al.) or is
it rather a _power law graph_? What would that change?

Delay distributions can be combined either sequentially (through a convolution?):

Definition on continuous domain is:
$$
(f*g)(t):=\int _{-\infty }^{\infty }f(t-\tau )g(\tau )\,d\tau.
$$

which translates to finite domains as:
$$
h(n) = (f \star g)(n) = \Sigma_{i=-\inf}^{\inf} f(n−i)g(i).
$$

Found this Algorithm in 1D (which is what's interesting for us): https://www.algorithm-archive.org/contents/convolutions/1d/1d.html

#### Refinement & alternatives exploration

ΔQ can be applied to refine steps in a process, but also explore alternative designs:
* Impact of a distribution of path length on block diffusion time
* Impact of header/body split on overall diffusion

For example:

> For the ‘Near’ peers shipping a 64 kB block, this means an intensity of 42.7 Mb/s (8 × 64000/(0.024 − 0.012))

* 0.024 = time to ship a full block between 2 nodes in the same DC
* 0.012 = latency between 2 nodes in same DC (RTT)
* 8 = number of nodes from which we download full block ?
* 64000 = size of a block

Not sure what does this number means? Bandwidth lower-bound of a node?

#### Comparison between ΔQ analysis and simulation

Aims at showing that simulation is intractable as it would need too many samples to provide similar information
* Feeling that the argument about the number of graphs to generate is a strawman argument. There's a huge amount of them of course, but you don't really care to cover those, you only want to ensure your sample has some variety while staying consistent with the expected characteristics of the network.
* you can reduce the search space to _relevant_ graphs and leave pathological ones aside

#### Semantics of ΔQ

Δ0 is a partial CDF, eg. a CDF with some cutoff before 1 to represent failures

```
ΔQ(Δ0) = Δ0
ΔQ(A -> B) = ΔQ(A) * ΔQ(B) -- convolution
ΔQ(A // B) = p(A)ΔQ(A) + p(B)ΔQ(B) -- alternative w/ proba
ΔQ(∃(A | B)) = ΔQ(A) + ΔQ(B) - ΔQ(A) x ΔQ(B) -- exclusive one outcome
ΔQ(∀(A | B)) = ΔQ(A) x ΔQ(B) -- all outcomes
```

How can we apply ΔQ to the problem of finality in a blockchain?
We first need to define finality and settlement: It's the time it takes for a transaction to be considered _Final_ by one node? By all nodes?

A survey paper about networking in cryptocurrencies: https://arxiv.org/pdf/2008.08412.pdf

## 2024-02-13

### YH - Formal specification

- Introduced `CollisionFree` predicate
- Refactored relation on global state
- Proofing property that when there is collision-free state all previous states have been collision-free as well

### BB - IOSim enhancements

- Improved faithfulness of slot-leader selection.
- Refactored to use `MonadRandom` throughout.

### AB - Model-Based Testing a node

Trying to express block production property as a ratio of number of blocks over current slot for a single node, got a failed test:

```
  2) Peras.NodeModel Honest node mints blocks according to stakes
       Assertion failed (after 5 tests):
         do var0 <- action $ Tick 45
            var1 <- action $ Tick 73
            var2 <- action $ Tick 35
            var3 <- action $ Tick 19
            action $ ForgedBlocksRespectSchedule [var3,var2,var1,var0]
            pure ()

         trace:

         Produced 4 blocks in 172 slots
```

* First, the good news is that the test works and we actually produce blocks and can check those
* Second, the condition is an equality but it should be a bounde interval c
* I like the fact the failure produces a useful trace, but in this case it does not shrink

Tweaking the property checked, taking into account the actual stake of the node which is randomly generated from max stake.
I am surprised by the discrepancy between what I compute as expected and what's actually produced:

```
 Assertion failed (after 2 tests):
   do var0 <- action $ Tick 85
      action $ ForgedBlocksRespectSchedule [var0]
      pure ()

   trace:

   Actual: 17, Expected:  7.769
   Stake: 457 % 500, active slots:  0.1, Slot: 85
```

Trying to scale the number of slots in each action to see if this has an impact on the difference innumber of blocks produced

Looks like the discrepancy is not very surprising as the formula for slot learder ship is currently computed as:

```
  let expectedStake = fromIntegral $ peerCount * maximumStake `div` 2
      pSlotLottery = 1 - (1 - activeSlotCoefficient') ** (1 / expectedStake)
      p = 1 - (1 - pSlotLottery) ^ currency
   in (<= p) `first` uniformR (0, 1) gen
```

### Ensemble discussion

We need to start Experimenting with adversarial node/network behaviour, to be able to mix honest nodes + various types of malicious node in a single test run and simulation. Big question is: What it means to be adversarial? How does it impact the chain and the network? Perhaps a simple and generic answer is that dishonest nodes are the ones producing "malicious" blocks, whose content we do not really care about?

:right_arrow: We want to mark blocks produced by adversarial nodes and check how much such blocks the chain ultimately contains

This leads to the interesting question of whether or not the mempool should be out of scope? We think so but perhaps there are expectations we are not aware of?

### Network Simulator

* Tools to simulate and emulate protocols
* 2 different multiplexers -> green vs. native threads (tokio)
  * sockets/handles for sending/receiving messages
  * implement policies/latencies
  * in Cardano -> nodes come slower to each other

* Alan -> working on Simplex, no imminent consumer of it
  * Fast BFT/HotStuff/Simplex -> need some kind of network simiulator
  * have something, but not as complete as what netsim aims
  * Rust/Scala

* easy to port and use Wasm -> native threads converted to JS
* handling time? -> global clock
* metrics? => latency, bandwidth

## 2024-02-12

### BB - IOSim enhancements

1. Enabled optional profiling of Haskell code, via Nix.
2. Fixed memory leak cause by bug in `io-classes-1.3.1.0`.
3. Finished provisional algorithm for routing.
4. Improved visualization of chain forking.

### BB - Haskell package maintenance

1. Separated Haskell files generated by `agda2hs` to separate folders from the Agda source, in the [peras-hs](peras-hs/) package.
2. Relocated `Peras.Ophans` from `peras-iosim` to `peras-hs`.
3. Added Haskell package builds to CI.
4. Added formatting pre-commit check for Haskell and Nix files.
5. Turned on `StrictData` language extension for `peras-hs` and `peras-iosim`.
6. Temporarily disabled `peras-quickcheck` in [cabal.project](cabal.project) and [.github/workflows/ci.yaml](.github/workflows/ci.yaml), due to missing `netsim` library.

### AB - Connecting quickcheck & Rust

Having "fun" calling Rust library from Haskell through FFI.
* Some interesting article on how to build Haskell + Rust together: https://blog.michivi.com/posts/2022-08-cabal-setup/
* I am trying to understand how to write correct capi calls from documentation: https://wiki.haskell.org/Foreign_Function_Interface#Generalities
* Defining additional header and library directories for cabal to find netsim stuff: https://cabal.readthedocs.io/en/3.4/cabal-project.html#foreign-function-interface-options
* Another blog post about C++ FFI https://topikettunen.com/blog/haskell-cpp-ffi/

Managed to use `dummyFFI` from `netsim` library which is just an echo,
but it definitely works. Now need to better understand how the library
is supposed to work, possibly implementing some very simple node.

### AB - Connecting Quickcheck & peras-iosim

* Split `peras-quickcheck`'s model in 2, one `NetworkModel` and one `NodeModel` which should respectively assert properties of a whole network, and of a single node
* Run model test against a single [Peras.IOSim.Node](https://github.com/input-output-hk/peras-design/blob/52a6b882d2363148f6fd1cc430d6054a5f5215eb/peras-iosim/src/Peras/IOSim/Node.hs#L73) with the goal of checking the node respects leader's schedule which is a very basic property but not so simple to express and useful to check
  * Property is not implemented, I would like to express it as some expected number of blocks produced during a time interfval
  * Had some discussoing with John Hughes on how to express that in DL: The number of blocks is not directly accessible as it's an _output_ of the SUT and only accessible to the DL as `Var`iables
  * Currently needs to be done as an `action` with a `postcondition` that can resolve the variables, but it might be possible and useful to extend DL to be able to resolve variables as an expression in order to avoid having to modify the model only for the purpose of observing some computation result

### Team Discussion

The quality of the Network simulation is important
* We want both an idealised network, statistical regularities, and a faitful model of the actual network -> realistically inferred from existing network
* Network modelling is a big risk area for the project as its quality and the ability to run simulations and experiments will be critical to produce meaningful and useful results
* => meet netsim implementation team to better align on goals and where we want to go

* Take the Agda types as is + incorporate in the simulation
  * How faithful is the traduction?

* **Goal of the week**:
  * Express _knowledge propagation_ property in Agda?
  * Perhaps leader schedule respect would be an even simpler property to state and test?
  * Translate to Haskell
  * Run q-d over implementation in both Haskell and Rust

## 2024-02-10

### BB - Peras IOSim

Mostly finished refactoring of `peras-iosim` to incorporate functionality of `random-forks`.

- Additions and changes
    1. Various refactorings.
    2. Implemented a Praos-like protocol.
    3. Command-line options.
    4. YAML input and JSON output.
    5. Visualization.
- Next steps
    - Diagnose and fix memory leak.
    - Migrate Peras algorithm from `random-forks`.
    - Implement logging via a suitable logging monad.

## 2024-02-09

### BB - Peras IOSim

Continued refactoring of `peras-iosim` to incorporate functionality of `random-forks`.

- Additions and changes
    1. Integrated `peras-iosim` with Agda-derived types.
    2. Implemented orphan instances.
    3. Implemented JSON serialization.
    4. Aligned usage of Agda types.
    5. Implemented network routing.
    6. Implemented random-network generation.
- Next steps
    - Read YAML files as input.
    - Migrate Praos algorithm from `random-forks`.
    - Migrate Peras algorithm from `random-forks`.
    - Implement logging via a suitable logging monad.
    - Migrate visualization from `random-forks`.

### YH - Model in Agda

* Moved the initial implementation of the semantics into a separate module: [SmallStep.agda](src/Peras/SmallStep.agda)
* Similar for the proofs: [SmallStep/Propeties.agda](src/Peras/SmallStep/Propeties.agda)
* The small-step semantics implement closely the semantics proposed in the PoS-NSB paper

### AB - Quickcheck Model

Adding self-hosted runner on my Mac OS machine for Peras in order to benefit from caching.
Configuration is straightforward but unfortunately it's not possibler to share runners between repositories on a case-by-case basis: They have to be defined as organisation-level runners and then can be shared.

* Initial build time is 12m57s
* Rebuild took 1m9s :tada:

Got a first stab at `ModelSpec` compiling and "running", trying to express chain progress property as:

```
chainProgress :: DL Network ()
chainProgress = do
  anyActions_
  getModelStateDL >>= \Network{nodeIds} -> do
    bestChains <- forM nodeIds (action . ObserveBestChain)
    let (settled, unsettled) = commonPrefix bestChains
    DL.assert "" $
      all (((< 42) . length) . asList) unsettled
        && not (null (asList settled))
```

Need to look at the actual definition in the Praos or PoS-NB paper perhaps...

One issue is that this can't work as is: an `action SomeAction` where `SomeAction :: Action MyState a` return `Var a` which is just a symbolic reference to a value and not the value itself.
It actually does not make sense for the Model to attempt to track all the chains produced, it's actually simpler to just track the elapsed time (slots) and compute how long the common prefix should be

Modified model to check observation on the `postcondition` of the `RunModel` but now the test loops!
* Sprinkling traces does not reveal anything of interest, seems like it's stuck somewhere between computing next state and performing the action on the run model :thinking:
* Struggling to understand why my q-d run is hanging, trying to run it within `IO` instead of `IOSim` but the type tetris is annoying...

Managed to write a function to run actions in IO, inspired by [runPropertyStateT](https://github.com/input-output-hk/quickcheck-dynamic/blob/c309099aa30333a34d3f70ad7acc87d033dd5cdc/quickcheck-dynamic/src/Test/QuickCheck/Extras.hs#L7)
* I don't understand much of what I am doing here as it's really unclear what's going on in the `PropertyM`, but it compiles.
* It still hangs however -> compiling with profiling to be able to dump some traces statistics

Thanks to profiling I found out where my error was :facepalm: : the `baseNodes` function uses `unfoldr` to generate node ids and then `take 10`, but then it generates node ids using `unfoldr` again without any stopping condition which of course never terminates

### Team sync

Discussing whether or not to check-in generated code?
* Checking in would be useful and then have some check in place in the CI
* it's probably ok either way now

What about Praos Genesis?
* could have impact on our work as the criterion for chain extension is different
* also has impact on the networking stuff

First simulation should focus on committee size -> most important number in the system, needs intuition on what's the right value

## 2024-02-08

### BB - Nix, Agda, and Haskell housekeeping

1. Reconciled Haskell package dependencies.
2. Switched to IOGX-style flake.
3. Included pre-built Agda standard library.
4. Added `nix build .#peras` for building the Peras library in Agda and Haskell.
5. Nix-based CI.
6. Cabal file for Haskell code generated by `agda2hs`.

*Issue:* the Nix-based CI test takes ~28 minutes, but this will be far faster when caching is enabled.

### Pairing session - Agda modelling of messages

Some resources on agda2hs:
  * What's  the best practice for generating code from Agda?
  * Haskell.Prelude contains Agda exports suitable for Haskell
  * agda2hs tutorial: https://agda.github.io/agda2hs/tutorials.html and [paper](https://dl.acm.org/doi/pdf/10.1145/3546189.3549920)
  * The most elaborate project so far is [agda-core](https://github.com/jespercockx/agda-core/), which itself relies on a Agda/Haskell library for well-scoped syntax (https://github.com/jespercockx/scope).

Together with AB we started to work on the extraction of the model from Agda to Haskell using `agda2hs`
* The tool requires to put the `AGDA2HS` pragma for all data types that are exported
* We renamed constructors to be upper case and type parameters to be lower case as required in Haskell
* Data types that used the standard library had to be adjusted. For example we changed the `Block` data type that used `set` to a parameterized data type:
```agda
open import Data.Tree.AVL.Sets renaming (⟨Set⟩ to set)

...

record Block (t : Set) : Set where
  field slotNumber : Slot
        blockHeight : Word64
        creatorId : PartyId
        parentBlock : Hash
        includedVotes : t
        leadershipProof : LeadershipProof
        payload : List Tx
        signature : Signature

Block⁺ = Block (set HashO)
```
* The import of `Data.ByteString` in Haskell is possible using the `FOREIGN` pragma

We then try to parameterise the `Block` type on the agda side to be able to inject whatever we want as concrete type, but agda2hs does not like our kind for the parameter -> needs to be a `Set`, or a simple type-level expression.
There should be a way to map types/imports from Agda to HS?

We have some kind of strategy to go from Agda, sticking to "simple" types wherever we need it but it's not entirely satisfactory as we are losing information in the process
Then got an interesting discussion with some other agda2hs user:

> I found that if I had something in Agda that couldn't turn into
> Haskell then I was going to wrong way - you need to figure out what
> it looks like in Haskell and then try to handle that in Agda, rather
> than fitting the Haskell to the Agda, if you see what I mean?
>
> At least you are doing proofs over the Haskell code, not an abstract
> model that may or may not relate to the real implementation. Agda2hs
> seems to come with a bunch of Haskell.Prelude related modules that
> mirror the Haskell modules. For anything bespoke I just used
> postulate (and, if I had kept going, would have re-implemented them
> as "Haskell in Agda")
>
> I would suggest that agda2hs should be renamed to hsInAgda
> :slightly_smiling_face: I found like that agda2hs keeps almost
> exactly what I wrote in the .agda file when it converts. I also
> found that you could do nice things with syntax declarations if you
> want to use unicode in the agda file though. So I defined functions
> with long Haskell names but could give them unicode
> symbols. Wherever I used the unicode symbol subsequently agda2hs
> dropped in the long name.

## 2024-02-07

### Team session

Q: How does Praos Security model relates to PoS-NB paper's model? Seems like the latter is simpler, has stronger assumptions thus leading to weaker guarantees

Some high-level questions being discussed:
* What are the next steps on simulations?
* Could be good to have "foundation" code in Agda and then evaluates simulation tools using always the same code in order to ensure interoperability
* JSON serialisation is hard in Agda, need to be done at generated code level
* Write down the types together?

What is a good property to express?
* How to express finality?
* What are block diffusion properties and their impact on the finality => impact on nr. of peers on speed of finality

Exploring simulation tools:
* discrete event simulators?
* not too much concerned about scale?
* could leverage https://github.com/input-output-hk/hydra-sim

Some hypothesis about Peras protocol itself:
* if $A$ is too low, cooldown periods happen to often
* Later discussion w/ researchers tell us $A$ is not so important because the protocol is geared towards optimistic cases, so it can be small

Cool idea we played a bit with: Have a visualisation up and running as a demo so that people can tweak the parameters to see how the protocol is behaving. Then we can gamify it, asking people to share their favorite parameters set and run more thorough simulations with those parameters. It will also be a nice way to engage with the community and have apeople understand the benefits and tradeoffs of this new protocol extension.

Code generation:
* Trying to write a simple model of the message types in Agda and generate HS code
* Default generator yields unreadable and encoded haskell -> not super
  useful for embedding in QC, so we'd rather want [agda2hs](https://github.com/agda/agda2hs) which generates pretty readable code

Possible experiment:
* build a slurp node
* Run the node in various datacenters connected to other peers
* store the chain following data -> reconstruct the progress of the chain at vartious point in time
* Is this not what the CF is doing with their Cardano network monitoring project? => ask for more information

### BB - Peras simulation using `IOSim`

- Began work on `IOSim`-based Peras simulator.
    - A couple of days from now, this will replace the `random-forks` model.
    - Based on ideas from Hydra simulator.
    - Initially use a simple centralized barrier for synchronizing clocks.
        - A more sophisticated barrier algorithm can be implemented later, if needed.
    - Status
        - Foundational types for Praos.
        - Partial implementation of network.
    - Next steps
        - Basic Praos-like protocol.
        - Visualization of output.
        - Integrate with Agda-generated types.
- Notes and ideas
    - Study other network simulators (6+ candidates already)
    - Review design document for Cardano network.
    - Consider how $\Delta$Q-analysis can be used with the simulation.
    - The `random-forks` simulator runs 3000 nodes for one hour of simulated time in two seconds of wall-clock time.
    - Statistical design of experiments will be needed (OAT sensitivities, then LHS or OA designs).
    - Talk to Karl Knutson of CF about network statistics
    - Eventually, publish a web-based version of the simulator.

## 2024-02-06

### BB - Simplfied Praos/Peras Simulation/Visualization

- Changes
    - Removed use of `IO`, in order to accommodate `IOSim`.
    - Refactored random-number generation.
    - Refactored types into separate module.
    - Refactored graph visualization into separate module.
    - Added rounds and voting.
- Not yet implemented
    - Cooling-off period.
    - The code is still hacky and disposable.
    - Vertical alignment of blocks by slot in visualization.
    - Display of voting-round boundaries in visualization.
- Observations
    - `StatefulGen` and `IOSim` don't easily coexist.
    - Visualization the block production, voting, and forking is practical for many nodes and slots.
    - The Peras procotol can equally well be simulated via a centrally managed or a distributed simulation, but a distributed simulation seems cleanest and closest to the protocol.
- Next steps
    - Consider whether it is worthwhile further developing the model, or whether it would be better to re-architect the model in Agda or in a simulation framework.
    - Document visualization lessons-learned and next-generation design.

| Example chain                                                                 | Example topology                                                                  |
|-------------------------------------------------------------------------------|-----------------------------------------------------------------------------------|
| ![chain](https://ipfs.io/ipfs/Qme5KFUoNg7iDEQX84X6rU67YdYtMerp6Ywh574FKCTTCA) | ![topology](https://ipfs.io/ipfs/QmTXidVC4bqUVc8mnvJbbFda8itBYuKNBhWahzWBN7zPQ3) |

### YH

Reading the PoS-NSB paper and Coq code
  * Use of `math-comp` library in Coq takes getting used to
  * Sketched the relation on what states are reachable, i.e. the small steps semantics and the transitive closure in Agda
    https://github.com/input-output-hk/peras-design/blob/d90f164d5b5d1ac15bc6c8126d8180addb872681/src/Peras/Chain.agda#L131-L151

#### AB - Test Model

Reading PoS-NSB paper let me think about how to generate meaningful tests:
* The Model could generate a valid sequence of transactions, inject
  them in arbitrary nodes, and verify all nodes converge to a valid
  maximal chain
* This requires modelling txs which is annoying
* We could instead have the Model just play the role of the
  network/diffusion layer for blocks (And later votes) and select
  block to broadcast from whatever each node has made available some
  blocks, possibly injecting also rogue blocks. This removes the need
  to forge transactions and put the model in the shoes of the
  adversary, interposing itself between otherwise honest nodes

Trying to get a working environment (Again) but I have issues with
HLS/LSP: Code action for filling missing variables did not work, so I
upgraded to latest available `lsp-haskell` but now I get another
error:

``` Symbol’s value as variable is void:
lsp-haskell-plugin-cabal-code-actions-on ```

Managed to propertly configure auto formatting for Haskell on local
environment for Peras, such that it picks up the right configuration
file.  I ditched use of lsp-format-code action because it's borked as
per https://github.com/haskell/haskell-language-server/issues/411


Pushed a first version of a test model, along the lines sketched above.
The model's actions are very simple:
* `Tick` to advance the slot for all nodes,
* `ObserveChain` to retrieve the current best chain from a node.

Then when `perform`ing `Tick` on the real nodes, they will produce
some `Block`s which will be broadcast to other nodes, possibly later
with some delays or loss...

A basic property that could be interesting to state as our first test
would be the _Common Prefix_ property:

``` do anyActions_ getState >>= \ nodes -> do chains <- mapM (action
. ObserveBestChain) nodes assert $ all ((< k) . lengthDivergingSuffix)
chains ```

eg. all nodes' potential forks are not deeper than the security parameter `k` or equivalently all nodes have a common prefixs.

When we express properties for Peras, we could have this property
provide a tighter bound than `k` in the "steady state", or fallback to
`k` when confronted with adversarial behaviour.

## 2024-02-05

### BB

[Initial work in progress on a crude simulation of peers, chains, and forks](random-forks/ReadMe.md):

- Generates a reasonable but random topology of peers.
- Simplified election of slot leaders.
- Simplified lottery of voting committee.
- Forking of chain and message passing to downstream neighbors.
- The chaining is a work in progress, with several glaring but easily remedied deficiencies.
- The code is unpolished and hacky.
- The next step would be to add an approximation of the Peras protocol.

This is a disposable model, just  for exploration and building intuition.

| Example chain                                                                                                         | Example topology                                                                                                     |
|-----------------------------------------------------------------------------------------------------------------------|----------------------------------------------------------------------------------------------------------------------|
| ![chain](https://ipfs.io/ipfs/QmNNgoTeefUGrsHL8zpVy1BvaFzmce2WNm1yj4yWDjvGkF) | ![topology](https://ipfs.io/ipfs/QmVao93ZHzn7BXQyLjZ3Km2m7tfstu1cAzWDG19Va5oxGp) |


#### AB

Trying to assess what would be most useful to start working on for Peras.

We basically have a few moving pieces that need to fit together:
* A formal (eg. Agda-based) model of the protocol, along the lines of [Formalizing Nakamoto-Style Proof of Stake](https://eprint.iacr.org/2020/917)
  * need to analyse the original paper and the modeling and proof techniques used
  * need to port those to Agda
* An executable encoding of this formal model that's suitable for use by quickcheck-dynamic (or similar tool) to generate test traces for the protocol
  * requires to be able to generate something from Agda?
  * requires some kind of modeling of the environment of an instance of the protocol -> need to be done at the formal level too?
* Some driver/glue code to be able to actually test an executable (prototype) against this specificaiton/environment
* An actual prototype
  * need to be "embeddable" in order to maximise testing capabilities and minimise time, eg. use some form of IPC/shared memory instead of relying on full-blown network communications
  * abstracts away the details of the communication, e.g assumes some form of async message-passing from a network layer

Some interesting article defining what it means to formalise a Nakamoto consensus: https://allquantor.at/blockchainbib/pdf/stifter2018agreement.pdf

Looking at generated code from Agda:
* HS code is just unreadable: names and symbols are encoded, variables are just numbered with a single character prefix, etc.
* Not sure what this `MAlonzo` thing is? -> https://wiki.portal.chalmers.se/agda/Docs/MAlonzo says it's the standard compiler backend that generates Haskell from Agda code

As expected, generated code should be treated as opaque and "Sealed" and not easily amenable to extensions and modifications

Perhaps I should just start focusing on a simple aspect, e.g the Chain
Weight algorithm. Algorithm is rather complicated as it involves both
chains and votes and is pretty critical for the system. Other option
is to go top-down and just ignore the details of chain weight for the
moment, eg. write the pure protocol state machine model and build the
full chain from that?


Looking at
[AFLNet](https://thuanpv.github.io/publications/AFLNet_ICST20.pdf)
article which leverages AFL fuzzer to work on protocol/network
systems, not sure how this is done or if there's actual introspection
of the fuzzed system as AFL does

Retrieving https://github.com/AU-COBRA/PoS-NSB and adding as submodule for peras,  then trying to "Build it".
My memories of Coq are a bit blurry but it seems necessary to understand how they formalised the problem if we hope to be able to replicate it for Peras

#### Ensemble session

##### Topology of the network

A good experiment to evaluate it:
* Spin-up nodes all over the network and check propagation time
* Would allow us to create realistic simulation
* build an intuition about the structure of the network
* how much of the protocol survives depending on topology of netwokr

We might want to start asking now to experts what the actual topology looks like:
* Start w/ network team
* -> Karl Knutsson + Markus Gufler
* Galois ? -> CNSA project -> ?


Key metrics we might want to evaluate for running Peras:
* bytes storage => Disk
* bytes in RAM => Mem
* nbr + size of messages => impact on bandwidth
* pooltool.io -> measure latency

first-order -> network details independent, use distribution (ΔQ)
* used dQ in Marlowe to reason about degradation and back-pressure
* used fixed size queues -> tell the client to wait

partial deployment of Peras?

which formal model?
* experiment with https://github.com/input-output-hk/ouroboros-high-assurance ?
* try to formalise a piece of it? -> better go down the Coq/Agda route
* good inspiration for Agda: https://github.com/oracle/bft-consensus-agda

#### Some estimates for the protocol params

Some values for the parameters

* $T$: the length (in slots) of a voting round --> order of a few network deltas
* $K$: the length of a cooldown period (in voting rounds) --> large
  enough so that order of $b\times n + k$ blocks are produced in time $T\times K$,
  where $k$ is the current common-prefix parameter
* $L_{low}$, $L_{high}$: define vote-candidate window -->
  * $L_{high}$: some constant so that we think there is common prefix in
    practice if we cut off blocks newer than $current_time - L_{high}$;
  * $L_{low}$: should in theory be security parameter to guarantee that
    there exists a block in the interval $[L_{low}, L_{high}]$
* $A$: max. age for including vote --> security parameter to ensure
  honest votes get included (because of bad chain quality of Praos)
* $\tau$: number of votes required for quorum -->
  $`  \frac{3}{4\times n} + 2\times\delta, \mathrm{for some} \delta > 0  `$
* $b$: weight boost per vote --> prob. some small constant
* $W$: weight to cut off for common prefix --> order of security
  parameter; should be informed by the fact that R successful voting
  rounds give error
  $` e^{-2\delta\times b\times n\times R} `$
* $n$: committee size: order of security parameter to avoid
  adversarially dominated committees; we're also hoping to make it
  work for smaller committee sizes at some point

## 2024-01-31

### Peras Meeting

* Cardano Vision workshop -> CH + Research plan for next years
* Intermediate solutions to speed up finality -> low hanging fruits
  * CH ask about anti-grinding?
  * Peter also asked what happened to anti-grinding?
* grinding = making a block makes it possible to manipulate future lottery to make more block
  * introduce some PoW to calculate nonce over the epoch
  * no work on the Peras R&D team
  * could be good to still track it here and ensure it's making progress and tackled by someone?

* Peras paper: Alex, Aggelos, Christian, Peter, Sandro
  * targeting CCS but it's a bit soon
  * draft of the paper?
  * what kind of support? -> depends on the venue
  * could be good to have some kind of artifact

* Formal model ?
  * Best known approach so far : https://arxiv.org/abs/2007.12105
  * We need to start somewhere -> Write Sandro's algorithm in Agda
  * Could then port proof techniques from Coq
