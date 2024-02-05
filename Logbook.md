## 2024-02-05

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
