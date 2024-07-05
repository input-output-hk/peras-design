---
title: "Peras Technical Report #2"
author:
  - Arnaud Bailly
  - Brian W. Bush
  - Yves Hauser
  - Hans Lahe
date: 2024-04-17
monofont: Monaco
---

> [!IMPORTANT]
> Unlike for the first tech report, we should only include analyses that conform to the latest version of the protocol.

# Executive summary

> [!IMPORTANT]
> Summarize approach, results, and findings

# Protocol definition

> [!WARNING]
> The following is a near-verbatim copy of Figure 2 of the draft Peras paper. The only signficant alterations are the following:
>
> - Omit preagreement
>     - Set the termination bound to zero: T ≡ 0
>     - The proposed block for voting is simply the youngest block at least L slots old on the locally preferred chain.
> - Do not track certificate arrival time: Δ ≡ 0
> - The initial set of certificates is the genesis certificate, not the empty set.
> - Clarified ambiguities.
> - Omit irrelevant details.
> - Made chain-preference deterministic.
> - Sequenced operations.

> [!IMPORTANT]
> Do we want to provide a detailed description of the protocol here?
> Seems to me we should reference the Agda specification and only provide a high-level overview of what has changed since last tech report.

## Variables

The protocol keeps track of the following variables, initialized to the values below:

- `In1`: $C_\text{pref} \gets C_\text{genesis}$: preferred chain;
- `In2`: $\mathcal{C} \gets \{C_\text{genesis}\}$: set of chains;
- `In3`: $\mathcal{V} \gets \emptyset$: set of votes;
- `In4`: $\mathsf{Certs} \gets \{\mathsf{cert}_\text{genesis}\}$: set of certificates;
- `In5`: $\mathsf{cert}^\prime \gets \mathsf{cert}_\text{genesis}$: the latest certificate seen;
- `In6`: $\mathsf{cert}^* \gets \mathsf{cert}_\text{genesis}$: the latest certificate on chain.

## Sequence

The protocol operations occur sequentially in the following order:

- Fetching
- Block Creation
- Voting

## Fetching

At the beginning of each slot:
- `Fe1`: Fetch new chains $\mathcal{C}_\text{new}$ and votes $\mathcal{V}_\text{new}$.
- `Fe2`: Add any new chains in $\mathcal{C}_\text{new}$ to $\mathcal{C}$, add any new certificates contained in chains in $\mathcal{C}_\text{new}$ to $\mathsf{Certs}$.
    - `Fe2x`: Discard any equivocated blocks or certificates: i.e., do not add them to $\mathcal{C}$ or $\mathsf{Certs}$.
- `Fe3`: Add $\mathcal{V}_\text{new}$ to $\mathcal{V}$ and turn any new quorum in $\mathcal{V}$ into a certificate $\mathsf{cert}$ and add $\mathsf{cert}$ to $\mathsf{Certs}$.
    - `Fe3x`: Discard any equivocated votes: i.e., do not add the to $\mathcal{V}$.
- `Fe4`: Set $C_\text{pref}$ to the heaviest (w.r.t. $\mathsf{Wt}_\mathsf{P}(\cdot)$) valid chain in $\mathcal{C}$.
    - `Fe4x`: *If several chains have the same weight, select the one whose tip has the smallest block hash as the preferred one.*
    - Each party $\mathsf{P}$ assigns a certain weight to every chain $C$, based on $C$'s length and all certificates that vote for blocks in $C$ that $\mathsf{P}$ has seen so far (and thus stored in a local list $\mathsf{Certs}$).
    - `CW1`: Let $\mathsf{certCount}_\mathsf{P}(C)$ denote the number of such certificates, i.e., $\mathsf{certCount}_\mathsf{P}(C) := \left| \left\{ \mathsf{cert} \in \mathsf{Certs} : \mathsf{cert} \text{ votes for a block on } C \right\} \right|$.
    - `CW2`: Then, the weight of the chain $C$ in $\mathsf{P}$'s view is $\mathsf{Wt}_\mathsf{P}(C) := \mathsf{len}(C) + B \cdot \mathsf{certCount}_\mathsf{P}(C)$ for a protocol parameter $B$.
- `Fe5`: Set $\mathsf{cert}^\prime$ to the certificate with the highest round number in $\mathsf{Certs}$.
- `Fe6`: Set $\mathsf{cert}^*$ to the certificate with the highest round number on (i.e., included in) $C_\text{pref}$.

## Block creation

Whenever party $\mathsf{P}$ is slot leader in a slot $s$, belonging to some round $r$:

- `BC1`: Create a new block $\mathsf{block} = (s, \mathsf{P}, h, \mathsf{cert}, ...)$, where
    - `BC2`: $h$ is the hash of the last block in $C_\text{pref}$,
    - `BC3`: $\mathsf{cert}$ is set to $\mathsf{cert}^\prime$ if
        - `BC4`: there is no round-$(r-2)$ certificate in $\mathsf{Certs}$, and
        - `BC5`: $r - \mathsf{round}(\mathsf{cert}^\prime) \leq A$, and
        - `BC6`: $\mathsf{round}(\mathsf{cert}^\prime) > \mathsf{round}(\mathsf{cert}^*)$,
        - `BC7`: and to $\bot$ otherwise,
- `BC8` Extend $C_\text{pref}$ by $\mathsf{block}$, add the new $C_\text{pref}$ to $\mathcal{C}$ and diffuse it.

## Voting

Party $\mathsf{P}$ does the following at the beginning of each voting round $r$:

- `Vo1`: Let $\mathsf{block}$ be the youngest block at least $L$ slots old on $C_\text{pref}$.
- `Vo2`: If party $\mathsf{P}$ is (voting) committee member in a round $r$,
    - either
        - `VR-1A`: $\mathsf{round}(\mathsf{cert}^\prime) = r-1$ and $\mathsf{cert}^\prime$ was received before the end of round $r-1$, and
        - `VR-1B`: $\mathsf{block}$ extends (i.e., has the ancestor or is identical to) the block certified by $\mathsf{cert}^\prime$,
    - or
        - `VR-2A`: $r \geq \mathsf{round}(\mathsf{cert}^\prime) + R$, and
        - `VR-2B`: $r = \mathsf{round}(\mathsf{cert}^*) + c \cdot K$ for some $c > 0$,
    - `Vo3`: then create a vote $v = (r, \mathsf{P}, h,...)$,
    - `Vo4`: Add $v$ to $\mathcal{V}$ and diffuse it.

# Votes & Certificates

This section details the Peras voting process, from the casting and detailed structure of votes, to the creation, diffusion, and storage of certificates.

# Votes & Certificates

## Votes

### Overview

Voting in Peras is mimicked after the _sortition_ algorithm used in Praos, e.g it is based on the use of a _Verifiable Random Function_ by each stake-pool operator guaranteeing the following properties:

* The probability for each voter to cast their vote in a given round is correlated to their share of total stake,
* It should be computationally impossible to predict a given SPO's schedule without access to their secret key VRF key,
* Verification of a voter's right to vote in a round should be efficiently computable,
* Vote should be unique and non-malleable (this is a requirement for the use of efficient certificates aggregation, see [below](#alba-certificates)).

Additionally we would like the following property to be provided by our voting scheme:

* Voting should require minimal additional configuration (ie. key management) for SPOs,
* Voting and certificates construction should be fast in order to ensure we do not interfere with other operations happening in the node.

We have experimented with two different algorithms for voting, which we detail below.

### Structure of votes

We have used an identical structure for single `Vote`s, for both algorithms. We define this structure as a CDDL grammar, inspired by the [block header](https://github.com/input-output-hk/cardano-ledger/blob/e2aaf98b5ff2f0983059dc6ea9b1378c2112101a/eras/conway/impl/cddl-files/conway.cddl#L27) definition from cardano-ledger:

```cddl
vote =
  [ voter_id         : hash32
  , voting_round     : round_no
  , block_hash       : hash32
  , voting_proof     : vrf_cert
  , voting_weight    : voting_weight
  , kes_period       : kes_period
  , kes_vkey         : kes_vkey
  , kes_signature    : kes_signature
  ]
```

This definition relies on the following primitive types (drawn from Ledger definitions in [crypto.cddl](https://github.com/input-output-hk/cardano-ledger/blob/e2aaf98b5ff2f0983059dc6ea9b1378c2112101a/eras/conway/impl/cddl-files/crypto.cddl#L1))

```cddl
round_no = uint .size 8
voting_weight = uint .size 8
vrf_cert = [bytes, bytes .size 80]
hash32 = bytes .size 32
kes_vkey = bytes .size 32
kes_signature = bytes .size 448
kes_period = uint .size 8
```

As already mentioned, `Vote` mimicks the block header's structure which allows Cardano nodes to reuse their existing VRF and KES keys. Some additional notes:

* Total vote size is **710 bytes** with the above definition,
* Unless explicitly mentioned, `hash` function exclusively uses 32-bytes Blake2b-256 hashes,
* The `voter_id` is it's pool identifier, ie. the hash of the node's cold key.

#### Casting vote

A vote is _cast_ by a node using the following process which paraphrases the [actual code](https://github.com/input-output-hk/peras-design/blob/4ab6fad30b1f8c9d83e5dfb2bd6f0fe235e1395c/peras-vote/src/Peras/Voting/Vote.hs#L293)

1. Define _nonce_ as the hash of the _epoch nonce_ concatenated to the `peras` string and the round number voted for encoded as 64-bits big endian value,
2. Generate a _VRF Certificate_ using the node's VRF key from this `nonce`,
3. Use the node's KES key with current KES period to sign the VRF certificate concatenated to the _block hash_ the node is voting for,
4. Compute _voting weight_ from the VRF certificate using _sortition_ algorithm (see details below).

#### Verifying vote

[Vote verification](https://github.com/input-output-hk/peras-design/blob/34196ee6e06ee6060c189116b04a2666450c5b75/peras-vote/src/Peras/Voting/Vote.hs#L392) requires access to the current epoch's _stake distribution_ and _stake pool registration_ information.

1. Lookup the `voter_id` in the stake distribution and registration map to retrieve their current stake and VRF verification key,
2. Compute the _nonce_ (see above),
3. Verify VRF certificate matches nonce and verification key,
4. Verify KES signature,
5. Verify provided KES verification key based on stake pool's registered cold verification key and KES period,
6. Verify provided _voting weight_ according to voting algorithm.

### Leader-election like voting

The first algorithm is basically identical to the one used for [Mithril](https://mithril.network) signatures, and is also the one envisioned for [Leios](https://leios.cardano-scaling.org) (see Appendix D of the paper). It's based on the following principles:

* The goal of the algorithm is to produce a number of votes targeting a certain threshold such that each voter receives a number of vote proportionate to $\sigma$, their fraction of total stake, according to the basic probability function $\phi(\sigma) = 1 - (1 - f)^\sigma$,
* There are various parameters to the algorithm:
  * $f$ is the fraction of slots that are "active" for voting
  * $m$ is the number of _lottery_ each voter should try to get a vote for,
  * $k$ is the target total number of votes for each round (eg. quorum). $k$ should be chosen such that $k = m \dot \phi(0.5)$ to reach a majority quorum,
* When its turn to vote comes, each node run iterates over an index $i \in \[1 \dots m\]$, computes a hash from the _nonce_ and the index $i$, and compares this hash with $f(\sigma)$: if it's lower than or equal, then the node has one vote
  * Note the computation $f(\sigma)$ is exactly identical to the one used for [leader election](https://github.com/intersectmbo/cardano-ledger/blob/f0d71456e5df5a05a29dc7c0ac9dd3d61819edc8/libs/cardano-protocol-tpraos/src/Cardano/Protocol/TPraos/BHeader.hs#L434)

We [prototyped](https://github.com/input-output-hk/peras-design/blob/73eabecd272c703f1e1ed0be7eeb437d937e1179/peras-vote/src/Peras/Voting/Vote.hs#L311) this approach in Haskell.

### Sortition-like voting

The second algorithm is based on the _sortition_ process initially invented by [Algorand](https://web.archive.org/web/20170728124435id_/https://people.csail.mit.edu/nickolai/papers/gilad-algorand-eprint.pdf) and [implemented](https://github.com/algorand/sortition/blob/main/sortition.cpp) in their node. It's based on the same idea, ie. that a node should have a number of votes proportional to their fraction of total stake, given a target "committee size" expressed as a fraction of total stake $p$. And it uses the fact the number of votes a single node should get based on these parameters follows a binomial distribution.

The process for voting is thus:

* Compute the individual probability of each "coin" to win a single vote $p$ as the ratio of expected committee size over total stake
* Compute the binomial distribution $B(n,p)$ where $n$ is the node's stake
* Compute a random number between 0 and 1 using _nonce_ as the denominator over maximum possible value (eg. all bits set to 1) for the nonce as denominator
* Use [bisection method](https://en.wikipedia.org/wiki/Bisection_method) to find the value corresponding to this probability in the CDF for the aforementioned distribution

This yields a vote with some _weight_ attached to it "randomly" computed so that the overall sum of weights should be around expected committee size.

This method has also been [prototyped in Haskell](https://github.com/input-output-hk/peras-design/blob/73eabecd272c703f1e1ed0be7eeb437d937e1179/peras-vote/src/Peras/Voting/Vote.hs#L174).

### Benchmarks

The [peras-vote](../../peras-vote/) package provides some benchmarks comparing the 2 approaches, which gives us:

* Single Voting (Binomial): 139.5 μs
* Single Verification (binomial): 160.9 μs
* Single Voting (Taylor): 47.02 ms

**Note**: The implementation takes some liberty with the necessary rigor suitable for cryptographic code, but the timings provided should be consistent with real-world production grade code. In particular, when using _nonce_ as a random value, we only use the low order 64 bits of the nonce, not the full 256 bits.

## Certificates

### Mithril certificates

### ALBA

> [!WARNING]
> It's unclear whether or not KES signatures are [non malleable]() which is a requirement

* [ALBAs](https://iohk.io/en/research/library/papers/approximate-lower-bound-arguments/) appears to provide a good basis for Peras certificates
* The [Prototype implementation in Haskell](https://github.com/cardano-scaling/alba) provides some evidence this construction could be feasible in the context of Peras

### Proving & Verification time

The following picture plots the time needed (in milliseconds) to build certificate for varying number of votes, assuming a security parameter of 128, honest share of 67% and vote size of 256 bytes.

![ALBA Proving time](../diagrams/alba-cpu.svg)

We can observe that even in some extreme cases proving time stays consistently under 20ms and on the average is between 10 and 15ms for even large number of items. The wild variation in proving time for different number of input set is explained by the non-deterministic nature of the algorithm: We construct the proof through depth-first search, by repeatedly comparing hash values _modulo_ the expected number of honest items, so the number of comparisons and hashes to make may vary significantly depending on how the ordering of the list of items.

It's worth considering whether or not this dependency on the ordering of the items could be an attack vector as proving time could easily explode in case we need to explore more than a small fraction of the tree.

Verification time has not been plotted but is lower than 1ms in all the cases considered as it is tied to the number of hash computation one has to make which is $O(u)$.

### Certificate size

For a given set of parameters, eg. fixed values for $\lambda_{sec}$, $\lambda_{rel}$, and $n_p/n_f$ the proof size is perfectly linear and only depends on the size of each vote:

![Proof size / vote size](../diagrams/alba-proof-size-fixed-params.svg)

Varying the security parameter and the honest votes ratio for a fixed set of 1000 votes of size 200 yields the following diagram, showing the critical factor in proof size increase is the $n_p/n_f$ ratio: As this ratio decreases, the number of votes to include in proof grows superlinearly.

![Proof size vs. λ and honest votes ratio](../diagrams/alba-proof-size-lambda.svg)

### Benchmarks

In the following tables we compare some interesting metrics between the two differnt kind of certificates we studied, Mithril certificates (using BLS signatures) and ALBA certificates (using KES signatures): Size of certificate in bytes, proving time (eg. the time to construct a single vote), aggregation time (the time to build a certificate), and verification time.

For Mithril certificates:

|---------------------------------|-------|
| Certificate size                | 56kB  |
| Proving time (per vote)         | ~70ms |
| Aggregation time                | 1.2s  |
| Verification time (certificate) | 17ms  |

For ALBA certificates:

|---------------------------------|--------|
| Certificate size                | 47kB   |
| Proving time (per vote)         | ~133us |
| Aggregation time                | ~5ms   |
| Verification time (certificate) | 15ms   |
|                                 |        |

## Vote diffusion

# Constraints on Peras Parameters

| Parameter               | Symbol          | Units   | Description                                                                               | Constraints                                              | Rationale                                                                                 |
| ----------------------- | --------------- | ------- | ----------------------------------------------------------------------------------------- | -------------------------------------------------------- | ----------------------------------------------------------------------------------------- |
| Round length            | $U$             | slots   | The duration of each voting round.                                                        | $U \geq \Delta$                                          | All of a round's votes must be received before the end of the round.                      |
| Certificate expiration  | $A$             | slots   | The maximum age for a certificate to be included in a block.                              | $A = T_\text{heal}+T_\text{CQ}$                          | After a quorum failure, the chain must heal and achieve quality.                          |
| Chain ignorance period  | $R$             | rounds  | The number of rounds for which to ignore certificates after entering a cool-down period.  | $R = \left\lceil A / U \right\rceil$                     | Ensure chain-ignorance period lasts long enough to include a certificate on the chain.    |
| Cool-down period        | $K$             | rounds  | The minimum number of rounds to wait before voting again after a cool-down period starts. | $K = \left\lceil \frac{A + T_\text{CP}}{U} \right\rceil$ | After a quorum failure, the chain must heal, achieve quality, and attain a common prefix. |
| Certification boost     | $B$             | blocks  | The extra chain weight that a certificate gives to a block.                               | $B \gt 0$                                                | Peras requires that some blocks be boosted.                                               |
| Quorum size             | $\tau$          | parties | The number of votes required to create a certificate.                                     | $\tau \gt 3 n / 4$                                       | Guard against a minority (<50%) of adversarial voters.                                    |
| Committee size          | $n$             | parties | The number of members on the voting committee.                                            | $n \gt 0$                                                | Peras requires a voting committee.                                                        |
| Network diffusion time  | $\Delta$        | slots   | Upper limit on the time needed to diffuse a message to all nodes.                         | $\Delta \gt 0$                                           | Messages have a finite delay.                                                             |
| Active slot coefficient | $f$             | 1/slots | The probability that a party will be the slot leader for a particular slot.               | $0 \lt f \leq 1$                                         | Blocks must be produced.                                                                  |
| Healing time            | $T_\text{heal}$ | slots   | Healing period to mitigate a strong (25-50%) adversary.                                   | $T_\text{heal} ≟ \mathcal{O}\left( B^2 / f \right)$      | Sufficient blocks must be produced to overcome an adversarially boosted block.            |
| Chain-quality time      | $T_\text{CQ}$   | slots   | Ensure the presence of at least one honest block on the chain.                            | $T_\text{CQ} = \mathcal{O} (k/f)$                        | A least one honest block must be produced.                                                |
| Common-prefix time      | $T_\text{CP}$   | slots   | Achieve settlement.                                                                       | $T_\text{CQ} = \mathcal{O} (k/f)$                        | The Ouroboros Praos security parameter defines the time for having a common prefix.       |
| Security parameter      | $k$             | blocks  | The Ouroboros Praos security parameter.                                                   | n/a                                                      | Value for the Cardano mainnet.                                                            |

*Note that parameters $T$ and $\Delta$ are not used in this pre-alpha specification of the Peras protocol.*

# Simulating Peras

## Protocol simulation

The Peras simulator is a prototype/reference implementation of the Peras protocol in Haskell. The implementation aims to encode the pseudo-code for the protocol specification in as literal and transparent a manner as possible, regardless of the performance drawbacks of such literalness. Note that it simulates the Peras protocol in the abstract and does not include a simulation of network diffusion. Its core contains four modules:

- `Peras.Prototype.Fetching` handles the receipt of new chains and new votes. It includes the following logic:
    - creates new certificates when a new quorum of votes is reached,
    - selects the preferred chain, and
    - updates $\mathsf{cert}^\prime$ and $\mathsf{cert}^*$.
- `Peras.Prototype.BlockCreation` forges new blocks and, optionally, includes a certificate in the new block.
- `Peras.Prototype.Preagreement` selects the block that a party will vote upon.
- `Peras.Prototype.Voting` casts votes.

Additional, non-core modules handle the diffusion of votes, the interactions between multiple nodes, and visualization of results. The simulator's voting behavior has been tested against the Agda-derived executable specification via the `quickcheck-dynamic` property-based state-machine testing framework: see `Peras.Conformance.Test`.

The simulator can be run from the command line or in a web browser. At the command line, one can specify the input configuration (state) of the simulation, store its output configuration, and record a trace of simulation events. The ending time of the output configuration can be edited to set it to a later time, and then the simulation can be continued by providing that edited output configuration as input to the continued simulation.

```console
$ peras-simulate --help

peras-simulate: simulate Peras protocol

Usage: peras-simulate [--version] [--in-file FILE] [--out-file FILE]
                      [--trace-file FILE]

  This command-line tool simulates the Peras protocol.

Available options:
  -h,--help                Show this help text
  --version                Show version.
  --in-file FILE           Path to input YAML file containing initial simulation
                           configuration.
  --out-file FILE          Path to output YAML file containing final simulation
                           configuration.
  --trace-file FILE        Path to output JSON-array file containing simulation
                           trace.
```

The input configuration file specifies the protocol parameters, the initial state of the simulation, and the slot-leadership and committee-membership schedules for each node/party. This gives the user full control over the simulation and ensures reproducibility of the simulation results.

```json
{
  "params":{"U":20,"A":200,"R":10,"K":17,"L":10,"τ":2,"B":10,"T":15,"Δ":5},
  "start":0,
  "finish":300,
  "payloads":{},
  "parties":{
    "1":{"leadershipSlots":[2,10,25,33,39,56,71,96,101,108,109,115],"membershipRounds":[1,2,6],"perasState":{"certPrime":{"blockRef":"","round":0},"certStar":{"blockRef":"","round":0},"certs":[],"chainPref":[],"chains":[[]],"votes":[]}},
    "2":{"leadershipSlots":[12,17,33,44,50,67,75,88,105],"membershipRounds":[2,3,5,6],"perasState":{"certPrime":{"blockRef":"","round":0},"certStar":{"blockRef":"","round":0},"certs":[],"chainPref":[],"chains":[[]],"votes":[]}},
    "3":{"leadershipSlots":[5,15,42,56,71,82,124],"membershipRounds":[3,4,5,6],"perasState":{"certPrime":{"blockRef":"","round":0},"certStar":{"blockRef":"","round":0},"certs":[],"chainPref":[],"chains":[[]],"votes":[]}},
    "4":{"leadershipSlots":[8,15,21,38,50,65,127],"membershipRounds":[1,5],"perasState":{"certPrime":{"blockRef":"","round":0},"certStar":{"blockRef":"","round":0},"certs":[],"chainPref":[],"chains":[[]],"votes":[]}}
  },
  "diffuser":{"delay":0,"pendingChains":{},"pendingVotes":{}}
}
```

The output configuration file reveals all of the chains, votes, etc. tracked by each node/party. The trace file is a JSON array of events occurring in the simulation. The trace file converted to a GraphViz `.dot` file for visualization. Traces can also be piped into tools for real-time analysis.

| Tag                         | Event                                                      |
| --------------------------- | ---------------------------------------------------------- |
| `Protocol`                  | new protocol parameters                                    |
| `Tick`                      | new slot                                                   |
| `NewChainAndVotes`          | new chains and votes received                              |
| `NewCertificatesReceived`   | new certificates received (embedded in new chains)         |
| `NewCertificatesFromQuorum` | new certificates created after new votes have been fetched |
| `NewChainPref`              | node prefers a new chain                                   |
| `NewCertPrime`              | node selected a new $\mathsf{cert}^\prime$                 |
| `NewCertStar`               | node selected a new $\mathsf{cert}^*$                      |
| `ForgingLogic`              | logic for including a certificate in a new block           |
| `DiffuseChain`              | chain extended by a new block                              |
| `PreagreementBlock`         | preagreement on a block to be voted upon                   |
| `PreagreementNone`          | no preagreement for voting                                 |
| `VotingLogic`               | logic for casting a vote                                   |
| `DiffuseVote`               | diffuse a new vote                                         |

```console
$ peras-visualize --help

peras-visualize: visualize Peras simulation traces

Usage: peras-visualize [--version] --trace-file FILE [--dot-file FILE]

  This command-line tool visualizes Peras simulation traces.

Available options:
  -h,--help                Show this help text
  --version                Show version.
  --trace-file FILE        Path to input JSON-array file containing simulation
                           trace.
  --dot-file FILE          Path to output GraphViz DOT file containing
                           visualization.
```

## Protocol visualization

The results of simulations can be viewed graphically in a web application (see https://peras-simulation.cardano-scaling.org/) that lets one explore the operation of the Peras protocol and the influence that each of the protocol parameters has upon the evolution of the block tree. This can be used for education, for studying voting behavior, for selecting optimal values of the protocol parameters, or for debugging a simulation.

The screenshot below shows the user interface for the Peras simulation web application.

- Each of the Peras protocol parameters may be set, and tooltips provide explanations of them.
- Simulation-related parameters such as the duration of the simulation, the number of nodes involved, and the random-number seen may be set.
- Users can share simulations by copying a URL that embeds sufficient information to fully reproduce the simulation.
- Buttons allow the user to run, step singly, pause or stop the simulation.
- A zoomable display visualizes the simulated block tree.

![Screenshot of Peras visualization web application](../diagrams/simvis-parameters.png)

The screenshot below shows the visualization of the Peras block tree:

- Light blue rectangles represent blocks that do not record Peras certificates, whereas dark blue rectangles represent blocks that do record Peras certificates recorded in them.
    - Block lines point to the parent block.
    - The three ⊤ and ⊥ symbols in the block indicate whether each of the three certificate-inclusion rules are true or false, respectively.
- Salmon-colored circles represent votes for blocks, whereas olive-colored circles represent situation were a party was on the voting committee but not allowed to vote.
    - Salmon-colored dashed lines point to the block being voted for.
    - The four ⊤ and ⊥ symbols in the block indicate whether each of the four voting rules are true or false, respectively.
- Certificates are aqua rectangles.
    - Aqua dashed lines point to the block being certified.
- Nodes are red circles.
    - The red dashed lines point to the tip of their preferred blockchain.
    - The orange dashed lines point to their $\mathsf{cert}^\prime$ and $\mathsf{cert}^*$ certificates.

![Blocktree display in the Peras visualization web application](../diagrams/simvis-blocktree.png)

The visualizer can be deployed as a server via Docker. It supports multiple simultaneous web clients running each their own simulations and it supports basic HTTP authentication.

```console
$ peras-server --help

peras-server: server Peras simulations

Usage: peras-server [--version] [--port PORT]
                    [--username STRING --password STRING]

  This server provides Peras simulations.

Available options:
  -h,--help                Show this help text
  --version                Show version.
  --port PORT              Port on which the server listens.
  --username STRING        Authorized user.
  --password STRING        Password for authorized user.
```

## Markov-chain simulation

> [!IMPORTANT]
> Discuss the Markov-chain simulation and results

# Analyses of adversarial scenarios

> [!CAUTION]
> 1. Several well-formatted equations are not rendered correctly by GitHub's MathJAX. Make sure that these render correctly via `pandoc`.
> 2. Check all of the mathematical derivations in this section.
> 3. Explain the scenarios more clearly.

In this section we use the following notation:

- Active-slot coefficient: $\alpha$
- Round length: $U$
- Block-selection offset: $L$
- Certificate expiration: $A$
- Quorum for creating a certificate: $\tau = \frac{3}{4} n$
- Fraction of adversarial stake: $f$
- Mean size of the voting committee: $n$
- Per-slot probability of a block:
    - Honest block: $p = 1 - (1 - \alpha)^{1 - f} \approx \alpha \cdot (1 - f)$
    - Adversarial block: $q = 1 - (1 - \alpha)^f \approx \alpha \cdot f$
- Binomial distribution of $n$ trials each with probability $p$ :
    - Probability density function: $\mathbf{p}_\text{binom}(k,n,p)= {n\choose{k}} \cdot p^k \cdot (1 - p)^{n-k}$
    - Cumulative probability function: $\mathbf{P}_\text{binom}(m,n,p) = \sum_{k=0}^m \mathbf{p}(k,n,p)$
- Normal distribution with mean $\mu$ and standard deviation $\sigma$:
    - Probability density function: $\mathbf{p}_\text{normal}(x, \mu, \sigma) = \frac{1}{\sqrt{2 \pi \sigma^2}} e^{- \frac{(x - \mu)^2}{2 \sigma^2}}$
    - Cumulative probability function: $\mathbf{P}_\text{normal}(x,\mu,\sigma) = \int_{-\infty}^x dt \, \mathbf{p}_\text{normal}(t, \mu, \sigma)$

> [!IMPORTANT]
> Discuss the relationship between per-slot probabilities and per-block probabilities.

> [!IMPORTANT]
> Add paragraphs discussing how to interpret probabilities in terms of the security of a long-running blockchain.

## No honest quorum in round

***Question:*** What is the probability of not reaching a quorum if adversaries abstain from voting?

***Relevance:*** This analysis can be used to select a mean committee size that is appropriate for a given risk tolerance.

***Risk:*** A adversary can trigger a cool-down period if they abstain from voting.

***Scenario:*** Consider the situation where the adversary decides not to vote in a round, in order to prevent a quorum from occurring and to force the chain into a cool-down period. This occurs when the number of honest voters is less than the quorum size.

***Analysis:*** Let $\beta$ be the probability that a unit of stake is selected for voting-committee membership. Let $S$ be the total stake and $H = (1 - f) \cdot S$ be the honest stake. Assuming the total stake is large, we can approximate the binomial distribution by a normal one and express the probability of not having an an honest quorum as follows:

$$
P = \mathbf{P}_\text{binom} (\lfloor\tau\rfloor, H, \beta) \approx \mathbf{P}_\text{normal} \left( \tau, H \cdot \beta, \sqrt{H \cdot \beta \cdot (1 - \beta)} \right) \approx \mathbf{P}_\text{normal} \left( \tau, H \cdot \beta, \sqrt{H \cdot \beta} \right)
$$

Now set the quorum size to the recommended value $\tau = \frac{3}{4} n$ to discover a simple relationship:

$$
P \approx \mathbf{P}_\text{normal} \left( f , \frac{1}{4} , \sqrt{\frac{1 - f}{n}} \right)
$$

The following R function performs this computation:

```R
function(f, n)
  pnorm(f, 1 / 4, sqrt((1 - f) / n))
```

***Example:*** Plot the probability of not having an honest quorum as a function of the adversarial fraction of stake, for various mean sizes of the voting committee.

![Per-round probability of no honest quorum, when quorum is three-quarters of mean committee size](../diagrams/no-honest-quorum.plot.png)

## Adversarial quorum

***Question:*** What is the probability that adversaries can form a voting quorum in a round?

***Relevance:*** This analysis can be used to select a mean committee size that is appropriate for a given risk tolerance.

***Risk:*** An adversary can boost an adversarial fork.

***Scenario:*** Consider the situation where adversaries are lucky enough in the voting-committee sortition to hold a quorum of votes.

***Analysis:*** The analysis proceeds similarly to the "no honest quorum" scenario, but for adversaries having at least a quorum of votes.

$$
P = 1 - \mathbf{P}_\text{binom} (\lceil\tau\rceil, S - H, \beta) \approx 1 - \mathbf{P}_\text{normal} \left( \tau, (S - H) \cdot \beta, \sqrt{(S - H) \cdot \beta \cdot (1 - \beta)} \right) \approx 1 - \mathbf{P}_\text{normal} \left( \tau, f \cdot n, \sqrt{f \cdot n} \right)
$$

Now set the quorum size to the recommended value $\tau = \frac{3}{4} C$ to discover a simple relationship:

$$
P \approx \mathbf{P}_\text{normal} \left( f , \frac{3}{4} , \sqrt{\frac{f}{n}} \right)
$$

The following R function performs this computation:

```R
function(f, n)
  pnorm(f, 3 / 4, sqrt(f / n))
```

***Example:*** Plot the probability of having an adversarial quorum as a function of the adversarial fraction of stake, for various mean sizes of the voting committee.

![Per-round probability of adversarial quorum, when quorum is three-quarters of mean committee size](../diagrams/adversarial-quorum.plot.png)

## No certificate in honest block

***Question:*** What is the probability that adversaries can prevent a certificate from being included in a block before the certificate expires?

***Relevance:*** This analysis can be used to set the certificate-expiration parameter $A$.

***Risk:*** An adversary can trigger a premature ending of the cool-down period (via rule VR-2B) by preventing a new *cert\** from being recorded in a block.

***Scenario:***  Consider the situation where the voting certificate must be included on the chain (via rule Block Creation 1b), but no honest blocks are forged before the last *cert′* expires and adversaries abstain from updating *cert′* when they forge blocks.

***Analysis:***. The probability that adversaries forge every block during the period when the certificate hasn't expired is

$$
P = (1 - p)^A = (1 - \alpha)^{(1 - f) \cdot A}
$$

and this can be represented as the following R function:

```R
function(A, f, alpha)
  (1 - alpha)^((1 - f) * A)
```

***Example:*** Assuming an active-slot coefficient of 5%, plot the probability of a certificate not being recorded in an honest block before the certificate expires.

![Probability of now certificate in an honest block before it expires](../diagrams/no-certificate-in-honest-block.plot.png)

## Adversarial chain receives boost

> [!IMPORTANT]
> Discuss why there are several variants here.

### Variant 1

> [!CAUTION]
> This variant needs reworking!

***Question.*** What is the probability that an adversarial chain receives the next boost?

***Relevance:*** This analysis provides guidance on selecting the round length.

***Risk:*** An adversary can anchor their chain by having one of its later blocks boosted.

***Scenario.*** It currently is round $r$ and a certificate was created in round $r - 1$ for a block at least $U + L$ slots in the past that is also in the common prefix of the honest and adversarial chains. The honest parties lengthen one fork by $m \ge 0$ blocks to the next candidate for voting (i.e., the newest block on that fork that is at least $L$ slots old) and the adversarial parties similarly lengthen a separate fork by $n \ge 0$ blocks. If the adversarial chain is revealed to the honest parties before the start of the new round $r$ and if the adversarial chain is longer (i.e., $n \gt m$), then the voting committee will vote to boost the adversarial chain. The per-slot probability of adding a block to the honest or adversarial chain is $p$ or $q$, respectively.

![Adversarial chain receives boost](../diagrams/adversarial-chain-receives-boost.diagram.png)

***Analysis.*** Assume that the block- and vote-diffusion times are negligible, so that the last boosted block is indeed the last block before slot $r \cdot U - U - L$ and that the honest and adversarial candidates are indeed the last blocks on their forks before slot $r \cdot U - l$. (Note that this neglects the probability that the adversary will privately extend the last boosted block before slot $r \cdot U - U - L$.) Thus the lengthening of the two forks during the $U$ slots are the last boosted block are binomially distributed with parameters $m$ and $p$ (honest) and $n$ and $p$ (adversarial). The probability of $m < n$ is

$$
P = \sum_{0 \le m \lt n \le U} \mathbf{p}_\text{binom}(m,U,p) \cdot \mathbf{p}_\text{binom}(n,U,q) = \sum_{n=1}^U \mathbf{P}_\text{binom}(n-1,U,p) \cdot \mathbf{p}_\text{binom}(n,U,q)
$$

and the following R function implements this computation:

```R
function(U, p, q)
  sum( pbinom(1:U-1, U, p) * dbinom(1:U, U, q) )
```

***Example.*** Let the active-slot coefficient $\alpha = 0.05 \, \text{slot}^{-1}$ and let $f$ be the fraction of adversarial stake, so $p = \alpha \cdot (1 - f)$ and $q = \alpha \cdot f$. Plot the probability of the dishonest boost as a function of the adversarial fraction of stake and the round length.

![Per-round probability of dishonest boost when the active-slot coefficient is 5%.](../diagrams/adversarial-chain-receives-boost.plot.png)

### Variant 2

***Question.*** What is the probability that an adversarial chain receives the next boost?

***Relevance:*** This analysis provides guidance on selecting the round length.

***Risk:*** An adversary can anchor their chain by having one of its later blocks boosted, resulting in honest blocks being rolled back.

***Scenario.*** It currently is round $r$ and a certificate was created in round $r - 1$ for a block at least $U + L$ slots in the past that is also the common prefix of the honest and adversarial chains. The honest parties lengthen one fork by $m \ge 0$ blocks to the next candidate for voting (i.e., the newest block on that fork that is at least $L$ slots old) and the adversarial parties similarly lengthen a separate fork by $k \ge 0$ blocks before slot $r \cdot U - U - L$ and by $n \ge 0$ blocks subsequently. If the adversarial chain is revealed to the honest parties at slot $r \cdot U = L$ and if the adversarial chain is longer (i.e., $k + n \gt m$), then all parties will extend the adversarial chain and then next voting committee will boost the adversarial chain, causing the $m$ honest blocks to be rolled back.

![Adversarial chain receives boost](../diagrams/adversarial-chain-receives-boost-variant.diagram.png)

***Analysis.*** Assume that the block- and vote-diffusion times are negligible, so that the last boosted block is indeed the last public block before slot $r \cdot U - U - L$ and that the honest and adversarial candidates are indeed the last blocks on their forks before slot $r \cdot U - l$. Thus the lengthening of the two forks during the $U$ slots are the last boosted block are binomially distributed with parameters $m$ and $p$ (honest) and $n$ and $p$ (adversarial). Additionally, the adversary may privately produce $k$ blocks after the last boosted block and before slot $r \cdot U - U - L$: this random variable for producing such blocks is negative-binomially distributed. The probability of $m < k + n$ is

$$
P = \sum_{\substack{0 \le m \le U \\ 0 \le n \le U \\ 0 \le k \le \infty \\ m \lt n + k}} (1 - f) f^k \cdot {U\choose{m}} p^m (1-p)^{U-m} \cdot {U\choose{n}} q^n (1-q)^{U-n}
$$
which simplifies to
$$
P = (1 - f) \cdot \sum_{n=1}^U \mathbf{P}_\text{binom}(n-1,U,p) \cdot \mathbf{p}_\text{binom}(n,U,q) + (1 - f) \cdot \sum_{k=1}^U f^k \cdot \sum_{n=0}^{U-k} \mathbf{P}_\text{binom}(n+k-1,U,p) \cdot \mathbf{p}_\text{binom}(n,U,q) + f^{U+1}
$$

and we can be implemented in R as the following function:

```R
function (U, p, q) {
  f <- q / (p + q)
  p0 <- (1 - f) * sum( pbinom(0:(U-1), U, p) * dbinom(1:U, U, q) )
  pk <- (1 - f) * sum( mapply(function(k) f^k * sum( pbinom((k-1):(U-1), U, p) * dbinom(0:(U-k), U, q) ), 1:U) )
  pinf <- f^(U+1)
  p0 + pk + pinf
}
```

***Example.*** Let the active-slot coefficient $\alpha = 0.05 \, \text{slot}^{-1}$ and let $f$ be the fraction of adversarial stake, so $p = \alpha \cdot (1 - f)$ and $q = \alpha \cdot f$. Plot the probability of the dishonest boost as a function of the adversarial fraction of stake and the round length.

![Per-round probability of dishonest boost (variant) when the active-slot coefficient is 5%.](../diagrams/adversarial-chain-receives-boost-variant.plot.png)

## Healing from adversarial boost

***Question:*** How long does it take to neutralize the adversarial advantage of a certificate?

***Relevance:*** "During the initial “healing” phase of the cooldown period, parties continue with standard Nakamoto block creation until the potential advantage of B that the adversary could gain with a certificate is neutralized." This healing time helps determine the value of the certificate-expiration time $A$ and the chain-ignorance period $R$.

***Risk:*** An adversary can cause their fork to be preferred for an extended period if it has a certificate.

***Scenario:*** The honest chain must grow at least $B$ blocks longer than the adversarial chain if it is to resist the adversarial chain's receiving a boost from a certificate.

***Analysis:*** During cooldown, the growth of the honest chain (length $m$) and adversarial chain (length $n$) can be modeled by the difference between binomially distributed random variables. The probability of $m \lt n + B$ at slot $s$ is

$$
P = \sum_{0 \le m \lt n + B \le s} \mathbf{p}_\text{binom}(m, s, p) \cdot \mathbf{p}_\text{binom}(n, s, q) = \sum_{n=0}^s \mathbf{P}_\text{binom}(n+B-1, s, p) \cdot \mathbf{p}_\text{binom}(n, s, q)
$$

and can be computed by the following R function:

```R
function(s, B, p, q)
  sum(pbinom((B-1):(s+B-1), s, p) * dbinom(0:s, s, q))
```

***Example:*** Plot the probability of the honest chain not healing from an adversarial boost, as a function of the healing time $s$ and the boost $B$, under the assumption that the active-slot coefficient $\alpha = 0.05 \, \text{slot}^{-1}$ a.

![Probability of not healing from an adversarial boost, given 5% active slots.](../diagrams/healing-from-adversarial-boost.plot.png)

## No honest block

***Question:*** What is the probability of not having an honest block during a given period of time?

***Relevance:*** "In the subsequent phase, parties are required to submit the latest certificate they are aware of to the chain." This chain-quality time helps determine the value of the certificate-expiration time $A$ and the chain-ignorance period $R$.

***Risk:*** The registration of a certificate during cooldown might require waiting for an honest block where it can be included.

***Scenario, Analysis, Example:*** The scenario, analysis, and example are identical to the case "No certificate in honest block".

![Probability of not producing an honest block within the chain-quality time, given 5% active slots](../diagrams/no-honest-block.plot.png)

## No common prefix

***Question:*** How long can an adversary maintain a common prefix?

***Relevance:*** "Finally, in the third phase, parties wait until the blocks from the second phase have stabilized." This common-prefix time helps determine the value of the cooldown period $K$.

***Risk:*** A strong adversary can keep their fork viable for many slots.

***Scenario:*** The honest chain must grow longer than the adversarial chain.

***Analysis:*** During cooldown, the growth of the honest chain (length $m$) and adversarial chain (length $n$) can be modeled by the difference between binomially distributed random variables. The probability of $m \le n$ at slot $s$ is

$$
P = \sum_{0 \le m \le n \le s} \mathbf{p}_\text{binom}(m, s, p) \cdot \mathbf{p}_\text{binom}(n, s, q) = \sum_{n=0}^s \mathbf{P}_\text{binom}(n, s, p) \cdot \mathbf{p}_\text{binom}(n, s, q)
$$

and can be computed by the following R function:

```R
function(s, B, p, q)
  sum(pbinom(0:s, s, p) * dbinom(0:s, s, q))
```

***Example:*** Plot the probability of the adversarial chain being at least as long as the honest chain, as a function of the common-prefix time $s$, under the assumption that the active-slot coefficient $\alpha = 0.05 \, \text{slot}^{-1}$ a.

![Probability of not achieving the common-prefix time, given 5% active slots.](../diagrams/no-common-prefix.plot.png)

## Block rolled back

***Question:***

***Relevance:***

***Risk:***

***Scenario:***

***Analysis:***

***Example:***

# Recommendations for Peras parameters

Based on the analysis of adversarial scenarios, a reasonable set of default protocol parameters for further study and simulation is show in the table below. The optimal values for a real-life blockchain would depend strongly upon external requirements such as balancing settlement time against resisting adversarial behavior at high values of adversarial stake.

| Parameter              | Symbol | Units   | Value | Rationale                                                             |
|------------------------|--------|---------|------:|-----------------------------------------------------------------------|
| Round length           | $U$    | slots   |   400 | 1 ppm probability of 10% adversarial chain receiving boost.           |
| Certificate expiration | $A$    | slots   | 43200 | Determined by security parameter.                                     |
| Chain ignorance period | $R$    | rounds  |   108 | Determined by security parameter and round length.                    |
| Cool-down period       | $K$    | rounds  |   108 | Determined by security parameter and round length.                    |
| Certification boost    | $B$    | blocks  |    10 | 1 ppm probability of not healing from boost in 40% adversarial chain. |
| Committee size         | $n$    | parties |   900 | 1 ppm probability of no honest quorum at 10% adversarial stake.       |
| Quorum size            | $\tau$ | parties |   675 | Three-quarters of committee size.                                     |
| Security parameter     | $k$    | blocks  |  2160 | The Ouroboros Praos security parameter.                               |

# Formal specification in Agda

In the following subsections we explain how the formal specification of Ouroboros Peras relates the research paper with the reference implementation of the protocol.

## Formal specification

The formal specification is implemented in Agda as a relational specification. It provides a small-step semantics of the protocol that describes how the system can evolve over time.
Computational aspects in general are not considered, but are only defined by types, which might be refined by properties. The block-tree is an example of such a type that is not implemented in the formal specification, but on the other hand defined by properties specifying the behavior of an implementation of this data structure.

This is different approach to for example the formal ledger specification, where the formal specification is also directly executable.

We considered and investigated the following approaches to link the formal specification with an executable specification in Haskell

* Relational specification, make it decidable and use that executable version as reference implementation
    Pro: yields an executable specification in Haskell.
    Con: requires decidable versions of each small step.

* Relational specification, formulate test properties and prove that test properties conform
    Pro: yields properties in Haskell
    Con: no executable specification in Haskell

* Relational specification together with an executable specification and prove their equivalence
    Pro: yields an executable specification in Haskell
    Con: consistency and completeness proofs may be difficult

Restrictions:

* fixed set of participants

## Formally verified properties from the research paper

## Formally verified test executions

# Conformance testing

Conformance testing is linked to the Peras paper via the following chain of evidence:

- The protocol defined in the Peras paper is encoded in Agda as a relational specification.
- The proofs in the Peras paper will be encoded as Agda proofs.
- The protocol is also implemented as an executable specification in Agda.
- Soundness proofs demonstrate that the executable specification correctly implements the relational specification.
- The `agda2hs` tool generates Haskell code implementing the Agda executable specification.
- That Haskell code is used as the *state model* in the `quickcheck-dynamic` state-machine, property-based-testing framework.
- The implementation being tested is used as the *run model*.
- The `quickcheck-dynamic` tool generates arbitrary test cases and verifies that the run model obeys the properties of the state model.

The following types in the Agda executable specification are exported to Haskell.

```agda
record NodeModel : Set where
  field
    clock        : SlotNumber
    protocol     : PerasParams
    allChains    : List Chain
    allVotes     : List Vote
    allSeenCerts : List Certificate

data EnvAction : Set where
  Tick     : EnvAction
  NewChain : Chain → EnvAction
  NewVote  : Vote → EnvAction

initialModelState : NodeModel

transition : NodeModel → EnvAction → Maybe (List Vote × NodeModel)
```

> [!IMPORTANT]
> Update the above after adversarial tests have been added.

This is used in the Haskell state model as follows.

```haskell
instance StateModel NodeModel where
  data Action NodeModel a where
    Step :: EnvAction -> Action NodeModel [Vote]
  initialState = initialModelState
  precondition s (Step a) = isJust (transition s a)
  nextState s (Step a) _ = snd . fromJust $ transition s a
```

The present implementation focuses on the voting behavior, not on the block-production and network-diffusion behavior. For demonstration purposes, the `RunModel` is the Peras prototype/reference simulation describe in an earlier section of this document. Other implementations can be wired into the conformance tests via inter-process communication techniques.

```console
$ peras-simulation-test --match "/Peras.Conformance.Test/" --qc-max-success=1000

Peras.Conformance.Test
  Prototype node
    Simulation respects model [✔]
      +++ OK, passed 1000 tests.

      Action polarity (50500 in total):
      100.000% +

      Actions (50500 in total):
      38.487% +NewVote
      30.816% +Tick
      30.697% +NewChain

Finished in 4.7193 seconds
1 example, 0 failures

```

## Lessons learned from experiments with Agda-to-Haskell workflows

Aside from the workflow that we finally settle upon and that is described above, we explored several workflows for connecting the relational specification in Agda to `quickcheck-dynamic` tests in Haskell. This involves accommodating or working around several tensions:

- The relational specification uses the Agda Standard Library, which is not compatible with `agda2hs`.
    - Many of the Agda function names containing unicode characters or name patterns are not valid Haskell identifiers.
    - The MAlonzo representation of primitive types such as `Maybe` or tuples differs from the `agda2hs` representation of them in Haskell.
    - Type erasure via `@0` in Agda can remove non-essential portions of an Agda type that depend upon the standard library.
    - The use of any non-compatible identifiers or types in the arguments or implementation of an Agda function prevents its use in Haskell.
    - Module parameters appear in the export of functions made by `agda2hs`.
- The MAlonzo code generated by Agda's GHC backend contains mangled names, making it difficult to call from Haskell.
    - The `{-# COMPILE GHC ... as ... #-}` pragmas are not comprehensive enough to deeply rename Agda constructs for use in Haskell.
    - Judicious use of the `FOREIGN` and `COMPILE` pragmas for both the `GHC` and `AGDA2HS` backends can achieve a seamlessness that avoids ever having to deal with mangled names. The basic strategy is to use Agda to define types that can be exported to Haskell, but then to import those back into Agda for its use in MAlonzo.
        - The data types used by Haskell clients must be created use `Haskell.Prelude` and be created by `agda2hs` via the `{-# COMPILE AGDA2HS ... #-}` pragma.
            - Types involving natural numbers must be hand-coded using `{-# FOREIGN AGDA2HS ... #-}` because they compile to `Integer` in `MAlonzo` but to `Natural` in `agda2hs`.
            - Fields may not contain identifiers that violate Haskell naming requirements.
        - Those types are used as the concrete implementation in the very module where they are defined via the `{-# COMPILE GHC ... = data ... #-}` pragma.
        - Functions that are called by Haskell are annotated with the `{-# COMPILE GHC ... as ... #-}` pragma.
            - Every argument must be of a type that was generated with `{-# COMPILE AGDA2HS #-}` or is a basic numeric type or unit.
            - Functions cannot have arguments using natural numbers, tuples, `Maybe` etc.
            - Functions may contain identifiers that violate Haskell naming requirements.
        - The `agda --compile --ghc-dont-call-ghc --no-main` command generates mangled Haskell under `MAlonzo.Code.Peras`, except that is uses the unmangled types in `Peras` and has unmangled function names.
- The situation would be far simplier if one could use a pure Agda state-machine testing framework instead of having to export code to Haskell and then test there.
- The `StateModel` and `RunModel` of `quickcheck-dynamic` seem a little out of sync with this use case where the model and its properties are known to be correct because of Agda proofs and only the implementation is being tested.

The following picture attempts to clarify the relationship between Agda and Haskell as it has been explored in a hybrid Agda/Haskell specification/testing implementation:

* Agda code relies on the Agda _Standard Library_ which provide much better support for proofs than `agda2hs` and Haskell's `Prelude` obviously
* Therefore Haskell code needs to depend on this stdlib code which is problematic for standard types (Eg. numbers, lists, tuples, etc.)
* The Agda code separates `Types` from `Impl`ementation in order to ease generation
* `Types` are generated using agda2hs to provide unmangled names and simple structures on the Haskell side
* `Impl` is generate usign GHC to enable full use of stdlib stuff, with toplevel _interface_ functions generated with unmangled names
* `Types` are also taken into account when compiling using GHC but they are only "virtual", eg. the compiler makes the GHC-generated code depend on the `agda2hs` generated types
* Hand-written Haskell code can call unmangled types and functions

![Agda-Haskell Interactions](../diagrams/agda-haskell-interactions.jpg)

We used `agda` to generate `MAlonzo`-style Haskell code for the experimental Peras executable specification, [`Peras.QCD.Node.Specification`](https://github.com/input-output-hk/peras-design/blob/3d36761e5c72c55826d9dce1adf0dacdde4d7e3d/src/Peras/QCD/Node/Specification.agda#L1). A new `quickcheck-dynamic` test compares the `MAlonzo` version against the `agda2hs` version: these tests all pass, but the `MAlonzo` version runs significantly slower, likely because it involves more than two hundred Haskell modules.

* `agda2hs` version: 4m 45.206s (250 tests)
* `MAlonzo` version: 10m 46.280s (250 tests)

We also experimented with create a small embedded monadic DSL for writing the Peras specification in Agda in a manner so that it reads as pseudo-code understandable by non-Agda and non-Haskell programmers. For example, the executable specification for *fetching* looks like the following in this eDSL:

```agda
-- Enter a new slot and record the new chains and votes received.
fetching : List Chain → List Vote → NodeOperation
fetching newChains newVotes =
  do
    -- Increment the slot number.
    currentSlot ≕ addOne
    -- Update the round number.
    u ← peras U
    now ← use currentSlot
    currentRound ≔ divideNat now u
    -- Add any new chains and certificates.
    updateChains newChains
    -- Add new votes.
    votes ≕ insertVotes newVotes
    -- Turn any new quorums into certificates.
    newCerts ← certificatesForNewQuorums
    certs ≕ insertCerts newCerts
    -- Make the heaviest chain the preferred one.
    boost ← peras B
    heaviest ← heaviestChain boost <$> use certs <*> use chains
    preferredChain ≔ heaviest
    -- Record the latest certificate seen.
    updateLatestCertSeen
    -- Record the latest certificate on the preferred chain.
    updateLatestCertOnChain
    -- No messages need to be diffused.
    diffuse
```

There are still opportunities for syntactic sugar that would make the code more readable, but dramatic improvements probably are not feasible in this approach. Perhaps a more readable approach would be to express this in a rigorously defined, standardized pseudo-code language, which could be compiled to Agda, Haskell, Rust, Go, etc. Other lessons learned follow:

- Lenses improve readability.
- Using a `List` for the "set" data structure of the paper creates inefficiencies in the implementation.
    - Set invariants are not trivially enforced.
    - Access and query functions are slow.
- It might be difficult prove this executable specification matches the properties that are being formally proved.
- Even though the Agda code is written to look imperative, it has quite a few artifacts of functional style that could be an impediment to some implementors.
    - It might be better to use `let` statements instead of `← pure $`. Unfortunately, it would be quite difficult to design an assignment operator to replace monadic `let` in Agda.
    - The functional style avoids introducing lots of intermediate variables, but maybe that would be preferable to using functions as modifiers to monadic state (e.g., `_≕_ : Lens' s a → (a → a) → State s ⊤`).
    - The `use` and `pure` functions could be eliminated by defining operators (including logical and arithmetic ones) that hide them.
- Overall, the Agda code is more verbose than the textual specification.
- It might be difficult to create Agda code that is simultaneously easily readable by mathematical audiences (e.g., researchers) and software audiences (e.g., implementors).
- Quite a bit of boilerplate (instances, helper functions, lenses, State monad, etc.) are required to make the specification executable.
- Creating a full eDSL might be a better approach, but that would involved significantly more effort.


# Community feedback

- **Varied Needs**: Stakeholders have varying levels of technical expertise. Some require rigorous specifications (Agda, research papers), while others prefer high-level explanations and practical resources like pseudocode, diagrams, and data structure descriptions.
- **Accessibility**: There is a strong preference for CIPs (Cardano Improvement Proposals) to be understandable to a wider and diverse audience. dApp builders want to know if and what changes are required from them - i.e. how many confirmations they have to wait for before they can display to the user that the action is confirmed, SPOs want to know how much extra resources are neede and what effort is required for installation, etc.
- **Transparency and Rationale**: Stakeholders want clarity on the cost of Peras (in terms of ADA, fees, or resources) and a clear explanation of why this solution is possible now when it wasn't before.
- **Speed and Efficiency**: Some stakeholders emphasize the need for a faster development process, suggesting that the formal specification could be developed in parallel with the technical implementation.
- **Timeline**: Stakeholders are curious about the timeline for Peras development and implementation.

# Resources impact of Peras

## Network

We did some quick research on network pricing for a few major Cloud or VPS providers: https://docs.google.com/document/d/1JJJk4XPqmP61eNWYNfqL8FSbKAF9cWazKWFZP6tMGa0/edit

Comparison table in USD/mo for different outgoing data transfer volumes expressed as bytes/seconds and similar VMs (32GB RAM, 4+ Cores, 500GB+ SSD disk). The base cost of the VM is added to the network cost to yield total costs:

| Provider     | VM     | 50kB/s | 125kB/s | 250kB/s |
|--------------|--------|--------|---------|---------|
| DigitalOcean | $188   | $188   | $188    | $188    |
| Google Cloud | $200   | $213.6 | $234    | $268    |
| AWS          | $150 ? | $161.1 | $177.9  | $205.8  |
| Azure        | $175   | $186   | $202    | $230    |
| OVH          | $70    | $70    | $70     | $70     |
| Hetzner      | $32    | $32    | $32     | $32     |

Notes:

* the AWS cost is quite hard to estimate up-front, obviously on purpose. The $150 base price is a rough average of various instances options in the target range
* Google, AWS and Azure prices are based on 100% uptime and at least 1-year reservation for discounts

![Typical node inbound & outbound traffic](../static/img/node-average-traffic.jpg)

Assuming $U ~ 100$, a committee size of 2000 SPOs, a single vote size of 700 bytes, means we will be adding 14kB/s to the expected traffic to each node. For an AWS hosted SPO, which represents a [significant share](https://pooltool.io/networkhealth) of the SPOs, this would lead to cost increase of $3.4/mo (33GB times $0.11/GB).

## Storage

## CPU

# Conclusion

## The case for Peras

Peras provides demonstrably fast settlement without weakening security or burdening nodes. The settlement time varies as a function of the protocol-parameter settings and the prevalence of adversarial stake.

> [!IMPORTANT]
> Provide here a summary table of settlement time vs adversarial stake for a selection or protocol parameters.

The impact of Peras upon nodes falls into four categories: bandwidth, CPU, memory, bandwidth, and storage. Our ΔQ studies demonstrate that diffusion of Peras votes and certificates consumes minimal bandwidth and would not interfere with other node operations such as memory-pool and block diffusion. We have provided evidence that the CPU time required to construct and verify votes and certificates is much smaller than the duration of a voting round. Similarly, the memory needed to cache votes and certificates and the disk space needed to persist certificates is trivial compared to the memory needed for the UTXO set and the disk needed for the blocks.

> [!IMPORTANT]
> Put specific numbers in the paragraph above.

In terms of development impacts and resources, Peras requires only a minimal modification to the ledger CDDL and block header. Around cool-down periods, a certificate hash will need to be included in the block header and the certificate itself in the block. Implementing Peras does not require any new cryptographic keys, as the existing VRF/KES will be leveraged. It will require an implementation of the ALBA algorithm for creating certificates. It does require a new mini-protocol for diffusion of votes and certificates. The node's logic for computing the chain weight needs to be modified to account for the boosts provided by certificates. Nodes will have to persist all certificates and will have to cache unexpired votes. They will need a thread (or equivalent) for verifying votes and certificates. Peras only interacts with Genesis and Leios in the chain-selection function and it is compatible with the historical evolution of the blockchain. A node-level specification and conformance test will also need to be written.

> [!WARNING]
> Dare we assert that implementation of Peras in the Cardano node would take approximately three person years, provided the team already has familiarity with the node and stays focused?

In no way does Peras weaken any of the security guarantees provided by Praos or Genesis. Under strongly adversarial conditions, where an adversary can trigger a Peras voting cool-down period, the protocol in essence reverts to the Praos protocol, but for a duration somewhat longer than the Praos security parameter. Otherwise, settlement occurs after each Peras round. This document has approximately mapped the trade-off between having a short duration for each round (and hence faster settlement) versus having a high resistance to an adversary forcing the protocol into a cool-down period. It also estimates the tradeoff between giving chains a larger boost for each certificate (and hence stronger anchoring of that chain) versus keeping the cool-down period shorter.

## Recommended next steps

- Complete proofs.
    - Voting strings.
    - Liveness of the protocol.
    - Soundness of the executable specification.
    - Synchronize with Praos formalization.
    - Prepare a publication or online supplement.
- Complete conformance suite.
    - Tests for non-voting parts of the protocol.
    - Serialization format and inter-process communication for testing third-party implementations.
    - Package for easy installation and use.
- Recommend parameter values.
    - Seek and analyze stakeholder requirements, especially from partner chains.
    - Develop a parameter-evaluation tool (based on the Markov-chain simulator) that provides a full set of impact metrics for a given set of parameters.
- Reach out to stakeholders.
    - Populate website with latest results.
    - Online versions of all analysis, simulation, and visualization tools.
    - Organize a stakeholder workshop and/or a Intersect Consensus Technical WG.
        - Feedback on specification format.
        - Feedback on conformance suite.
        - Feedback on and refinement of the draft CIP.
- Tooling fixes and enhancements
    - Improve the usability, efficiency, and testing of the ΔQ software.
        - Provide out-of-the-box and possibly interactive visualization.
        - Provide faster numeric computations (e.g. using discretized CDFs and fast vector operations, possibly offloaded to GPU).
        - Provide additional combinators (e.g., quantile-arrival time) for the DSL.
    - Improve the protocol visualizer.
        - Allow users to inject adversarial behavior or network disruptions (e.g., "split brain" scenarios).
        - Make visualization scalable in the browser to long chains (i.e., hours of simulated block production) and large networks.
    - Improve the prototype simulator.
        - Add an efficient implementation suitable for large networks and long simulations.
        - Create a simple DSL for inputting simulation scenarios for both honest and adversarial behavior.
    - Improve the Markov-chain analyzer.
        - Add a DSL for defining scenarios.
        - Add visualization and analysis tools.
    - Collaborate with higher-resolution network simulation efforts, potentially implementing Peras on them.
        - PeerNet
        - ce-netsim
- Move from the "pre-alpha" to the "alpha" version of the protocol.
    - Requires completion of the Peras paper.
    - Formalize and implement the preagreement YOSO abstraction.
