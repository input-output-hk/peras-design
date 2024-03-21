---
title: Peras Technical Report #1
author: Peras Team
---

The goal of this document is to provide a detailed analysis of the Peras protocol from an engineering point of view, based upon the work done by the _Innovation team_ since January 2024.

# Previous work

## Peras Workshop

### Questions about Peras

* How do you detect double voting? Is double voting possible? How can the voting state be bounded?
* How are the voting committee members selected? What are the properties of the voting committee?
* Where should votes be included: block body, block header, or some other aggregate
* Under what circumstance can a cool down be entered?
* How significant is the risk of suppressing votes to trigger a cooldown period?
* Should vote contributions be incentivized?
* How much weight is added per round of voting?
* How to expose the weight/settlement of a block to a consumer of chain data, such as a wallet?
* Can included votes be aggregated into an artifact to prove the existence of votes & the weight they provide?

### Potential jugular experiments for Peras

* Network traffic simulation of vote messages
* Protocol formalization & performance simulations of Peras
* Optimal look-back parameter (measured in number of slots) within a round
  * Historic analytical study (n-sigma for reliability based on the number of 9s desired)
* Chain growth simulations for the accumulation of vote data
* Added chain catch-up time
* Cost of defusing votes and blocks that contain votes
* Need to refine: Voting committee selection via sampling needs to define how to analyze the needed properties of the committee.
* Later SRL: framing for vote packing to improve diffusion.

### SRL

| Questions to resolve                                                                                                 | Status                                          |
|----------------------------------------------------------------------------------------------------------------------|-------------------------------------------------|
| A concept formulated?                                                                                                | Done                                            |
| Basic scientific principles underpinning the concept identified?                                                     | Done                                            |
| Basic properties of algorithms, representations & concepts defined?                                                  | Done                                            |
| Preliminary analytical studies confirm the basic concept?                                                            |                                                 |
| Application identified?                                                                                              | Done                                            |
| Preliminary design solution identified?                                                                              | Done, provided by research                      |
| Preliminary system studies show the application to be feasible?                                                      |                                                 |
| Preliminary performance predictions made?                                                                            | Done                                            |
| Basic principles coded?                                                                                              |                                                 |
| Modeling & Simulation used to refine performance predictions further and confirm benefits?                           |                                                 |
| Benefits formulated?                                                                                                 |                                                 |
| Research & development approach formulated?                                                                          | Done                                            |
| Preliminary definition of Laboratory tests and test environments established?                                        | Preliminary definition of Laboratory tests only |
| Experiments performed with synthetic data?                                                                           |                                                 |
| Concept/application feasibility & benefits reported in scientific journals/conference proceedings/technical reports? |                                                 |

# Protocol Specification

## Overview

This diagram attempts at depicting graphically how the Peras protocol works over a period of time. A high-fidelity version is [available](/docs/diagrams/peras-with-certs.pdf).

![Peras Protocol Overview](../diagrams/peras-with-certs.jpg)


## Pseudo-code

* Researchers' pseudo-code is detailed in [this document](https://docs.google.com/document/d/1w_jHsojcBxZHgGrr63ZGa4nhkgEpkL6a2cFYiq8Vf8c/edit)

## Agda Specification

* Present the detailed specificaiton of the protocol in Agda
* Protocol properties
* link with q-d properties

## Pending questions

### Certificates

> Detail requirements for Peras voting certificates and possible impacts on the model

# Network Performance Analysis

This section provides high-level analysis of the impact of Peras protocol on the existing Cardano network, using [ΔQSD methodology](https://iohk.io/en/research/library/papers/mind-your-outcomes-the-dqsd-paradigm-for-quality-centric-systems-development-and-its-application-to-a-blockchain-case-study/). In order to provide a baseline to compare with, we first applied ΔQ to the existing Praos protocol reconstructing the results that lead to the current set of paremeters defining the performance characteristics of Cardano, following section 4 of the aforementioned paper. We then used the same modelling technique taking into account the specificities of Peras protocol insofar as they impact the core _outcome_ of the Cardano network, namely _block diffusion time_.

Note that one of the sub-goals for Peras project is to collaborate with PNSol, the original inventor of ΔQ methodology, to improve the usability of the whole method and promote it as a standard tool for designing distributed systems.

## Baseline - Praos ΔQ Modelling

### Model overview

Here is a graphical representation of the _outcome diagram_ for the ΔQ model of Cardano network under Praos protocol:

![Outcome diagram for Praos](/docs/diagrams/praos-delta-q.svg)

This model is based on the following assumptions:
* Full block diffusion is separated in a number of steps: request and reply of the block header, then request and reply of the block body,
* Propagating a block across the network might require several "hops" as there's not a direct connection between every pair of nodes, with the distribution of paths length depending on the network topology,
* We have not considered probability of loss in the current model.

The block and body sizes are assumed to be:
* Block header size is smaller than typical MTU of IP network (eg. 1500 bytes) and therefore requires a single roundtrip of TCP messages for propagation,
* Block body size is about 64kB which implies propagation requires several TCP packets sending and therefore takes more time.

> [NOTE!]
> As the Cardano network uses TCP/IP for its transport, we should base the header size on the [Maximum Segment Size](https://en.wikipedia.org/wiki/Maximum_segment_size), not the MTU.
> This size is 536 for IPv4 and 1220 for IPv6.

Average latency numbers are drawn from table 1 in the paper and depend on the (physical) distance between 2 connected nodes:

| Distance | 1 segment RTT (ms) | 64 kB RTT (ms) |
|----------|-------------------|----------------|
| Short    | 12                | 24             |
| Medium   | 69                | 143            |
| Long     | 268               | 531            |

For each step in the diffusion of block, we assume an equal ($frac{1}{3}$) chance for each class of distance.

> [NOTE!]
> The actual block body size at the time of this writing is 90kB, but for want of an actual delay value for this size, we chose the nearest increment available.
> We should actually measure the real value for this block size.

We have chosen to define two models of ΔQ diffusion, one based on an average node degree of 10, and another one on 15. Note the current target valency for cardano-node's connection is 20 but the actual value might be lower in practice (?). Table 2 gives us the following distribution of paths length:

| Length | Degree = 10 | Degree = 15 |
|--------|-------------|-------------|
| 1      | 0.40%       | 0.60%       |
| 2      | 3.91%       | 8.58%       |
| 3      | 31.06%      | 65.86%      |
| 4      | 61.85%      | 24.95%      |
| 5      | 2.78%       | 0           |

These numbers are reflected (somewhat inaccurately) in the above graph, representing the probabilities for the number of hops a block will have to go through before reaching another node.

### Modeling process

We have experimented with three different libraries for encoding this baseline model:
1. Original [ΔQ library](https://github.com/DeltaQ-SD/pnsol-deltaq-clone) built by Neil Davies, which uses randomized sampling to graph the _Cumulative Distribution Function_ resulting from the ΔQ model,
2. A library for [algebraic representation](https://github.com/DeltaQ-SD/Artjoms) of ΔQ models built to support the [Algebraic Reasoning with Timeliness](https://arxiv.org/pdf/2308.10654v1.pdf) paper, which uses discretization of proability density functions to approximate CFDs resulting from the various ΔQ language combinators,
3. Another recent library built by Peter Thompson to represent ΔQ probability distributions using [piecewise polynomials](https://github.com/DeltaQ-SD/dqsd-piecewise-poly), which should provide high-fidelity CDFs.

Library 2 was used to express the _outcome diagram_ depicted above using so-called _O language_, but while we were able to encode the model itself, the resulting computation of _CDFs_ for composite expressions resulting from _convolution_ of atomic expressions turned out to be unusable, yielding CDFs with accumulated probability lower than 1 even though we did not model any loss. Library 3, although the most promising to provide accurate models, turned out to be unsatisfactory as we were not able to produce proper numerical representations of a CDF for more complex expressions.

Using code from library 1, we were able to write the following ΔQ expressions to represent our Cardano model:

```haskell
oneMTU =
    fromQTA @SimpleUniform
        [(0, 0), (1 % 3, 0.012), (2 % 3, 0.069), (3 % 3, 0.268)]
blockBody64K =
    fromQTA @SimpleUniform
        [(0, 0), (1 % 3, 0.024), (2 % 3, 0.143), (3 % 3, 0.531)]
headerRequestReply = oneMTU ⊕ oneMTU -- request/reply
bodyRequestReply = oneMTU ⊕ blockBody64K -- request/reply
oneBlockDiffusion = headerRequestReply ⊕ bodyRequestReply

combine [(p, dq), (_, dq')] = (⇋) (toRational $ p / 100) dq dq'
combine ((p, dq) : rest) = (⇋) (toRational $ p / 100) dq (combine rest)

multihops = (`multiHop` oneBlockDiffusion) <$> [1 ..]

pathLengthsDistributionDegree15 =
    [0.60, 8.58, 65.86, 24.95]
hopsProba15 = zip (scanl1 (+) pathLengthsDistributionDegree15 <> [0]) multihops
deltaq15 = combine hopsProba15
```

Then using `empiricalCDF` computation with 5000 different samples yield the following graph:

![Praos ΔQ Model CDF](/docs/diagrams/plot-hops-distribution.svg)

To calibrate our model, we have computed an empirical distribution of block adoption time[^2] observed on the mainnet over the course of 4 weeks (from 22nd February 2024 to 18th March 2024), as provided by https://api.clio.one/blocklog/timeline/. The raw data is provided as a file with 12 millions entries similar to:

```
9963861,117000029,57.128.141.149,192.168.1.1,570,0,60,30
9963861,117000029,57.128.141.149,192.168.1.1,540,0,60,40
9963861,117000029,158.101.97.195,150.136.84.82,320,0,10,50
9963861,117000029,185.185.82.168,158.220.80.17,610,0,50,50
9963861,117000029,74.122.122.114,10.10.100.12,450,0,10,50
9963861,117000029,69.156.16.141,69.156.16.141,420,0,10,50
9963861,117000029,165.227.139.87,10.114.0.2,620,10,0,70
9963861,117000029,192.99.4.52,144.217.78.44,460,0,10,100
9963861,117000029,49.12.89.235,135.125.188.228,550,0,20,50
9963861,117000029,168.119.9.11,3.217.90.52,450,150,10,50
...
```

Each entry provides:

* Block height,
* Slot number,
* Emitter and receiver's IP addresses,
* Time (in ms) to header announcement,
* then additional time to fetch header,
* time to download block,
* and finally time to adopt block on the receiver.

Therefore the total time for block diffusion is the sum of the last 4 columns.

This data is gathered through a network of over 100 collaborating nodes that agreed to report various statistics to a central aggregator, so it's not exhausitve and could be biased.
The following graph compares this observed CDF to various CDFs for different distances (in the graph sense, eg. number of hops one need to go through from an emitting node to a recipient node) between nodes.

![Multiple hops & empirical CDF](/docs/diagrams/plot-praos-multi-hops.svg)

While this would require some more rigorous analysis to be asserted in a sound way, it seems there is a good correlation between empirical distribution and 1-hop distribution, which is comforting as it validates the relevance of the model.

## Peras ΔQ Model

Things to take into account for modelling peras:
* Impact of the size of the certificate: If it increases the size of the header too much,

* ΔQ model of Peras
  * model the impact of larger headers
  * more data to pull from nodes

* impact on block diffusion
* impact on security?

## Impact of Load congestion

* load congestion

# Simulations

# Integration in cardano-node

## Networking

* adding new protocol similar to ChainSync or TxSubmission
  * votes are propagated as hashes at the header level and pulled by the consumer downstream

## Consensus

* impact of having to deal with dangling votes constantly to select chain
* new storage for votes
* impact of verification of votes

## Resources

* how much resources requires Peras on top of Praos?

# Conclusion

## Future work

[^2]:  This data was kindly provided by [Markus Gufler](https://www.linkedin.com/in/markus-gufler)
