---
sidebar_label: 'Introduction'
sidebar_position: 1
---

# What is Peras?

Peras, or more precisely Ouroboros Peras, is an extension of [Ouroboros Praos](https://iohk.io/en/research/library/papers/ouroboros-praos-an-adaptively-secure-semi-synchronous-proof-of-stake-protocol/) that addresses one of the known issues of blockchains based on Nakamoto-style consensus, namely _settlement time_. Peras achieves that goal while being _self-healing_, preserving the security of Praos, and being light on resources.

:::important

This site documents the **pre-alpha** version of the protocol, which already provides strong guarantees of settlement bounds, adapts to fluctuating participation, and can recover from failures.
There's still research work ongoing to refine the protocol and provide even better guarantees in the face of high adversarial stake.

:::

## What is settlement?

Recall that in Cardano, like in all Nakamoto-style consensus blockchains, new blocks are added to the chain in a probabilistic way. The protocol gives each _Stake-Pool Operator_ (SPO) the right to _forge_ a new block every slot depending on the amount of stake they represent, and the protocol parameters are defined in such a way that one new block is created every 20 slots. A newly forged block is then propagated across the network and adopted by other nodes following the _longest chain_ principle: when a given node receives a new chain, i.e. a chain extended with a new block, it adopts it as its own if and only if the new chain is longer than any other previously known chain.

Because of the distributed, decentralized and probabilistic nature of the protocol, it's perfectly possible that two or more chains coexist simultaneously across the network:

* More than one SPO can be elected to create a new block at approximately the same time,
* Blocks take some time to reach all network nodes giving rise to the possibility of different nodes having different views of the best chain,
* Nodes come and go,
* Transactions included in blocks also need to travel across the network before reaching the SPO that will forge a block including them,
* ...

This phenomenon is well known as _forking_: a node's current best chain can be superseded by a new best chain which is very similar but for the last few blocks.

For an end-user submitting a transaction to the network, this raises the all important question: _When can they consider their transaction will never be rolled back_? In other words, when can they consider the transaction to be _settled_?

In the context of this work, settlement is therefore considered from an _observability_ perspective (pun intended):

> Settlement time is the duration after which a block (or transaction) added to node's best chain has a negligible probability of being rolled back because of a fork

## What's current settlement value?

It turns out giving a precise answer to this question is convoluted, and depends on various characteristics of the protocol, most notably the expected diffusion time (Δ) across the network, and assumptions about the fraction of _adversarial stake_. When reasoning about blockchain properties, the relative power between _honest_ nodes, i.e. the nodes that respect the protocol, and _adversarial_ nodes, i.e. the ones that can do whatever they want, is extremely important.

Ouroboros Praos has been [proven to be safe](https://iohk.io/en/research/library/papers/ouroboros-praos-an-adaptively-secure-semi-synchronous-proof-of-stake-protocol/) up to 50% adversarial stake: as long as the adversary does not control majority of the stake, it guarantees various key properties of the chain which we can summarize informally by saying all honest nodes will ultimately agree on the same, honest, chain. However, this robustness comes at a price which is the time nodes have to wait to consider a block (therefore a chain) _settled_.

In Cardano a node considers a block definitely _settled_, or _immutable_, once it is $k$ blocks behind the current tip of its best chain, where $k=2160$. Assuming average interblock arrival rate of 20 seconds, this means a block is settled after about 12 hours.

### How is $k$ determined?

The question of settlement time has been given a mathematically rigorous treatment in the paper [Practical Settlement Bounds for Longest-Chain consensus](https://iohk.io/en/research/library/papers/practical-settlement-bounds-for-longest-chain-consensus/), whose main findings can be summarized in the following picture.

![Fork probability for 10% adversarial stake](/img/settlement-failure-probability.png#scale50)

This graph reads as follows: assuming an adversarial stake of at most 10%, and a diffusion bound Δ of 5 seconds, the probability of a block being rolled back after a node has observed 20 blocks is 0.001%.

If Δ drops to 2s, e.g. if we consider the network to be faster and more reliable, then this probability also drops to 0.0001%.

On Cardano's mainnet, because of the much more stringent security requirements, we'll require a much lower failure rate of $2^60$. Assuming the adversary has at most 35% stake and huge _grinding power_, and network propagation delay $Δ=5s$, the same computation yields roughly the current value of $k$, i.e. a bit over 2000 blocks.

### What happens in practice?

In practice we know that _core nodes_, e.g.. block producing nodes or relays, seldom observe forks longer than 2 blocks. And most wallets, explorers, DApps, and other end-user facing systems provide feedback about transaction settlement under the name _number of confirmations_ which is exactly the same thing: the number of blocks past current best chain's tip of the block containing the transaction. A _number of confirmations_ higher than 10 is considered _high_.

However, it's quite possible an adversary is "lurking in the shadows", building a _private chain_ and awaiting the best time to take over the network and roll back transactions which would have normally be considered safe. This idea of private chains or "selfish mining" has been detailed in the classical paper [Majority is not enough](https://arxiv.org/abs/1311.0243), and it is critical to address this problem to ensure the security of any decentralised blockchain. This explains why we observe such a difference between the theoretical settlement bound provided by the protocol, and the practically observed one.

## How does Peras work?

Peras exists to bridge that gap and make settlement bounds closer to practical values, e.g. to dramatically decrease the probability of a fork even after only a few blocks.

The key idea of Peras is to use stake-based voting to _boost_ the weight of blocks on which a majority  of SPOs agree. The chain selection rule is then modified to select the _heaviest_ chain instead of the _longest_ one.

### How does the protocol work?

From a high-level perspective, the protocol works as follows:

* At the beginning of each _round_, a randomly selected _committee_ of SPOs _vote_ for the block at a fixed depth from their current best chain tip, with each vote having a weight correlated to the SPO's stake,
* Time is divided in fixed-length _rounds_ with a duration in the order of a few tens of slots,
* The votes are broadcast to all nodes across the network,
* If a node sees a _quorum_ of vote for the same block, it can issue a _certificate_ which _boosts_ the weight of this block,
* Certificates are also diffused across the network on demand, to those nodes which don't have equivalent votes,
* If a node does not receive a quorum for a round, either from votes or a certificate, it enters a _cooldown_ period during which any vote or certificate are _ignored_,
  * A node exits cooldown after a fixed number of rounds, and starts voting again.
  * When it enters cooldown, a block producer also appends the latest certificate to the block it forges.

### What are the benefits?

The exact effect of Peras depends on the values of various protocol parameters which are detailed in the [Technical Report](/docs/reports/tech-report-2). Based on the [recommendations](/docs/reports/tech-report-2#recommendations-for-peras-parameters) provided in the report

> anyone seeing a transaction appearing in a block need wait no more
> than two minutes to be certain whether the transaction is on the
> preferred chain (effectively permanently, less than a one in a
> trillion probability even at 45% adversarial stake) versus having
> been discarded because of a roll back

Importantly, Peras does not change the underlying security guarantees of Ouroboros Praos, and reverts to it in the event of a cooldown. Moreover, it adapts to fluctuating participation of SPOs and can recover from temporary "failures", e.g. if an adversary manages to temporarily reach a _quorum_, they only will be able to takeover the chain if they manage to maintain that superiority over time, otherwise the honest parties will take over.

## Where to go from here?

A lot more details about Peras protocol can be found in various places:

* For detailed analysis of the protocol, please refer to [Technical Report #2](/docs/reports/tech-report-2)
* For a formal description, refer to the [Agda Specification](pathname:///agda_html/Peras.SmallStep.html)
* Conformance tests are available in the [Peras repository](https://github.com/input-output-hk/peras-design)
* A live simulation of the protocol is available https://peras-simulation.cardano-scaling.org


<!--  Localwords:  Peras Ouroboros Praos Nakamoto SPO observability
 -->
