---
title: "Peras Technical Report #2"
author:
  - Arnaud Bailly
  - Brian W. Bush
  - Yves Hauser
date: 2024-04-17
monofont: Monaco
---


# Votes & Certificates

## Votes

### Background

Some references:

* https://medium.com/witnet/cryptographic-sortition-in-blockchains-the-importance-of-vrfs-ad5c20a4e018
  EC signatures are not unique, and malleable, therefore not usable for sortition
* The original paper from [Micali et al.](https://people.csail.mit.edu/silvio/Selected%20Scientific%20Papers/Pseudo%20Randomness/Verifiable_Random_Functions.pdf) introducing _Verifiable Random Functions_
* The VRF-based committee election used by [OASIS](https://docs.oasis.io/adrs/0010-vrf-elections/) and the [RFC9381](https://datatracker.ietf.org/doc/rfc9381/) specification
* Some article about how it's actually implemented in the [Cardano lottery](https://cexplorer.io/article/how-does-the-lottery-work-on-the-cardano-network)

  > VRF Evaluate algorithm has multiple inputs. Besides others, these
  > include the slot ID for which the lottery is currently running,
  > and 2/3 of all VRF output from the previous epoch, from which a
  > single hash (value) is created. This hash is also called a
  > Nonce. Nonce makes it impossible to compute VRF results too far in
  > advance.

  This means that the nonce is computable only 1.5 days before the epoch ends, or 288000 slots
* Actual computation happens in the [Praos](https://github.com/input-output-hk/ouroboros-consensus/blob/1a5502edba18a297e9d2ddece4f6bb89abead950/ouroboros-consensus-protocol/src/ouroboros-consensus-protocol/Ouroboros/Consensus/Protocol/Praos.hs#L468) module in the consensus code. New nonce is accumulated with `eta`, a value computed from the header VRF proof by [vrfNonceValue](https://github.com/input-output-hk/ouroboros-consensus/blob/1a5502edba18a297e9d2ddece4f6bb89abead950/ouroboros-consensus-protocol/src/ouroboros-consensus-protocol/Ouroboros/Consensus/Protocol/Praos/VRF.hs#L122). This function implements [range extension](https://iohk.io/en/research/library/papers/on-uc-secure-range-extension-and-batch-verification-for-ecvrf/)

### Peras Votes

> How does this translate for committee based sortition for Peras (and ultimately Leios?)
> In particular, what's the nonce we should use for generating a random vote? Could we reuse the same nonce than for leader election? Seems like not a so good idea...

Peras votes follow the same principles as the Praos Leadership election.

## ALBA Certificates

* [ALBAs](https://iohk.io/en/research/library/papers/approximate-lower-bound-arguments/) appears to provide a good basis for Peras certificates
* The [Prototype implementation in Haskell](https://github.com/cardano-scaling/alba) provides some evidence this construction could be feasible in the context of Peras

### Proving & Verification time

The following picture plots the time needed (in milliseconds) to build certificate for varying number of votes, assuming a security parameter of 128, honest share of 67% and vote size of 256 bytes.

![ALBA Proving time](../diagrams/alba-cpu.svg)

We can observe that even in some extreme cases proving time stays consistently under 20ms and on the average is between 10 and 15ms for even large number of items. The wild variation in proving time for different number of input set is explained by the non-deterministic nature of the algorithm: We construct the proof through depth-first search, by repeatedly comparing hash values _modulo_ the expected number of honest items, so the number of comparisons and hashes to make may vary significantly depending on how the ordering of the list of items.

It's worth considering whether or not this dependency on the ordering of the items could be an attack vector as proving time could easily explode in case we need to explore more than a small fraction of the tree.

Verification time has not been plotted but is lower than 1ms in all the cases considered as it is tied to the number of hash computation one has to make which is $O(u + s_p)$.

### Certificate size

For a given set of parameters, eg. fixed values for $\lambda_{sec}$, $\lambda_{rel}$, and $n_p/n_f$ the proof size is perfectly linear and only depends on the size of each vote:

![Proof size / vote size](../diagrams/alba-proof-size-fixed-params.svg)

Varying the security parameter and the honest votes ratio for a fixed set of 1000 votes of size 200 yields the following diagram, showing the critical factor in proof size increase is the $n_p/n_f$ ratio: As this ratio decreases, the number of votes to include in proof grows superlinearly.

![Proof size vs. λ and honest votes ratio](../diagrams/alba-proof-size-lambda.svg)
