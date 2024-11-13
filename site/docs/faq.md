---
sidebar_label: 'F.A.Q.'
sidebar_position: 2
---

# Ouroboros Peras FAQ

## Where is the Ouroboros Peras protocol defined?

Ouroboros Peras (henceforth, Peras) is defined in the Cardano Improvement Proposal (CIP) [Ouroboros Peras - Faster Settlement](https://github.com/cardano-foundation/CIPs/pull/872). The CIP motivates Peras, formally and informally specifies the protocol, and provides evidence that Peras significantly reduces settlement time without much impact on nodes’ operating costs.

## What are the benefits of Peras?

Peras dramatically improves the settlement time of Cardano transactions by having a committee of block-producing nodes periodically vote to certify blocks. Certified blocks decrease the likelihood of a rollback according to protocol parameters, so any transactions in (or preceding) those blocks, and therefore the chain they form, become effectively irreversible much faster than with Praos. Peras voting rounds may be as short as a minute or two, meaning that certified blocks appear that regularly and settle the preceding transactions at that frequency.

## Why is faster settlement beneficial to Cardano?

Faster settlement benefits use cases such as exchanges (both decentralized and centralized), bridges, partner chains, and DApps by providing effective assurances that a transaction will not be rolled back. In such use cases, the party would wait until they observe a certified block at or after their transaction.

## How do we know that Peras is safe?

Peras is backed by research that proves the protocol’s liveness, consistency, self-healing, and security properties. A detailed analysis of the protocol and its potential implementation has been conducted by a team of dedicated engineers over the course of 2024.

## Does Peras open Cardano to new types of attacks?

While Peras inherits the safety guarantees of Ouroboros Praos, adversaries selected for the Peras voting committee in a particular voting round might attempt to disrupt the voting process by choosing to withhold their votes or vote for non-preferred chains. This would prevent honest parties from forming a quorum of votes for a candidate block and delay settlement time. Such attacks become increasingly likely to succeed as the adversarial stake approaches 25% of the total stake, but the Peras protocol mitigates this problem by temporarily stopping voting if a quorum is not reached in each round.

## What is a ‘certified block’ in Peras?

A block that has received a quorum of votes from the Peras voting committee is considered to be ‘certified’ and is assigned some weight. While standard blocks have a weight of 1, blocks certified by a quorum of Peras votes have their weight boosted according to the protocol parameter B, therefore influencing nodes’ choice of the preferred chain.


## How does Peras voting affect a node’s selection of its preferred chain?

In Ouroboros Praos, nodes select their preferred chain following the longest chain rule. In Peras, nodes select their preferred chain following the heaviest chain rule. This implies that certified blocks have a higher impact than normal blocks on chain selection.
What does ‘cooldown period’ mean in Peras?

If the Peras voting committee fails to reach quorum, the protocol enters a 'cooldown' period, during which voting is suspended, and the protocol operates like Ouroboros Praos. This cooldown is necessary because a failure to reach quorum at some round could allow an attacker to complete the quorum later. By continuing this attack over multiple rounds, the attacker could at some point cause a significant reorganization of the chain, leading to a safety violation. During the cooldown, no voting or boosting occurs until the potential adversarial advantage is mitigated. After sufficient time for chain healing, restoration of chain quality, and assurance of a common chain prefix, the protocol emerges from the cooldown period and resumes voting.

## Does Peras change the cost of transactions or affect staking rewards?

Peras only affects the consensus protocol and has no impact on the cost of transactions. However, the voting process requires resources from stake pool operators (see below) and the community might decide to reward those.

## Will Peras require a hard fork?

Yes, because Peras changes the consensus protocol and the block structure.

## How will Peras affect stake pool operators (SPOs)?

Peras will modestly increase the cost of operating a block-producing Cardano node because it requires slightly more bandwidth than Praos. A recent analysis estimates that network traffic will increase by about 14 kB/s, which may cost an additional $3.8/month at current cloud computing prices.

## How does Peras affect Cardano blocks?

Peras leaves the Cardano block header unchanged, but it augments the block body with the option to record a Peras certificate. The size of the certificate depends upon the size of the Peras voting committee and the cryptographic technique used to create the certificate, but generally speaking, a Peras certificate might be approximately 50 kB.
In normal operating conditions Peras certificates will not be recorded in blocks. If the Peras protocol enters a ‘cooldown’ period however, one or two certificates will be included in blocks early on during cooldown. Overall, this rare inclusion of a certificate in a block body will have minimal impact on block utilization.

## When will Peras be available on the Cardano blockchain?

As the new constitution for Cardano comes into force, this decision will need to be voted for by the community.

## Does Peras conflict with Ouroboros Leios?

Peras modifies the chain selection algorithm of Ouroboros Praos to speed up settlement. Ouroboros Leios adds stake-based block endorsing to increase throughput. Thus, Peras deals with settlement speed and Leios deals with transaction volume. Leios can build on any base protocol, such as Praos or Peras, that possess a few specific properties. A recent video ‘Scaling Blockchain Protocols’ by Input | Output’s chief scientist Aggelos Kiayias discusses how Peras and Leios work together to improve settlement times and throughput on Cardano. It's worth noting that Peras and Leios use similar staked-based voting mechanisms, which implies Leios will benefit from developments required by Peras.

## Does Peras conflict with Ouroboros Genesis?

Ouroboros Genesis solves the problem of dynamic availability of block-producing nodes by introducing the ‘densest chain’ preference in nodes’ selection of their preferred chain. The original Genesis protocol measures density in terms of the number of blocks. When Genesis and Peras are combined, density is measured in terms of the weight of blocks. In Peras, the weight of a chain is its number of blocks plus the boost parameter B times the number of blocks certified in Peras voting rounds. Genesis’s density concept is fully compatible with Peras’s weight concept.
Instead of adding a voting layer with Peras, why not just switch to using a traditional voting-based BFT protocol?
Peras retains the Praos protocol structure along with the security, scaling, decentralization, and dynamism advantages of the Ouroboros family of Nakamoto protocols while improving their settlement times. Additionally, Peras has self-healing properties, which BFT protocols do not.

## Why aren’t all Peras votes and certificates stored in blocks?

It is not necessary to store all votes and certificates in blocks for the protocol's security. Doing so would therefore unnecessarily utilize a large fraction of a block’s size budget, reducing the number of transactions that can be stored in blocks and lowering overall throughput.

## How long do Peras votes have to be stored off-chain?

Peras votes only need to be retained until they either expire (which is determined by a Peras protocol parameter) or are incorporated into a Peras certificate (since a certificate simply aggregates a quorum of votes). Nodes can store votes in transient memory and provide them to newly syncing nodes as they replace the recent history of blocks.

## How long do Peras certificates have to be stored off-chain?

Peras nodes must forever persist certificates to disk so they can be provided to newly syncing nodes as they replay block history.

## Who came up with Peras?

Input | Output’s research team created Peras.

## How will Peras affect the user experience of interacting with DApps?

Peras primarily focuses on improving transaction settlement time, which means faster confirmation times for users. This will lead to a more responsive and efficient experience when interacting with DApps that incorporate settlement time constraints in the user interface.

## How will Peras affect the user experience of interacting with centralized exchanges?

When depositing ada to a centralized exchange (CEX), it is common for CEXes to wait for 15 to 30 confirmations. Since Peras brings faster transaction finality and significantly reduces the risk of rollback, there is a real possibility that CEXes could lower the number of confirmations it takes before the user can use their ada.

## Can Peras help reduce network congestion during peak usage periods?

No, Peras does not increase the number of transactions that can fit in a block. Ouroboros Leios will reduce congestion by increasing throughput.

## Will Peras introduce any new considerations for smart contract development and deployment on Cardano?

Peras does not affect how smart contracts execute on Cardano, but faster settlement might enable new use cases for smart contracts.

## How often do we expect to revert back to Praos?

Peras will only revert to Praos if a quorum of voting committee members do not cast votes for the same block in a given round. There are three situations where this could happen:

* members of the voting committee are offline or choose not to vote,
* sufficient votes do not diffuse to the block-producing nodes, or
* block-producing nodes disagree about which block is being voted for.

The Peras protocol parameters can be set to ensure that there is plenty of time for votes to diffuse to all  block-producing nodes, which addresses point 2 above. Other parameters ensure that the block being voted for is in the distant enough past that it is on the preferred chain of all block producers with high probability, which partially addresses point 3. Case #3 can also occur during an attack where adversarial block-producing nodes possess nearly a quarter of the stake or more. Case #1 could occur during a massive infrastructure disruption where many block-producing nodes are offline. Therefore, assuming the probability of global-scale network disruptions and large stake attacks is extremely low, well chosen protocol parameters will ensure cooldown periods are very unlikely to occur.

## How does Peras achieve fast finality on top of Nakamoto consensus that is known to have slow finality?

Peras modifies the chain selection of the underlying Nakamoto approach by having a committee of the block-producing nodes add weight to blocks on their dominant chain at a fixed interval. This augments the sequential Nakamoto process, where block producers take turns minting blocks, with a parallel process where block producers collectively certify blocks. That additional attestation process speeds settlement up.

## Is Peras a layer 2?

No, Ouroboros Peras is a layer 1 protocol, just like Ouroboros Praos or Genesis. Peras’ fast settlement may, however, benefit some layer 2 use cases.

## Which other CIPs will need PRs when Peras is adopted?

The CIPs for protocol parameters and for the disaster recovery plan will need revision when Peras is adopted.

## Will relay nodes need to track boosted blocks?

Yes, both block producers and relay nodes will need to track boosted blocks because they need to agree on the weight of the chain. If relay nodes did not include boosts in their chain selection, then they could experience periods of time when they were not following the weightiest chain.

## What is the lightest way for clients to know whether a block has a Peras boost?

Services such as BlockFrost likely will provide information on the number of Peras boosts that follow a given transaction.
