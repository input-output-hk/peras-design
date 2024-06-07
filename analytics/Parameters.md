# Constraints on Peras Parameters

| Parameter | Symbol | Units | Description | Constraints | Rationale |
| ---- | ---- | ---- | ---- | ---- | ---- |
| Round length | $U$ | slots | The duration of each voting round. | $U \geq \Delta$ | All of a round's votes must be received before the end of the round. |
| Block selection offset | $L$ | slots | The minimum age of a candidate block for being voted upon. | $L \leq U$ | Rule VR-1B will fail if the candidate block is older than the most recently certified block. |
| Chain ignorance period | $R$ | rounds | The number of rounds for which to ignore certificates after entering a cool-down period. | $R = \left\lceil A / U \right\rceil$ | Ensure chain-ignorance period lasts long enough to include a certificate on the chain. |
| Cool-down period | $K$ | rounds | The minimum number of rounds to wait before voting again after a cool-down period starts. | $K = \left\lceil \frac{A + T_\text{CP}}{U} \right\rceil$ | After a quorum failure, the chain must heal, achieve quality, and attain a common prefix. |
| Certificate expiration | $A$ | slots | The maximum age for a certificate to be included in a block. | $A = T_\text{heal}+T_\text{CQ}$ | After a quorum failure, the chain must heal and achieve quality. |
| Certification boost | $B$ | blocks | The extra chain weight that a certificate gives to a block. | $B \gt 0$ | Peras requires that some blocks be boosted. |
| Quorum size | $\tau$ | parties | The number of votes required to create a certificate. | $\tau \gt 3 n / 4$ | Guard against a minority (<50%) of adversarial voters. |
| Committee size | $n$ | parties | The number of members on the voting committee. | $n \gt 0$ | Peras requires a voting committee. |
| Preagreement termination | $T$ | slots | The maximum number of slots needed for preagreement. | $T \lt U$ | Preagreement must complete before the round ends. |
| Network diffusion time | $\Delta$ | slots | Upper limit on the time needed to diffuse a message to all nodes. | $\Delta \gt 0$ | Messages have a finite delay. |
| Active slot coefficient | $\alpha$ | 1/slots | The probability that a party will be the slot leader for a particular slot. | $0 \lt \alpha \leq 1$ | Blocks must be produced. |
| Healing time | $T_\text{heal}$ | slots | Healing period to mitigate strong (25-50%) adversary. | $T_\text{heal} ≟ \mathcal{O}\left( B / \alpha \right)$ | Sufficient blocks must be produced to overcome an adversarially boosted block. |
| Chain-quality time | $T_\text{CQ}$ | slots | Ensure the presence of at least one honest block on the chain. | $T_\text{CQ} ≟ \mathcal{O} \left( \left( \log (1 - \alpha) \right)^{-1} \right)$ | A least one honest block must be produced. |
| Common-prefix time | $T_\text{CP}$ | slots | Achieve settlement. | $T_\text{CP} ≟ \mathcal{O} \left( k / \alpha \right)$ | The Ouroboros Praos security parameter defines the time for having a common prefix. |
| Security parameter | $k$ | blocks | The Ouroboros Praos security parameter. | $k = 2160$ | Value for the Cardano mainnet. |
