# "Split-Brain" Experiment

This first "split-brain" experiment with `peras-iosim` involves running a network of 100 nodes with fivefold connectivity for 15 minutes, but where nodes are partitioned into two non-communicating sets between the 5th and 10th minute. The nodes quickly establish consensus after genesis, but split into two long-lived forks after the 5th minute; shortly after the 10th minute, one of the forks is abandoned as consensus is reestablished.


## Partitioning the network

Nodes are divided into two "parities" determined by whether the hash of their name is an even or odd number. When the network is partitioned, only nodes of the same parity are allowed to communicate with each other: see [`Peras.IOSIM.Experiment.splitBrain`](../../src/Peras/IOSim/Experiment.hs).


## Setup

We consider both the Praos and Peras protocols:

- [protocol-praos.yaml](protocol-praos.yaml)
- [protocol-peras.yaml](protocol-peras.yaml)

We use the following Peras parameters to create a scenario that exhibits occasional cool-down periods and a strong influence of the voting boost:

```yaml
activeSlotCoefficient: 0.10
roundDuration: 50
pCommitteeLottery: 0.00021
votingBoost: 0.25
votingWindow: [150, 1]
votingQuorum: 7
voteMaximumAge: 100
cooldownDuration: 4
prefixCutoffWeight:  10000000
```

The control ("normal") case is a network that does not experience partitioning: [network-normal.yaml](network-normal.yaml).

```yaml
randomSeed: 13234
peerCount: 100
downstreamCount: 5
maximumStake: 1000
messageDelay: 350000
endSlot: 1500
experiment:
  tag: NoExperiment
```

The treatment ("split") case experiences partitioning between the 5th and 10th minutes: [network-split.yaml](network-split.yaml).

```yaml
randomSeed: 13234
peerCount: 100
downstreamCount: 5
maximumStake: 1000
messageDelay: 350000
endSlot: 1500
experiment:
  tag: SplitBrain
  experimentStart: 500
  experimentFinish: 1000
```


## Execution

Run the experiment in a Nix shell with the [experiment.sh](experimeht.sh) script:

```console
$ nix develop

$ ./experiment.sh

-----
Protocol: praos
Network: split
-rw-rw-r-- 1 bbush bbush-upg  22K Mar  9 09:53 chain-praos-split.dot
-rw-rw-r-- 1 bbush bbush-upg 452K Mar  9 09:53 chain-praos-split.png
-rw-rw-r-- 1 bbush bbush-upg 171K Mar  9 09:53 chain-praos-split.svg
-rw-rw-r-- 1 bbush bbush-upg 7.6M Mar  9 09:53 result-praos-split.json
-----
Protocol: praos
Network: normal
-rw-rw-r-- 1 bbush bbush-upg  22K Mar  9 09:53 chain-praos-normal.dot
-rw-rw-r-- 1 bbush bbush-upg 398K Mar  9 09:53 chain-praos-normal.png
-rw-rw-r-- 1 bbush bbush-upg 170K Mar  9 09:53 chain-praos-normal.svg
-rw-rw-r-- 1 bbush bbush-upg 8.5M Mar  9 09:53 result-praos-normal.json
-----
Protocol: peras
Network: split
-rw-rw-r-- 1 bbush bbush-upg  32K Mar  9 09:56 chain-peras-split.dot
-rw-rw-r-- 1 bbush bbush-upg 1.5M Mar  9 09:56 chain-peras-split.png
-rw-rw-r-- 1 bbush bbush-upg 218K Mar  9 09:56 chain-peras-split.svg
-rw-rw-r-- 1 bbush bbush-upg  15M Mar  9 09:56 result-peras-split.json
-----
Protocol: peras
Network: normal
-rw-rw-r-- 1 bbush bbush-upg  36K Mar  9 09:59 chain-peras-normal.dot
-rw-rw-r-- 1 bbush bbush-upg 1.1M Mar  9 09:59 chain-peras-normal.png
-rw-rw-r-- 1 bbush bbush-upg 236K Mar  9 09:59 chain-peras-normal.svg
-rw-rw-r-- 1 bbush bbush-upg  22M Mar  9 09:59 result-peras-normal.json
```

The `result-*.json` files contain the final states of the simulations and the `chain-*.{dot,png,svg}` files visualize the resulting block tree. Here are archived results:

|                                 | Normal Praos | Split Praos | Normal Peras | Split Peras |
|---------------------------------|--------------|-------------|--------------|-------------|
| Results                         | [result-praos-normal.json](https://ipfs.io/ipfs/QmdbfyV2d6iDSqqp7GrbQiNTrUZiwRE6E676PN94n9wxoQ) | [result-praos-split.json](https://ipfs.io/ipfs/QmZ2YJT3bFB3Jsc2Pa8ABaaEum5vPR35crLTnuhznZsA4m) | [result-peras-normal.json](https://ipfs.io/ipfs/QmZwQ83UvnnvGrRxsoVKUSuBDDJEXZoSzyqhWwFBisVEyg) |
[result-peras-split.json](https://ipfs.io/ipfs/QmVxYWVHCKhrSvu5rrZMTmC4SdsMRzZ5hce32Bmk2mNpyq) |
| Graphviz file                   | [chain-praos-normal.dot](https://ipfs.io/ipfs/QmQFMsPP8H5Ab8jtBiANYUXeacf8wt4UC8o1zhc2RZJ9Ky) | [chain-praos-split.dot](https://ipfs.io/ipfs/QmZEwYXsjhUznS2TYHwxGzgyBkDSiJnYJPr7TNAfjYdsWa) | [chain-peras-normal.dot](https://ipfs.io/ipfs/Qmbdu7xiQ9kJHbheQCxZXE9zVmBMLCuCCtjsLnfht2RQXi) |
[chain-peras-split.dot](https://ipfs.io/ipfs/Qmf2qVfcD5ug6TF5HdNPAFpDnZkosRcZ3SKrnsywV1Jtxi) |
| PNG file (low resolution)       | [chain-praos-normal.png](https://ipfs.io/ipfs/QmT2t4UGcrUrTBSjNCC9MMqtwH1scoE5SCe6Wvd6PF16FT) | [chain-praos-split.png](https://ipfs.io/ipfs/QmcfhBuPV2pht2Yfm9dwYqcqdrS3dh6fWVaZ6MbYxDYuyL) | [chain-peras-normal.png](https://ipfs.io/ipfs/QmNds5SBK8QiYd1PiRCmFT5PK5HMxgeuiLXiL4nMbSr8Wb) |
[chain-peras-split.png](https://ipfs.io/ipfs/QmZcTfENLsmFKbwfir8HN1SmzsyjoBVQSQg3eiUwKYdgMx) |
| SVG file (high high resolution) | [chain-praos-normal.svg](https://ipfs.io/ipfs/QmefJ5zBw4cPMK75NC9pFQYkzSWbhN1vTFpqQuuKpGFm54) | [chain-praos-split.svg](https://ipfs.io/ipfs/QmQeVPQgiBdeEzHpr18dQTeo9ovZmSSsug4BetsnAuUoHR) | [chain-peras-normal.svg](https://ipfs.io/ipfs/QmRxG2VvrjNpv1t55Su2sbbvuuR6SkhibLLUhaLEubUV8L) | [chain-peras-split.svg](https://ipfs.io/ipfs/QmYkET8rbRZwhNg5bUWvrkyhu9QFwc3yrsW1Fkrtbcrz14) |


## Results

| Protocol | Metric                                              | Blocks | Slots |
|----------|-----------------------------------------------------|-------:|------:|
| Praos    | Length of discarded chain at slot 1000              |     68 |  1000 |
|          | Length of dominant chain at slot 1000               |     73 |  1000 |
|          | Number of blocks in discarded chain after slot 1000 |      2 |       |
| Peras    | Length of discarded chain at slot 1000              |     75 |  1000 |
|          | Length of dominant chain at slot 1000               |     66 |  1000 |
|          | Number of blocks in discarded chain after slot 1000 |      3 |   137 |
|          |                                                     |      1 |   118 |
|          |                                                     |      1 |   137 |
|          |                                                     |      1 |   141 |
|          |                                                     |      1 |    55 |
|          |                                                     |      1 |    24 |
|          |                                                     |      1 |    18 |
|          | Number of blocks afters slot 1000 to reach quorum   |     18 |   304 |

In the Peras simulation, the chain that eventually became dominant forged fewer blocks during the partition period, but it was lucky to include sufficient votes for a quorum at slot 503 and that kept the chain out of the cool-down period long enough to put more votes on the chain, which increased the chain weight. It appears that that was sufficient for the chain to eventually dominate.

![Forking and reestablishment of quorum in Peras split-brain experiment](https://ipfs.io/ipfs/QmXmYdLpVa65zNfrHf15wEQ6SjSALwiRFoaX1NvvcAkYvy)


## Findings

1. The complexity of the forking, voting, and cool-down in the Peras results highlights the need for capable visualization and analysis tools.
2. The voting boost can impede the reestablishment of consensus after a network partition is restored.
3. It would be convenient to be able to start a simulation from an existing chain, instead of from genesis.
4. VRF-based randomization make it easier to compare simulations with different parameters. 
5. Even though `peras-iosim` runs aren't particularly fast, we probably don't need to parallelize them because typical experiments involve many executions of simulations, which means we can take advantage of CPU resources simply by running those different scenarios in parallel.
6. The memory footprint of `peras-iosim` is small (less than 100 MB) if tracing is turned off; with tracing, it is about twenty times that, but still modest.
