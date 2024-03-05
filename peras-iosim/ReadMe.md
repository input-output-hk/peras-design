# An `IOSim`-based simulation of the Peras protocol

This is a work in progress. 


## Usage

```console
$ cabal run exe:peras-iosim -- --help

peras-iosim: simulate Peras protocol

Usage: peras-iosim [--version] --parameter-file FILE --protocol-file FILE 
                   [--trace-file FILE] [--result-file FILE] 
                   [--network-dot-file FILE] [--network-png-file FILE] 
                   [--network-svg-file FILE] [--chain-dot-file FILE] 
                   [--chain-png-file FILE] [--chain-svg-file FILE]

  This command-line tool simulates and visualizes Peras protocol simulations.

Available options:
  -h,--help                Show this help text
  --version                Show version.
  --parameter-file FILE    Path to YAML file with simulation parameters.
  --protocol-file FILE     Path to YAML file with protocol parameters.
  --trace-file FILE        Path to output text file for simulation trace.
  --result-file FILE       Path to output JSON file for simulation results.
  --network-dot-file FILE  Path to output GraphViz .dot file of network
                           visualizaton.
  --network-png-file FILE  Path to output PNG file of network visualizaton.
                           Requires `GraphViz` executable.
  --network-svg-file FILE  Path to output SVG file of network visualizaton.
                           Requires `GraphViz` executable.
  --chain-dot-file FILE    Path to output GraphViz .dot file of chain
                           visualizaton.
  --chain-png-file FILE    Path to output PNG file of chain visualizaton.
                           Requires `GraphViz` executable.
  --chain-svg-file FILE    Path to output SVG file of chain visualizaton.
                           Requires `GraphViz` executable.

```


## Example

Use the parameters [small-network.yaml](small-network.yaml) and the pseudo-Praos protocol [pseudo-peras.yaml](pseudo-peras.yaml).

```console
$ cat small-network.yaml 
randomSeed: 13234
peerCount: 100
downstreamCount: 3
maximumStake: 1000
messageDelay: 0.35
endSlot: 600

$ cat pseudo-peras.yaml 
activeSlotCoefficient: 0.10
roundDuration: 10
pCommitteeLottery: 0.00021
votingBoost: 0.25
votingWindow: [50, 1]
votingQuorum: 10
voteMaximumAge: 30
cooldownDuration: 5
prefixCutoffWeight:  10000000

```

(Note that a one-node example is available in the configuration [one-node.yaml](one-node.yaml).)

Run the simulation. Beware of poor performance and high memory usage: consider running with `ulimit -m`.

```bash
cabal run exe:peras-iosim -- \
  --parameter-file small-network.yaml \
  --protocol-file pseudo-peras.yaml \
  --result-file result.json \
  --network-png-file peers.png \
  --chain-png-file chains.png
```

View the results [results.json](https://ipfs.io/ipfs/QmaUCsn34TQ6yLS8ftEQFdR3TsjMWxhBrYqiD1A2sKTwvi):

```console
$ json2yaml result.json | head -n 20

activeNodes: []
blocksSeen:
  ? ''
  : - creatorId: 9047079929149956632
      includedVotes: []
      leadershipProof: 7c81eec7dfe5
      parentBlock: ''
      payload: []
      signature: 4b2e560116a8
      slotNumber: 22
  06a0c64a048e:
  - creatorId: 4491903650083474994
    includedVotes: []
    leadershipProof: 04665e458c93
    parentBlock: 06a0c64a048e
    payload: []
    signature: e30da02fc918
    slotNumber: 44
  0af73bf44eaf:
  - creatorId: 7915415148195206136
```

The network topology is plotted as [peers.png](https://ipfs.io/ipfs/QmPKWdUejoJRY7fQfyV2vru7ysKy5gddGum8GXB5AjvsMJ) and the chains are plotted as [chains.png](https://ipfs.io/ipfs/QmRLHreSxVuFbQkwz88cmEnjM8q843EoLrxQfkBrncjVb5).

| Network Topology                                                                  | Chains                                                                             |
|-----------------------------------------------------------------------------------|------------------------------------------------------------------------------------|
| ![peers.png](https://ipfs.io/ipfs/QmPKWdUejoJRY7fQfyV2vru7ysKy5gddGum8GXB5AjvsMJ) | ![chains.png](https://ipfs.io/ipfs/QmRLHreSxVuFbQkwz88cmEnjM8q843EoLrxQfkBrncjVb5) |
