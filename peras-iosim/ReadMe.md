# An `IOSim`-based simulation of the Peras protocol

This is a work in progress. 


## Usage

```console
$ cabal run exe:peras-iosim -- --help

Usage: peras-iosim [--version] --parameter-file FILE --protocol-file FILE 
                   [--trace-file FILE] [--result-file FILE] 
                   [--network-dot-file FILE] [--network-png-file FILE] 
                   [--chain-dot-file FILE] [--chain-png-file FILE]

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
  --chain-dot-file FILE    Path to output GraphViz .dot file of chain
                           visualizaton.
  --chain-png-file FILE    Path to output PNG file of chain visualizaton.
                           Requires `GraphViz` executable.
```


## Example

Use the parameters [small-network.yaml](small-network.yaml) and the pseudo-Praos protocol [pseudo-praos.yaml](pseudo-praos.yaml).

```console
$ cat small-network.yaml 
randomSeed: 12345
peerCount: 10
downstreamCount: 3
maximumStake: 1000
endSlot: 1000

$ cat pseudo-praos.yaml 
protocol: PseudoPraos
activeSlotCoefficient: 0.05
```

(Note that a one-node example is available in the configuration [one-node.yaml](one-node.yaml).)

Run the simulation. Beware of poor performance and high memory usage: consider running with `ulimit -m`.

```bash
cabal run exe:peras-iosim -- \
  --parameter-file small-network.yaml \
  --protocol-file pseudo-praos.yaml \
  --result-file result.json \
  --network-png-file peers.png \
  --chain-png-file chains.png
```

View the results [results.json](https://ipfs.io/ipfs/QmZKSas1LCx8gT7dZTESxjQqfJYpkb1FFhDZMnEBjmzWcd):

```console
$ json2yaml result.json | head -n 20

activeNodes: []
exitStates:
  N1:
    clock: '1970-01-01T00:16:40Z'
    committeeMember: false
    downstreams:
    - N10
    - N2
    - N6
    nodeId: N1
    owner: cc984eae6e3c
    preferredChain:
      previous:
        previous:
          previous:
            previous:
              previous:
                previous:
                  previous:
                    previous:
```

The network topology is plotted as [peers.png](https://ipfs.io/ipfs/QmdZfFwVqEQZmEcwvufccDFfzsoSVCw4xYDnD685nPdPmu) and the chains are plotted as [chains.png](https://ipfs.io/ipfs/Qmc9cCAh2KfNtPWHMexavT8K2QktPRDiMaoxWkxKEJW7un).

| Network Topology                                                                  | Chains                                                                             |
|-----------------------------------------------------------------------------------|------------------------------------------------------------------------------------|
| ![peers.png](https://ipfs.io/ipfs/QmdZfFwVqEQZmEcwvufccDFfzsoSVCw4xYDnD685nPdPmu) | ![chains.png](https://ipfs.io/ipfs/Qmc9cCAh2KfNtPWHMexavT8K2QktPRDiMaoxWkxKEJW7un) |
