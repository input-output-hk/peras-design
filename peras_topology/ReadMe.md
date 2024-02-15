# Network topology generator

This is a work in progress.

## Example

See [src/main.rs](src/main.rs) for a Rust program that reads a YAML-formatted set of network parameters and outputs a JSON topology for a rrandomly-generated network.

```console
$ cargo run

PARAMETERS: {"randomSeed":12345,"endSlot":100,"peerCount":10,"downstreamCount":3,"totalStake":null,"maximumStake":1000,"messageDelay":0.35}

TOPOLOGY: {"connections":{"N5":["N3","N9","N1"],"N10":["N5","N8","N2"],"N3":["N1","N5","N6"],"N7":["N2","N9","N8"],"N2":["N8","N3","N5"],"N4":["N9","N10","N3"],"N1":["N9","N6","N2"],"N8":["N6","N4","N5"],"N9":["N8","N10","N2"],"N6":["N7","N9","N3"]}}
```
