# Model and Simulations for Ouroboros Peras

![](https://github.com/github/input-output-hk/peras-design/actions/workflows/ci.yaml/badge.svg)

This repository is intended to host more or less formal specifications, experiments, models for the Ouroboros Peras protocol.

## Hacking

### Agda

Please check instructions for [Installing Agda](https://agda.readthedocs.io/en/latest/getting-started/installation.html) on the official website.

### Checking

To typecheck all `.agda` source files:

```
make
Checking Peras.Block (./src/Peras/Block.agda).
Checking Peras.Chain (./src/Peras/Chain.agda).
Checking Peras.Nakamoto (./src/Peras/Nakamoto.agda)
```

To remove all `.agdai` files produced:

```
make clean
```
