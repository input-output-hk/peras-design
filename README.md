# Model and Simulations for Ouroboros Peras

<div align="center">
  <a href="https://github.com/input-output-hk/peras-design/actions/workflows/ci.yaml"><img src="https://github.com/input-output-hk/peras-design/actions/workflows/ci.yaml/badge.svg" /></a>
</div>

This repository is intended to host more or less formal specifications, experiments, models for the Ouroboros Peras protocol.

## Documentation

* [Weekly updates](docs/weekly) provide regular "heartbeat" about the
  state of the project and what the team is working on
* [Logbook](Logbook.md) contains a detailed account of problems,
  successes, failures, ideas, references and is intended as a tool to
  help the team members stay in sync

## Hacking

### Agda

#### With nix

The repository provides a nix flake from which one can enter a development shell suitable for Agda using the following command:

```bash
nix develop
make
```

The Peras library for Agda can be built with `nix build .#peras`.

#### Without nix

Please check instructions for [Installing Agda](https://agda.readthedocs.io/en/latest/getting-started/installation.html) on the official website.

Peras code requires agda-stdlib, check out instructions for [installing libraries](https://agda.readthedocs.io/en/latest/tools/package-system.html) and do not forget to:

* Add `standard-library` to your `~/.agda/defaults` file
* Add `<path to>/standard-library.agda-lib` to `~/.agda/libraries` file

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
