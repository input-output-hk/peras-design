# Model and Simulations for Ouroboros Peras

<div align="center">
  <a href="https://github.com/input-output-hk/peras-design/actions/workflows/ci.yaml"><img src="https://github.com/input-output-hk/peras-design/actions/workflows/ci.yaml/badge.svg" /></a>
</div>

This repository contains the various artifacts (code, diagrams, documentation, website, journal...) from the Peras R&D project.

## Documentation

* The [website](https://peras.cardano-scaling.org) provides all relevant documentation, most notably the technical reports published by the project, updates, and links to simulator,
* The [Logbook](Logbook.md) contains a detailed account of problems,
  successes, failures, ideas, references and is intended as a tool to
  help the team members stay in sync

## Hacking

> [!IMPORTANT]
>
> As of 2024-11-01, this repository has entered maintenance mode as the project as left the R&D stage and moved under the umbrella of [Intersect MBO]() towards implementation.
> Checkout [CIP](https://github.com/cardano-foundation/CIPs/pull/872) for relevant discussions on the road towards implementing Peras in Cardano.

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

### Haskell

Use `nix develop` to enter a development shell that contains all of the required Haskell package dependencies. In that shell, `cabal build all` will build the haskell packages.

Alternatively, one can build the packages directly via Nix:
- `nix build .#peras-hs`
- `nix build .#peras-iosim`
- `nix build .#peras-quickcheck`

#### Profiling

Furthermore, use `nix develop .#profiled` for a shell with profiled versions of all of the packages. One can place a file `cabal.project.local`, with the contents below, in the root folder of this repository and then build profiled code with `cabal build`.

```cabal
library-profiling: True
profiling: True
package *
  ghc-options: -O2 -threaded -fprof-auto -fprof-cafs "-with-rtsopts=-N -p -s -hc -i0.1 -ls"
```
