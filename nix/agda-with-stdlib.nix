{ repoRoot, ... }:

let
  stdlib = repoRoot.nix.agda-stdlib;
  agda2hs = repoRoot.nix.agda2hs.lib;
in repoRoot.nix.agda-packages.agda.withPackages [ stdlib agda2hs ]
