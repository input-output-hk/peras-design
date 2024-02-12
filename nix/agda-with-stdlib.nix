{ repoRoot, inputs, pkgs, system, lib }:

let
  stdlib = repoRoot.nix.agda-stdlib;
in
repoRoot.nix.agda-packages.agda.withPackages [ stdlib ]
