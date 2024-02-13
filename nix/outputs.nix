{ repoRoot, inputs, pkgs, lib, system }:

let
  project = repoRoot.nix.project;
  peras-agda = repoRoot.nix.peras-agda;
in
[
  (
    project.flake
  )
  {
    inherit repoRoot;
    packages.peras = peras-agda;
    devShells.profiled = project.variants.profiled.devShell;
    z = project.flake;
  }
]
