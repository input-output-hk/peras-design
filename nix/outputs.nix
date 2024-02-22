{ repoRoot, inputs, pkgs, lib, system }:

let
  project = repoRoot.nix.project;
  peras-agda = repoRoot.nix.peras-agda;
  rust = repoRoot.nix.rust;
in
[
  (
    project.flake
  )
  {
    inherit repoRoot;
    packages.peras = peras-agda;
    packages.peras_topology = rust.peras_topology;
    packages.peras_rust = rust.peras_rust;
    devShells.profiled = project.variants.profiled.devShell;
  }
]
