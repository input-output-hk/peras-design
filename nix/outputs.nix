{ repoRoot, inputs, pkgs, lib, system }:

let
  project = repoRoot.nix.project;
  peras-agda = repoRoot.nix.peras-agda;
  test-demo-agda = repoRoot.nix.test-demo;
  rust = repoRoot.nix.rust;
in
[
  (project.flake)
  {
    inherit repoRoot;
    packages.peras = peras-agda;
    packages.test-demo-agda = test-demo-agda;
    devShells.profiled = project.variants.profiled.devShell;
  }
]
