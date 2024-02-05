{ repoRoot, inputs, pkgs, system, lib }:
let
  project = repoRoot.nix.project;
  containers = repoRoot.nix.containers;
in
[
  # Default packages, apps, devShells, checks, hydraJobs coming from the Haskell project
  (project.flake)
  { }
  { inherit containers; }
]
