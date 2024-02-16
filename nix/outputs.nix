{ repoRoot, inputs, pkgs, lib, system }:

let
  project = repoRoot.nix.project;
  peras-agda = repoRoot.nix.peras-agda;
  peras-topology = inputs.nixos-unstable.legacyPackages.rustPlatform.buildRustPackage rec {
    pname = "peras_topology";
    version = "11.0.2";
    src = ../peras_topology;
    cargoSha256 = "1s3c6lxwicjx7mdm6jrxihcpilfghp81xzqgs7f0vpky1d7xhy71";
    meta = with pkgs.stdenv.lib; {
      description = "A topology library for Peras";
    };
  };
in
[
  (
    project.flake
  )
  {
    inherit repoRoot;
    packages.peras = peras-agda;
    packages.peras_topology = peras-topology;
    devShells.profiled = project.variants.profiled.devShell;
  }
]
