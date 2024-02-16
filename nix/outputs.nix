{ repoRoot, inputs, pkgs, lib, system }:

let
  project = repoRoot.nix.project;
  peras-agda = repoRoot.nix.peras-agda;
  peras-topology = pkgs.rustPlatform.buildRustPackage rec {
    pname = "peras_topology";
    version = "11.0.2";
    src = ../peras_topology;
    cargoSha256 = "176jr6r0d7l756vsffm3pq7zw0jxwls6iwg4h3mvz9bg5dhfmmms";
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
