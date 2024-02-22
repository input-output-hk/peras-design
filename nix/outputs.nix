{ repoRoot, inputs, pkgs, lib, system }:

let
  project = repoRoot.nix.project;
  peras-agda = repoRoot.nix.peras-agda;
  peras_topology = inputs.nixos-unstable.legacyPackages.rustPlatform.buildRustPackage rec {
    pname = "peras_topology";
    version = "0.1.0";
    src = ../peras_topology;
    cargoSha256 = "1vxaa60bhknad2f7zmjys73nwfx0fyd9xpydglk9yxjgn27dcfwn";
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
    packages.peras_topology = peras_topology;
    devShells.profiled = project.variants.profiled.devShell;
  }
]
