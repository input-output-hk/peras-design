{ inputs, pkgs, ... }:

let
  toolchain = pkgs.rust-bin.stable.latest.default;
  craneLib = (inputs.crane.mkLib pkgs).overrideToolchain toolchain;
in rec {
  peras_topology = craneLib.buildPackage { src = ../peras_topology; };
  peras_rust = craneLib.buildPackage {
    src = ../peras-rust;
    buildInputs = [ peras_topology ];
    preConfigure = ''
      # Replace a relative path by its /nix/store equivalent
      sed -i "s@../peras_topology@${../peras_topology}@" Cargo.toml
    '';
    preInstall = ''
      mkdir -p "$out/include"
      cp "$src/peras.h" "$out/include/"
    '';
  };
}
