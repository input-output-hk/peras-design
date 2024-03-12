{ repoRoot, inputs, pkgs, lib, system }:

let
  peras_topology = inputs.nixos-unstable.legacyPackages.rustPlatform.buildRustPackage rec {
    pname = "peras_topology";
    version = "0.1.0";
    src = ../peras_topology;
    cargoSha256 = "1vxaa60bhknad2f7zmjys73nwfx0fyd9xpydglk9yxjgn27dcfwn";
    doCheck = false; # FIXME: Turn on the unit tests as soon as they start passing.
    meta = with pkgs.stdenv.lib; {
      description = "A topology library for Peras";
    };
  };
  peras_topology_src = ../peras_topology;
  peras_rust = inputs.nixos-unstable.legacyPackages.rustPlatform.buildRustPackage rec {
    pname = "peras_rust";
    version = "0.1.0";
    src = ../peras-rust;
    cargoSha256 = "";
    cargoLock = {
      lockFile = ../peras-rust/Cargo.lock;
      outputHashes = {
        "netsim-0.1.0" = "sha256-lx+lLOp85XUUOxyN6AetjnG4v+bgQVjMY0iZHMEDPeY=";
      };
    };
    buildInputs = [ peras_topology ];
    doCheck = false; # FIXME: Turn on the unit tests as soon as they start passing.
    preConfigure = ''
      sed -i "s@../peras_topology@${peras_topology_src}@" Cargo.toml
    '';
    preInstall = ''
      mkdir -p "$out/include"
      cp "$src/peras.h" "$out/include/"
    '';
    meta = with pkgs.stdenv.lib; {
      description = "A rust library for Peras";
    };
  };
in
{
  peras_topology = peras_topology;
  peras_rust = peras_rust;
}
