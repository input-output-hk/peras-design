{ repoRoot, inputs, pkgs, lib, system }:

let
  peras_topology = inputs.nixos-unstable.legacyPackages.rustPlatform.buildRustPackage rec {
    pname = "peras_topology";
    version = "0.1.0";
    src = ../peras_topology;
    cargoSha256 = "1vxaa60bhknad2f7zmjys73nwfx0fyd9xpydglk9yxjgn27dcfwn";
    meta = with pkgs.stdenv.lib; {
      description = "A topology library for Peras";
    };
  };
  peras_rust = inputs.nixos-unstable.legacyPackages.rustPlatform.buildRustPackage rec {
    pname = "peras_rust";
    version = "0.1.0";
    src = ../peras-rust;
    cargoSha256 = "0lq9jdfqznwilx0mrq43701wzqsfqinjc1v8qas8ph2135pp42dj";
    doCheck = false; # FIXME: Turn on the unit tests as soon as they start passing.
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
