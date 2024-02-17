{ repoRoot, inputs, pkgs, lib, system }:

let
  agdaPackages = repoRoot.nix.agda-packages;
in
pkgs.stdenv.mkDerivation {
  version = "1.0";
  pname = "peras";
  src = ./..;
  meta = {
    description = "Agda library for Peras.";
  };
  buildInputs = [
    repoRoot.nix.agda-with-stdlib
    repoRoot.nix.agda-stdlib
    repoRoot.nix.agda2hs
    pkgs.gnumake
  ];
  buildPhase = ''
    echo "${repoRoot.nix.agda-stdlib}/standard-library.agda-lib" > libraries
    echo "${repoRoot.nix.agda2hs}/agda2hs.agda-lib" >> libraries
    export AGDA_LIBS="--local-interfaces --library-file=$PWD/libraries"
    make
  '';
  installPhase = ''
    mkdir "$out"
    cp -pr peras.agda-lib src "$out"
  '';
}
