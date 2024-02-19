{ repoRoot, inputs, pkgs, lib, system }:

let
  agdaPackages = repoRoot.nix.agda-packages;
in
repoRoot.nix.agda-packages.mkDerivation {
  version = "1.0";
  pname = "peras";
  src = ./..;
  meta = {
    description = "Agda library for Peras.";
  };
  buildInputs = [
    repoRoot.nix.agda-stdlib
    repoRoot.nix.agda2hs.lib
  ];
  everythingFile = "./src/Everything.agda";
  preBuild = ''
    # Create the missing everything file.
    find src -type f -name \*.agda | sed -e 's/^src\//import /; s/\.agda$// ; s/\//./g' > Everything.agda
    sed -i '1imodule Everything where' Everything.agda
    mv Everything.agda src/
  '';
}
