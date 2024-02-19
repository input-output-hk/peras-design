{ repoRoot, inputs, pkgs, lib, system }:

let

  haskellProject = pkgs.haskell-nix.hackage-project {
    name = "agda2hs";
    version = "1.2";
    compiler-nix-name = "ghc96";
    modules = [{
      packages.agda2hs.components.exes.agda2hs.dontStrip = false;
      # The `agda` and `agda2hs` executables must have the same version in order
      # to avoid recompiling the standard library during other compilations.
      packages.Agda.package.buildType = lib.mkForce "Simple";
      packages.Agda.components.library.enableSeparateDataOutput = lib.mkForce true;
      packages.Agda.components.library.postInstall = repoRoot.nix.agda-project.hsPkgs.Agda.components.library.postInstall;
    }];
  };

  agdaLib = repoRoot.nix.agda-packages.mkDerivation {
    pname = "agda2hs";
    version = "1.2";
    src = inputs.agda2nix;
    meta = {
      description = "agda2hs";
    };
    everythingFile = "./lib/Everything.agda";
    preBuild = ''
      # This won't compile without `--sized-types`.
      sed -i '/^flags:/s/$/ --sized-types/' agda2hs.agda-lib
      # Create the missing everything file.
      find lib -type f -name \*.agda | sed -e 's/^lib\//import /; s/\.agda$// ; s/\//./g' > Everything.agda
      sed -i '1imodule Everything where' Everything.agda
      mv Everything.agda lib/
      # Remove extraneous files.
      rm -rf test tutorials
    '';
  };

  altAgdaLib = repoRoot.nix.agda-packages.mkDerivation {
    pname = "agda2hs";
    version = "1.2";
    src = inputs.agda2nix;
    meta = {
      description = "agda2hs";
    };
    everythingFile = "./lib/Everything.agda";
    preBuild = ''
      # Create the missing everything file.
      find lib -type f -name \*.agda | sed -e 's/^lib\//import /; s/\.agda$// ; s/\//./g' > Everything.agda
      sed -i '1imodule Everything where' Everything.agda
      mv Everything.agda lib/
      # Remove the one file that uses `--sized-types`.
      sed -i '/Haskell\.Prim\.Thunk/d' lib/Everything.agda
      # Remove extraneous files.
      rm -rf test tutorials
    '';
  };

in

{
  exe = haskellProject.hsPkgs.agda2hs.components.exes.agda2hs;
  lib = altAgdaLib;
}
