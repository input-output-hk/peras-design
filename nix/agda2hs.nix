{ repoRoot, inputs, pkgs, lib, system }:

let

  project = pkgs.haskell-nix.hackage-project {
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

in

project.hsPkgs.agda2hs.components.exes.agda2hs 
