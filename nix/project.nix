{ repoRoot, inputs, pkgs, system, lib, ... }:

let

  peras_rust = repoRoot.nix.rust.peras_rust;

  cabalProject' = pkgs.haskell-nix.cabalProject' ({ pkgs, config, ... }: {
    src = ../.;
    shell.withHoogle = false;
    inputMap = {
      "https://input-output-hk.github.io/cardano-haskell-packages" =
        inputs.iogx.inputs.CHaP;
    };
    name = "peras-design";
    compiler-nix-name = lib.mkDefault "ghc96";
    flake.variants.profiled.modules = [{
      enableProfiling = true;
      enableLibraryProfiling = true;
    }];
  });

  cabalProject = cabalProject'.appendOverlays [ ];

  project = lib.iogx.mkHaskellProject {
    inherit cabalProject;
    readTheDocs.enable = false;
    shellArgs = repoRoot.nix.shell;
  };

in
project
