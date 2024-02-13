{ repoRoot, inputs, pkgs, system, lib }:

let

  cabalProject' = pkgs.haskell-nix.cabalProject' ({ pkgs, config, ... }:
    let
      # When `isCross` is `true`, it means that we are cross-compiling the project.
      # WARNING You must use the `pkgs` coming from cabalProject' for `isCross` to work.
      isCross = pkgs.stdenv.hostPlatform != pkgs.stdenv.buildPlatform;
    in
    {
      src = ../.;
      shell.withHoogle = false;
      inputMap = {
        "https://input-output-hk.github.io/cardano-haskell-packages" = inputs.iogx.inputs.CHaP;
      };
      name = "peras-design";
      compiler-nix-name = lib.mkDefault "ghc96";
      modules = [ ];
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
