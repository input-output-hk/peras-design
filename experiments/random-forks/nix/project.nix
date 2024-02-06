{ repoRoot, inputs, pkgs, lib, system }:

let

  cabalProject = pkgs.haskell-nix.cabalProject' ({ config, pkgs, ... }: {
    name = "random-forks";
    src = ../.;
    compiler-nix-name = "ghc928";
    shell.withHoogle = false;
    inputMap = {
      "https://input-output-hk.github.io/cardano-haskell-packages" = inputs.iogx.inputs.CHaP;
    };
    modules = [{
      packages = {
        random-forks.ghcOptions = [ "-Werror" ];
      };
    }];
  });

  project = lib.iogx.mkHaskellProject {
    inherit cabalProject;
    shellArgs = repoRoot.nix.shell;
  };

in

project
