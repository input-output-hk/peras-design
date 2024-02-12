{ repoRoot, inputs, pkgs, lib, system }:

cabalProject:

{
  name = "peras-design";

  packages = [
    repoRoot.nix.agda-with-stdlib
    repoRoot.nix.agda-stdlib
    repoRoot.nix.agda2hs
    repoRoot.nix.emacs-with-packages
    pkgs.haskellPackages.pointfree
    # pkgs.haskellPackages.pointful
    pkgs.gnumake
    pkgs.graphviz # For plotting network topology and chain forking.
    pkgs.haskellPackages.threadscope # For visualizing profiles.
    pkgs.ghostscript_headless # For visualizing profiles.
  ];

  env.AGDA_STDLIB = "${repoRoot.nix.agda-stdlib}/standard-library.agda-lib";

  shellHook = ''
    echo "${repoRoot.nix.agda-stdlib}/standard-library.agda-lib" > .libraries
    export AGDA_LIBS="--local-interfaces --library-file=$PWD/.libraries"
  '';

  tools = {
    # haskellCompilerVersion = cabalProject.args.compiler-nix-name;
    # cabal-fmt = null;
    # cabal-install = null;
    # haskell-language-server = null;
    # haskell-language-server-wrapper = null;
    # fourmolu = null;
    # hlint = null;
    # stylish-haskell = null;
    # ghcid = null;
    # shellcheck = null;
    # prettier = null;
    # editorconfig-checker = null;
    # nixpkgs-fmt = null;
    # optipng = null;
    # purs-tidy = null;
  };

  preCommit = {
    cabal-fmt.enable = false;
    #   cabal-fmt.extraOptions = "";
    fourmolu.enable = true;
    #   fourmolu.extraOptions = "";
    hlint.enable = false;
    #   hlint.extraOptions = "";
    #   shellcheck.enable = false;
    #   shellcheck.extraOptions = "";
    #   editorconfig-checker.enable = false;
    #   editorconfig-checker.extraOptions = "";
    nixpkgs-fmt.enable = true;
    #   nixpkgs-fmt.extraOptions = "";
    #   optipng.enable = false;
    #   optipng.extraOptions = "";
  };
}
 
