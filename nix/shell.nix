{ repoRoot, inputs, pkgs, lib, system }:

cabalProject:

{
  name = "peras-design";

  packages = [

    # Agda packages.
    repoRoot.nix.agda-with-stdlib
    repoRoot.nix.agda-stdlib
    repoRoot.nix.agda2hs.lib
    repoRoot.nix.agda2hs.exe
    repoRoot.nix.emacs-with-packages

    # Rust packages.
    pkgs.clang
    pkgs.llvmPackages.bintools
    pkgs.rustup

    # Additional Haskell tools.
    pkgs.haskellPackages.pointfree
    # pkgs.haskellPackages.pointful

    # Additional tools
    pkgs.gnumake # For make-based Agda builds.
    pkgs.gnused # For Rust shell hook.
    pkgs.graphviz # For plotting network topology and chain forking.
    pkgs.haskellPackages.threadscope # For visualizing profiles.
    pkgs.ghostscript_headless # For visualizing profiles.

  ];

  # Agda environment variables.
  env.AGDA_STDLIB = "${repoRoot.nix.agda-stdlib}/standard-library.agda-lib";
  env.AGDA2HS_LIB = "${repoRoot.nix.agda2hs.lib}/agda2hs.agda-lib";

  # Rust environment variables: https://github.com/rust-lang/rust-bindgen#environment-variables
  env.LIBCLANG_PATH = pkgs.lib.makeLibraryPath [ pkgs.llvmPackages_latest.libclang.lib ];
  env.RUSTFLAGS = builtins.concatStringsSep " " (builtins.map (a: ''-L ${a}/lib'') [
    # add libraries here (e.g. pkgs.libvmi)
  ]);
  env.BINDGEN_EXTRA_CLANG_ARGS = builtins.concatStringsSep " " (
    # Includes with normal include path
    (builtins.map (a: ''-I"${a}/include"'') [
      # add dev libraries here (e.g. pkgs.libvmi.dev)
      pkgs.glibc.dev
    ])
    # Includes with special directory paths
    ++ [
      ''-I"${pkgs.llvmPackages_latest.libclang.lib}/lib/clang/${pkgs.llvmPackages_latest.libclang.version}/include"''
      ''-I"${pkgs.glib.dev}/include/glib-2.0"''
      ''-I${pkgs.glib.out}/lib/glib-2.0/include/''
    ]
  );

  shellHook = ''
    # Agda hook.
    echo "${repoRoot.nix.agda-stdlib}/standard-library.agda-lib" > .libraries
    echo "${repoRoot.nix.agda2hs.lib}/agda2hs.agda-lib" >> .libraries
    export AGDA_LIBS="--local-interfaces --library-file=$PWD/.libraries"
    # Rust hook.
    export RUSTC_VERSION=$(rustup toolchain list | sed -n -e '/ (default)$/{s/ (default)$//;p}')
    export PATH=''${CARGO_HOME:-~/.cargo}/bin:$PATH
    export PATH=''${RUSTUP_HOME:-~/.rustup}/toolchains/$RUSTC_VERSION/bin/:$PATH
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
 
