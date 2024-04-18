{ repoRoot, pkgs, lib, ... }:

cabalProject:

{
  name = "peras-design";

  packages = with pkgs; [

    # Haskell dependencies.
    pkgs.cairo

    # Agda packages.
    repoRoot.nix.agda-with-stdlib
    repoRoot.nix.agda-stdlib
    repoRoot.nix.agda2hs.lib
    repoRoot.nix.agda2hs.exe
    repoRoot.nix.emacs-with-packages

    # Rust packages.
    clang
    llvmPackages.bintools
    rust-bin.stable.latest.default

    # Additional Haskell tools.
    haskellPackages.pointfree
    # haskellPackages.pointful

    # Additional tools
    gnumake # For make-based Agda builds.
    gnused # For Rust shell hook.
    graphviz # For plotting network topology and chain forking.
    haskellPackages.threadscope # For visualizing profiles.
    ghostscript_headless # For visualizing profiles.
    plantuml # For UML diagrams.
    pandoc # For generating PDF from markdown.
    librsvg # SVG conversion in pandoc.
    mononoki # Font for Agda.

  ];

  # Agda environment variables.
  env.AGDA_STDLIB = "${repoRoot.nix.agda-stdlib}/standard-library.agda-lib";
  env.AGDA2HS_LIB = "${repoRoot.nix.agda2hs.lib}/agda2hs.agda-lib";

  # Rust environment variables: https://github.com/rust-lang/rust-bindgen#environment-variables
  env.LIBCLANG_PATH =
    pkgs.lib.makeLibraryPath [ pkgs.llvmPackages_latest.libclang.lib ];
  env.RUSTFLAGS = builtins.concatStringsSep " " (builtins.map (a: "-L ${a}/lib")
    [
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
      ''
        -I"${pkgs.llvmPackages_latest.libclang.lib}/lib/clang/${pkgs.llvmPackages_latest.libclang.version}/include"''
      ''-I"${pkgs.glib.dev}/include/glib-2.0"''
      "-I${pkgs.glib.out}/lib/glib-2.0/include/"
    ]
  );

  shellHook = ''
    # Agda hook.
    echo "${repoRoot.nix.agda-stdlib}/standard-library.agda-lib" > .libraries
    echo "${repoRoot.nix.agda2hs.lib}/agda2hs.agda-lib" >> .libraries
    export AGDA_LIBS="$PWD/.libraries"
    echo "NOTE: 'make' will use the libraries file '$AGDA_LIBS' unless 'AGDA_LIBS' is set differently."
    # Rust hook.
    export RUSTC_VERSION="$(rustup toolchain list | sed -n -e '/ (default)$/{s/ (default)$//;p}')"
    export PATH="''${CARGO_HOME:-~/.cargo}/bin:$PATH"
    export PATH="''${RUSTUP_HOME:-~/.rustup}/toolchains/$RUSTC_VERSION/bin/:$PATH"
    export LD_LIBRARY_PATH="$PWD/peras-rust/target/debug:$LD_LIBRARY_PATH"
    if [ ! -f rust-toolchain ]
    then
      echo "$RUSTC_VERSION" > rust-toolchain
    fi
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
    # cabal-fmt.extraOptions = "";
    fourmolu.enable = true;
    # fourmolu.extraOptions = "";
    hlint.enable = false;
    # hlint.extraOptions = "";
    # shellcheck.enable = false;
    # shellcheck.extraOptions = "";
    # editorconfig-checker.enable = false;
    # editorconfig-checker.extraOptions = "";
    nixpkgs-fmt.enable = true;
    # nixpkgs-fmt.extraOptions = "";
    # optipng.enable = false;
    # optipng.extraOptions = "";
  };
}

