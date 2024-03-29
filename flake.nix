{
  description = "peras-design";

  inputs = {
    iogx = {
      url = "github:input-output-hk/iogx";
      inputs.hackage.follows = "hackage";
    };
    hackage = {
      url = "github:input-output-hk/hackage.nix";
      flake = false;
    };
    agda2nix = {
      url = "github:agda/agda2hs/b269164e15da03b74cf43b51c522f4f052b4af80";
      flake = false;
    };
    crane.url = "github:ipetkov/crane";
    crane.inputs.nixpkgs.follows = "nixpkgs";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs = inputs:
    inputs.iogx.lib.mkFlake rec {
      inherit inputs;
      nixpkgsArgs.overlays = [ (import inputs.rust-overlay) ];
      repoRoot = ./.;
      outputs = import ./nix/outputs.nix;
      systems = [ "x86_64-linux" "x86_64-darwin" "aarch64-darwin" ];
      # debug = false;
    };

  # This flake is currently failing on aarch64-darwin with:
  #
  # error: builder for '/nix/store/f7gai4c7rgsylckm9660rwq8405lf57a-glibc-nolibgcc-2.37-8.drv' failed with exit code 1;
  #        last 10 log lines:
  #        > checking for egrep... /nix/store/cdmbbylvs8hr92b41a6v1ds874z2rmz2-gnugrep-3.11/bin/grep -E
  #        > mips nios2 or1k powerpc riscv s390 sh checking for grep that handles long lines and -e... (cached) /nix/store/cdmbbylvs8hr92b41a6v1ds874z2rmz2-gnugrep-3.11/bin/grep
  #        > checking for egrep... (cached) /nix/store/cdmbbylvs8hr92b41a6v1ds874z2rmz2-gnugrep-3.11/bin/grep -E
  #        > sparc x86_64
  #        > configure: error:
  #        > *** The GNU C library is currently unavailable for this platform.
  #        > *** If you are interested in seeing glibc on this platform visit
  #        > *** the "How to submit a new port" in the wiki:
  #        > ***   https://sourceware.org/glibc/wiki/#Development
  #        > *** and join the community!
  #        For full logs, run 'nix log /nix/store/f7gai4c7rgsylckm9660rwq8405lf57a-glibc-nolibgcc-2.37-8.drv'.
  # error (ignored): error: cannot unlink '/private/tmp/nix-build-Agda-lib-Agda-2.6.4.1.drv-0': Directory not empty
  # error: 1 dependencies of derivation '/nix/store/yf47kdqz8pslv22bfa66hlc0wv9jslfj-peras-design-env.drv' failed to build

  # Users should be instructed to put those values in `/etc/nix/conf`, the
  # following lines works only if your current user to trusted-users, but this is
  # essentially equivalent to giving that user root access to the system.
  #
  # nixConfig = {
  #   extra-substituters = [ "https://cache.iog.io" ];
  #   extra-trusted-public-keys =
  #     [ "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ=" ];
  #   allow-import-from-derivation = true;
  # };
}
