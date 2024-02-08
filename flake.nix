{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-23.05";
    flake-parts.url = "github:hercules-ci/flake-parts";
  };
  outputs = inputs:
    inputs.flake-parts.lib.mkFlake {inherit inputs;} {
      systems = ["x86_64-linux" "aarch64-darwin"];
      perSystem = {pkgs, ...}: let
        agda = pkgs.agda.withPackages (p: [p.standard-library]);
        agda2hs = pkgs.haskellPackages.agda2hs;
      in {
        devShells.default = pkgs.mkShell {
          buildInputs = [agda agda2hs];
        };
      };
    };
}
