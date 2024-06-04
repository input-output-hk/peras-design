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
}
