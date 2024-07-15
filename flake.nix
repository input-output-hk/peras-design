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
    agda2hs = {
      url = "github:agda/agda2hs/f5ac455b0d6e4364f4195918fe1cf215a3e8c434";
      flake = false;
    };
    agda2hsFlake = {
      url = "github:agda/agda2hs/f5ac455b0d6e4364f4195918fe1cf215a3e8c434";
      flake = true;
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
