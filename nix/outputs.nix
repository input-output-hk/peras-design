{ repoRoot, inputs, pkgs, lib, system }:

let
  project = repoRoot.nix.project;
  peras-agda = repoRoot.nix.peras-agda;
  rust = repoRoot.nix.rust;
  html-spec = pkgs.writeScriptBin "peras-html-spec" ''
    export PATH=${repoRoot.nix.agda-with-stdlib}/bin:${repoRoot.nix.agda2hs.exe}/bin:${pkgs.pandoc}/bin:$PATH
    .github/workflows/scripts/agda-2-html.sh
  '';
in
[
  (project.flake)
  {
    inherit repoRoot;
    packages.peras = peras-agda;
    devShells.profiled = project.variants.profiled.devShell;
    packages.peras-html-spec = html-spec;
  }
]
