{ pkgs, ... }:

pkgs.emacs.pkgs.withPackages (epkgs: [ epkgs.agda2-mode pkgs.mononoki ])
