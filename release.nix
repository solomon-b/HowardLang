let
  sources = import ./nix/sources.nix;
  pkgs = import sources.nixpkgs { };
in
  pkgs.haskellPackages.callPackage ./default.nix { }
