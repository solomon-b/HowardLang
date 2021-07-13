let
  sources = import ./nix/sources.nix;
  pkgs = import sources.nixpkgs { };
  project = import ./release.nix;
in
pkgs.stdenv.mkDerivation {
  name = "shell";
  buildInputs = project.env.nativeBuildInputs ++ [
    pkgs.cabal-install
  ];
}
