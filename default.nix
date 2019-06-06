{ nixpkgs ? import <nixpkgs> {}, ghc ? nixpkgs.haskell.packages.ghc861 }:
with nixpkgs;

stdenv.mkDerivation {
  name = "thc";
  buildInputs = [ (ghc.ghcWithPackages (ps: with ps; [ text containers fingertree Cabal ])) cabal-install ];
}
