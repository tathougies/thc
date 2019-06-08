{ nixpkgs ? import <nixpkgs> {}, ghc ? nixpkgs.haskell.packages.ghc863 }:
with nixpkgs;

stdenv.mkDerivation {
  name = "thc";
  buildInputs = [ (ghc.ghcWithPackages (ps: with ps; [ text haskell-lsp ansi-terminal containers fingertree Cabal ])) cabal-install ];
}
