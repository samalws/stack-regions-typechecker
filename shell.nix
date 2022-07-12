{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  buildInputs = [ (pkgs.ghc.withPackages (p: [p.data-default p.MissingH])) ];
}
