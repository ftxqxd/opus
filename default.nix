with import <nixpkgs> {};

stdenv.mkDerivation rec {
  name = "opus";

  src = ./.;

  buildInputs = [ llvm_7 libxml2 ];
}
