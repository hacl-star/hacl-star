
let nixeverest = import /home/volhovm/code/nix-everest/nixexprs {}; in
with import <nixpkgs> { };
haskell.lib.buildStackProject {
   ghc = haskell.packages.ghc865.ghc;
   name = "hestarhs";
   buildInputs = [ nixeverest.kremlin-master pkgconfig zlib ];
   LD_LIBRARY_PATH = [
     "/home/volhovm/code/hacl-star/code/experimental/he"
   ];
   LANG = "en_US.UTF-8";
}

