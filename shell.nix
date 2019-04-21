# Hacl* libraries assume that user has F* and kremlin built from the
# source somewhere in the system, and that FSTAR_HOME and KREMLIN_HOME
# point to these directories directly. Another option would be to install
# F*, kremlin and z3 system-wide, but this is slightly tricker to do
# -- though we then definitely know which version is installed, and
# the absence of artifacts produced by makefiles make it easier to
# reason about different problems.
#
#
# #### Dirty installation
#
# The dirty installation on nixos will require opam to be installed
# globally (or via nix-env). Init it, install the switch required,
# add the line activating eval $(opam env) into your .bashrc or anything
# at the startup (opam will suggest to do it). Makefile.prepare has several
# related targets, prepare-ocaml installs required opam libraries, others
# clone and build big dependencies (f*, kremlin, z3).
#
# This shell file provides more libraries than it is required by the impure
# opam installation, so just use nix-shell -p <libraries from gmp pkgconfig
# from the first block>. Important notice: some opam packages like sqlite3-conf
# or zlib-conf use pkg-config in order to detect a library. Pkgconfig
# will only see them if it's included in the environment with the
# libraries that one needs, so pkgconfig is included in this shell.
# Installing these libraries globally is not required, and, moreover,
# is not recommended:
# https://nixos.wiki/wiki/FAQ/I_installed_a_library_but_my_compiler_is_not_finding_it._Why%3F
#
# So, after nix-shell -p, run 'make prepare-ocaml'.
# Set the two _HOME variables. Go to your custom directory with F* and build it
# using make, and do the same for kremlin. Make sure you clean up
# intermediate files produced by make (git clean -fx, git reset HEAD --hard).
# Hacl* will also assume that FStar/ and kremlin/ are directories at the same
# level as hacl-star, if you don't set up the two _HOME variables mentioned,
# so one can use this convention and not set the variables at all.
#
#
# #### Pure installation
#
# The pure installation is supposed to be much simpler, and it relies on the
# following repository:
#
# https://github.com/blipp/nix-everest
#
# One can install big dependencies from it using nix-env and export
# FSTAR_HOME and KREMLIN_HOME variables in ~/.bashrc setting these
# to paths in /nix/store like this:
#
# export FSTAR_HOME=$(nix-env -q --out-path --no-name fstar-master)
# export KREMLIN_HOME=$(nix-env -q --out-path --no-name kremlin-master)
#
# and (hopefully) all hacl* builds will work as expected.
#
# Entering this shell will provide hacl-star with all the necessary
# packages to compile. Make sure you unset your opam initialisation in
# ~/.bashrc so that nixpkgs ocaml comes first, as versions must match.

let
  pkgs = import <nixpkgs> {};
  #nixeverest_repo = builtins.fetchGit {
  #  url = https://github.com/blipp/nix-everest;
  #  rev = "52618c9d4b999810103b765837c75c3324693aa3";
  #} + "/nixexprs/default.nix";
  #nixeverest = import nixeverest_repo {};
  nixeverest = import ~/code/nix-everest/nixexprs/default.nix {};
in
{
  ocamlEnv = pkgs.stdenv.mkDerivation {
    name = "hacl-star-env";
    buildInputs = with pkgs; [
      # These are libraries that you need to build dependencies,
      # not used for hacl-star directly
      gmp
      zlib
      sqlite
      m4
      pkgconfig

      # Ocaml and related libraries
      ocamlPackages.ocaml
      ocamlPackages.findlib

      ocamlPackages.batteries
      ocamlPackages.fileutils
      #ocamlPackages.fix
      #ocamlPackages.menhir
      #ocamlPackages.pprint
      ocamlPackages.ppx_deriving_yojson
      #ocamlPackages.process
      #ocamlPackages.ocaml_sqlite3
      ocamlPackages.stdint
      #ocamlPackages.ulex
      #ocamlPackages.wasm
      #ocamlPackages.yojson
      ocamlPackages.zarith

      # Included, as fstar-master also provides ocaml library
      nixeverest.fstar-master
      nixeverest.kremlin-master
    ];
  };
}
