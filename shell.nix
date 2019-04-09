# Hacl* libraries assume that user has f* and kremlin built from the
# source somewhere in the system, and that FSTAR_HOME and KREMLIN_HOME
# point to these directories directly. Another option would be to install
# f*, kremlin and z3 system-wide, but this is slightly tricker to do
# -- though we then definitely know which version is installed, and
# the absence of artifacts produced by makefiles make it easier to
# reason about different problems.
#
#
#
# The dirty installation on nixos will require opam to be installed
# globally (or via nix-env). Init it, install the switch required,
# add the line activating eval $(opam env) into your .bashrc or anything
# at the startup (opam will suggest to do it). Makefile.prepare has several
# related targets, prepare-ocaml installs required opam libraries, others
# clone and build big dependencies (f*, kremlin, z3).
#
# This shell file provides libraries that are required by the impure
# opam installation. Important notice: some opam packages like sqlite3-conf
# or zlib-conf use pkg-config in order to detect a library. Pkgconfig
# will only see them if it's included in the environment with the
# libraries that one needs, so pkgconfig is included in this shell.
# Installing these libraries globally is not required, and, moreover,
# is not recommended:
# https://nixos.wiki/wiki/FAQ/I_installed_a_library_but_my_compiler_is_not_finding_it._Why%3F
#
# So, enter this shell using nix-shell shell.nix, and then run 'make prepare-ocaml'.
# Set the two _HOME variables. Go to your custom directory with F* and build it
# using make, and do the same for kremlin. Make sure you clean up
# intermediate files produced by make (git clean -fx, git reset HEAD --hard).
# Hacl* will also assume that FStar/ and kremlin/ are directories at the same
# level as hacl-star, if you don't set up the two _HOME variables mentioned,
# so one can use this convention and not set the variables at all.
#
#
# The pure installation is WIP and here's a related important repository:
# https://github.com/blipp/nix-everest
#
# One can install big dependencies from it using nix-env and export
# FSTAR_HOME and KREMLIN_HOME variables in ~/.bashrc setting these
# to paths in /nix/store, and (hopefully) all hacl* builds will work as
# expected.

with import <nixpkgs> {}; {
  ocamlEnv = pkgsi686Linux.stdenv.mkDerivation {
    name = "ocamlEnv";
    buildInputs = with pkgs; [
      gmp
      zlib
      sqlite
      m4
      pkgconfig
    ];
  };
}
