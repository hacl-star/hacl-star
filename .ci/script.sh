#!/usr/bin/env bash

set -e
set -o pipefail

# For OSX... seems like the most reliable way to figure out which OpenSSL is
# installed? We have both 1.1.1d and 1.1.1f and neither can be installed on the
# other configuration.
for p in /usr/local/Cellar/openssl@1.1/*; do export CFLAGS="-I$p/include/"; export LDFLAGS="-L$p/lib"; done

# Most likely running without OCaml -- need to configure
pushd dist/gcc-compatible
./configure
make -j
popd

if [[ "$(uname -m | cut -c 1-7)" == "aarch64" ]]; then
  make -C tests arm -j
else
  make -C tests -j test

  # Extracted C tests -- need full kremlib, don't work on ARM because of
  # intrinsics for x86 in cpu cycle count routines in testlib.c
  pushd dist/test/c/
  git clone https://github.com/fstarlang/kremlin --depth 10
  export KREMLIN_HOME=$(pwd)/kremlin
  make -C kremlin/kremlib/dist/generic -f Makefile.basic -j
  make -j -k
  popd
fi

if which opam; then
  make -C dist/gcc-compatible install-hacl-star-raw
  pushd bindings/ocaml
  dune build
  dune runtest
  dune install
  popd
fi
