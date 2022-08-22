#!/bin/bash

set -o pipefail
set -e

eval $(opam config env)
# TODO: why is this not working?
source $HOME/.bash_profile

export FSTAR_HOME=$(pwd)/../FStar
export KRML_HOME=$(pwd)/../karamel
export VALE_HOME=$(pwd)/../vale
export HACL_HOME=$(pwd)

export NOOPENSSLCHECK=1
make -j 6
make test-unstaged doc-wasm doc-ocaml
