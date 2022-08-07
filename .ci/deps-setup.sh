#!/bin/bash

set -o pipefail
set -e

eval $(opam config env)
source $HOME/.bash_profile
cat $HOME/.bash_profile

cd ..
./everest --yes pull_vale
./everest --yes FStar pull_projects FStar make --admit -j 6

export FSTAR_HOME=$(pwd)/FStar
export KRML_HOME=$(pwd)/karamel

# TODO: MLCrypto really needs to go

./everest --yes MLCrypto pull_projects MLCrypto make --admit -j 6

export MLCRYPTO_HOME=$(pwd)/MLCrypto
export OPENSSL_HOME=$(pwd)/openssl

pwd

git config --global user.email "foobar@example.com"
git config --global user.name "Foo Bar"
if ! ./everest --yes karamel pull_projects karamel make --admit -j 6; then
  cd karamel && git cherry-pick 49372568 && OTHERFLAGS="--admit_smt_queries true" make -j 6
fi
# TODO: remove hack above
