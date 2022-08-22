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

pwd

git config --global user.email "foobar@example.com"
git config --global user.name "Foo Bar"
./everest --yes karamel pull_projects karamel make --admit -j 6
