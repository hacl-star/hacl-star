#!/bin/bash

set -o pipefail
set -e

cd ..
git init .
git pull https://github.com/project-everest/everest.git # protz_remove_Scons
export OPAMYES=true
opam init --auto-setup --disable-sandboxing --comp 4.12.0 --yes
eval $(opam config env)
./everest --yes check
