#!/usr/bin/env bash
set -e
set -o pipefail

if [[ $1 == "" ]]; then
  echo "USAGE: $0 DST where DST is the directory in which files have to be copied"
  exit 1
fi

if which gsed &>/dev/null; then
  SED=gsed
else
  SED=sed
fi

if which gfind &>/dev/null; then
  FIND=gfind
else
  FIND=find
fi

make html
cp -R _build/html/* $1

mkdir -p $1/javascript_doc
cp -R ../dist/wasm/doc/out/* $1/javascript_doc

mkdir -p $1/ocaml_doc
cp -R ../bindings/ocaml/_build/default/_doc/_html/* $1/ocaml_doc

cd $1
rm -rf static && mv _static static
rm -rf images && mv _images images
$FIND . -type f | grep -v '\.git' | xargs $SED -i 's/_static/static/g'
$FIND . -type f | grep -v '\.git' | xargs $SED -i 's/_images/images/g'
$FIND . -type f | grep -v '\.git' | xargs $SED -i 's/_sources/sources/g'
