#!/usr/bin/env bash

set -e
set -o pipefail

if [[ $(uname -s) == "Darwin" ]]; then
  FIND=gfind
else
  FIND=find
fi

if ! [ -d code ]; then
  echo "Error: this script expects to be run from the root of HACL*, e.g. ./tools/$0"
  exit 1
fi

declare -A buckets

function mywc () {
  wc -l $1 | sed 's/^ *\([0-9]*\).*/\1/'
}

function matches () {
  if echo $1 | grep -q $2; then
    #echo $1 is a match for $2
    local v=${buckets[$2]}
    local l=$(mywc $1)
    buckets[$2]=$(($v + $l))
  else
    false
  fi
}

total=0

for file in $($FIND . -\( -iname '*.fst' -or -iname '*.fsti' -or -iname '*.vaf' -\) \
    -and -not -iname '*.types.vaf' -and -not -ipath './code/old/*' \
    -and -not -ipath './specs/old/*' -and -not -ipath './doc/*'); do
  total=$(($total + $(mywc $file)))
  matches $file '\.vaf$' ||
  matches $file '^./obj' ||
  matches $file '^./specs/Spec.' ||
  matches $file '^./vale/specs/interop' ||
  matches $file '^./vale/specs/\(defs\|hardware\|math\|crypto/Vale.AES\)' ||
  matches $file '^./vale/specs/crypto' ||
  matches $file '^./vale/code' ||
  matches $file '^./code/experimental' ||
  matches $file '^./code' ||
  matches $file '^./lib' ||
  matches $file '^./secure_api/merkle_tree' ||
  matches $file '^./providers/evercrypt' ||
  echo no match for $file
done

for k in ${!buckets[@]}; do
  echo -e "Lines for $k: ${buckets[$k]}"
done

echo "total: $total"
