#!/usr/bin/env bash

# A script for counting the number of lines of code in this repository into
# buckets based on a series of regexps.

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
    # Uncomment the line below to debug and to check that things are bucketized
    # properly.
    # echo $1 is a match for $2
    local v=${buckets[$2]}
    local l=$(mywc $1)
    buckets[$2]=$(($v + $l))
  else
    false
  fi
}

total=0

# Regexps are matched in order. To improve on this script, just insert a fresh
# regexps in the right position, then insert a label at the exact same position.
# It is a good idea to compare the output of the script before and after.

declare -a regexps
regexps=(
  ".vaf$"
  "^./obj"
  "^./specs/Spec."
  "^./vale/specs/crypto/Vale.AES"
  "^./specs/"
  "^./vale/specs/interop"
  "^./vale/specs/\(defs\|hardware\|math\)"
  "^./vale/specs/crypto"
  "^./vale/code"
  "^./code/experimental"
  "^./code"
  "^./lib"
  "^./secure_api/merkle_tree"
  "^./providers/test"
  "^./providers/evercrypt")

declare -a labels
labels=( \
  "Vale source files (.vaf)"
  "Generated F* files (from .vaf files)"
  "Reference (HACL) spec files"
  "Vale GCM spec (a reference spec used for AEAD)"
  "Auxiliary spec files (lemmas, derived specs, tests)"
  "Vale interop"
  "Vale hardware specs"
  "Other Vale crypto specs (proven equivalent to reference spec)"
  "Vale code"
  "Experimental Low* code"
  "Low* algorithms"
  "Low* support libraries"
  "Merkle Tree"
  "EverCrypt tests"
  "EverCrypt")

# Everything is zero by default.
for r in ${regexps[@]}; do
  buckets[$r]=0
done

# Note: explicitly avoiding AES_s.fst since the spec already exists in specs/
for file in $($FIND . -\( -iname '*.fst' -or -iname '*.fsti' -or -iname '*.vaf' -\) \
    -and -not -iname '*.types.vaf' -and -not -ipath './code/old/*' \
    -and -not -ipath './specs/old/*' -and -not -ipath './doc/*' \
    -and -not -iname 'Vale.AES.AES_s.fst'); do
  total=$(($total + $(mywc $file)))
  found=false
  for r in ${regexps[@]}; do
    if matches $file $r; then
      found=true
      break
    fi
  done
  if ! $found; then
    echo $file was not bucketized but still counts towards the total
  fi
done

for r in ${!regexps[@]}; do
  echo -e "${labels[$r]}: ${buckets[${regexps[r]}]}"
done

echo "Total: $total"
