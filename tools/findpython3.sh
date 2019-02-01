#!/bin/bash

set -e
set -o pipefail

candidates="python3 python python3.6 python3.7"

function try() {
  if echo "import sys; sys.exit (not (sys.version_info >= (3, 6)))" | $1; then
    echo -n $1
  else
    false
  fi
}

found=false
for c in $candidates; do
  if try $c; then
    found=true
    break
  fi
done
if ! $found; then
  echo "None of $candidates was a valid version of python3 (we want: >= 3.6)" 1>&2
  false
fi
