#!/bin/bash

set -e
set -o pipefail

candidates="python3 python python3.6 python3.7 python3.8"

# $1: executable to try (in the path)
function try() {
  if which $1 &>/dev/null && \
    echo "import sys; sys.exit (not (sys.version_info >= (3, 6)))" | $1;
  then
    echo -n $1
  else
    false
  fi
}

# $1: version to try (e.g. 3.6)
try_windows () {
    PYDIR=$(regtool -q get "/HKLM/Software/Python/PythonCore/$1/InstallPath/" || true)
    if ! [[ -d $PYDIR ]] ; then
      PYDIR=$(regtool -q get "/HKCU/Software/Python/PythonCore/$1/InstallPath/" || true)
    fi
    if [[ -d $PYDIR ]] ; then
      echo "$PYDIR/python.exe" | sed 's!\\!/!g'
    else
      false
    fi
}


found=false

if [[ $OS == "Windows_NT" ]]; then
  for v in 3.6 3.7 3.8; do
    if try_windows $v; then
      found=true
      break
    fi
  done
fi

if $found; then
  exit 0
fi

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
