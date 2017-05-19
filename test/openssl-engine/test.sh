#!/bin/bash
set -e

if [[ $1 == "" || $2 == "" ]]; then
  echo Usage: $0 OPENSSL_HOME ENGINE
  exit 0
fi

OPENSSL_HOME=$1
ENGINE=$2
EXE=

if [[ $(uname) == "Darwin" ]]; then
  export DYLD_LIBRARY_PATH=$OPENSSL_HOME:"$DYLD_LIBRARY_PATH"
elif [[ $(uname) == "Linux" ]]; then
  export LD_LIBRARY_PATH=$OPENSSL_HOME:"$LD_LIBRARY_PATH"
elif [[ $(uname) == "CYGWIN" ]]; then
  export PATH=$OPENSSL_HOME:"$PATH"
  EXE=".exe"
fi

tput setaf 1
echo Running with engine: $ENGINE
tput sgr0
# Due to a bug in OpenSSL: ciphers first, message digests later.
$OPENSSL_HOME/apps/openssl$EXE 2>&1 <<EOF | tee log
  engine $ENGINE
  speed -engine Everest ecdhx25519
  speed -engine Everest -evp chacha20
  speed -engine Everest -evp chacha20-poly1305
  speed -engine Everest -evp sha256
  speed -engine Everest -evp sha512
  speed -engine Everest -evp poly1305
EOF

sed=sed
if command -v gsed >/dev/null 2>&1; then
  sed=gsed
fi

SO=$(basename $2)
tput setaf 1
echo Generating CSV results in log-$SO.csv
tput sgr0
cat log | \
  egrep "^(type|Doing 253)" -A 1 | \
  egrep -v "^(OpenSSL|--|Warning)" | \
  $sed 's/for 3s.*//' | \
  $sed 's/\ \{2,\}/,/g' | \
  uniq > log-$SO.csv
