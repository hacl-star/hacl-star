#!/bin/bash

set -e

if [[ $HACL_HOME == "" ]]; then
  echo "Usage: HACL_HOME=<DIRECTORY> $0"
  echo "Please set a suitable value for HACL_HOME"
  exit 1
fi

echo -n "Will install vale into $(realpath $HACL_HOME/..)/vale, hit Ctrl-C to abort"
sleep 1
echo -n .
sleep 1
echo -n .
sleep 1
echo .

cd $HACL_HOME/..

if [ ! -d hacl-star ]; then
  echo \$HACL_HOME/../hacl-star does not exist
  exit 1
fi

if [ ! -d vale ]; then
  mkdir vale
fi

vale_version=$(<hacl-star/vale/.vale_version)
vale_version=${vale_version%$'\r'}  # remove Windows carriage return, if it exists

old_vale_version=none
if [ -e vale/bin/.vale_version ]; then
  old_vale_version=$(<vale/bin/.vale_version)
  old_vale_version=${old_vale_version%$'\r'}  # remove Windows carriage return, if it exists
fi

if [ $vale_version != $old_vale_version ]; then
  wget "https://github.com/project-everest/vale/releases/download/v${vale_version}/vale-release-${vale_version}.zip" -O vale/vale-release.zip
  rm -rf "vale/vale-release-${vale_version}"
  unzip -o vale/vale-release.zip -d vale
  rm -rf "vale/bin"
  mv "vale/vale-release-${vale_version}/bin" vale/
  chmod +x vale/bin/*.exe
  echo
  echo -e "\033[0;31mRemember to do:\033[0;0m"
  echo "export VALE_HOME=$(realpath $HACL_HOME/..)/vale"
else
  echo "Vale is up-to-date"
fi
