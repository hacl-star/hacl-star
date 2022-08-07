#!/usr/bin/env bash

set -e

if [[ $HACL_HOME == "" ]]; then
  echo "Usage: HACL_HOME=<DIRECTORY> $0 [DEST_DIR]"
  echo "Please set a suitable value for HACL_HOME"
  exit 1
fi

if [[ $1 != "" ]]; then
  DEST=$1
else
  DEST=$(realpath $HACL_HOME/..)
fi

echo -n "Will install vale into $DEST/vale, hit Ctrl-C to abort"
sleep 1
echo -n .
sleep 1
echo -n .
sleep 1
echo .

cd $DEST

if [ ! -d vale ]; then
  mkdir vale
fi

vale_version=$(<$HACL_HOME/vale/.vale_version)
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
  pwd
  echo
  echo -e "\033[0;31mRemember to do:\033[0;0m"
  echo "export VALE_HOME=$(realpath $HACL_HOME/..)/vale"
else
  echo "Vale is up-to-date"
fi

cp $HACL_HOME/runtimeconfig.json vale/bin/vale.runtimeconfig.json
cp $HACL_HOME/runtimeconfig.json vale/bin/importFStarTypes.runtimeconfig.json
