#!/bin/bash

set -e

NEW_CONFIG=$1
OLD_CONFIG=$(test -f .evercrypt_config && cat .evercrypt_config || echo "")

# See https://github.com/FStarLang/FStar/issues/1657 as to why we have to remove
# the .fsti
CONFIG_FILES="obj/EverCrypt.StaticConfig.fst.checked obj/EverCrypt.TargetConfig.fsti.checked obj/EverCrypt.TargetConfig.fst.checked"

if [[ $NEW_CONFIG != $OLD_CONFIG ]]; then
  for f in $CONFIG_FILES; do
    if [[ -f $f ]]; then
      rm -f $f
      echo "... detected config change, removed $f"
    fi
  done
  echo $NEW_CONFIG > .evercrypt_config
fi
