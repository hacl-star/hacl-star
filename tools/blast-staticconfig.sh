#!/bin/bash

set -e

NEW_CONFIG=$1
OLD_CONFIG=$(test -f .evercrypt_config && cat .evercrypt_config || echo "")
OLD_CONFIG_FILE=obj/EverCrypt.StaticConfig.fst.checked

if [[ $NEW_CONFIG != $OLD_CONFIG ]]; then
  if [[ -f $OLD_CONFIG_FILE ]]; then
    rm -f $OLD_CONFIG_FILE
    echo "... detected config change, removed $OLD_CONFIG_FILE"
  fi
  echo $NEW_CONFIG > .evercrypt_config
fi
