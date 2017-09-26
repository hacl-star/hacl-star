#!/bin/bash

cwd=$(cd $(dirname $0); pwd -P)

# Add license headers to all files.
for file in `find "$cwd/../../snapshots/nss/" -type f`; do
    echo -e "$(cat $cwd/license.txt)\n\n$(cat $file)" > "$file"
done

# Patch files where file names changed.
patch "$cwd/../../snapshots/nss/hacl_curve25519_64.h" < "$cwd/hacl_curve25519_64.h.patch"
patch "$cwd/../../snapshots/nss/hacl_curve25519_64.c" < "$cwd/hacl_curve25519_64.c.patch"
