#!/bin/bash

cwd=$(cd $(dirname $0); pwd -P)

# Patch files where file names changed.
patch "$cwd/../../snapshots/nss/hacl_curve25519_64.c" < "$cwd/hacl_curve25519_64.c.patch"

# Get snapshots/kremlib/gcc_compat.h into kremlib.h
gcc_compat=$(cat "$cwd/../../snapshots/kremlib/gcc_compat.h")
$(SED) -i "/.*gcc_compat.h.*/r$cwd/../../snapshots/kremlib/gcc_compat.h" "$cwd/../../snapshots/nss/kremlib.h"
$(SED) -i '/gcc_compat.h/d' "$cwd/../../snapshots/nss/kremlib.h"
$(SED) -i '/__GCC_COMPAT_H/d' "$cwd/../../snapshots/nss/kremlib.h"
