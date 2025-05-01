#!/nix/store/58br4vk3q5akf4g8lx0pqzfhn47k3j8d-bash-5.2p37/bin/bash

set -o pipefail
set -e

if [[ "${BASH_VERSINFO[0]}" -lt 4 ]]; then
  echo "A bash version >= 4 required. Got: $BASH_VERSION" >&2
  exit 1
fi

if [[ $(uname) == "Darwin" ]]; then
  # You're already running with homebrew or macports to satisfy the
  # bash>=4 requirement, so requiring GNU sed is entirely reasonable.
  sed=gsed
else
  sed=sed
fi

# If FOO appears in FILES, then FOO.h, FOO.c, internal/FOO.h, FOO.asm, FOO.S and
# FOO all get copied unconditionally to dist/mozilla (as long as they exist)
FILES=" \
  Hacl_Bignum \
  Hacl_Bignum25519_51 \
  Hacl_Bignum_Base \
  Hacl_Chacha20 \
  Hacl_AEAD Chacha20Poly1305_Simd128 \
  Hacl_AEAD_Chacha20Poly1305_Simd256 \
  Hacl_AEAD_Chacha20Poly1305 \
  Hacl_Chacha20_Vec128 \
  Hacl_Chacha20_Vec256 \
  Hacl_Curve25519_51 \
  Hacl_Curve25519_64 \
  Hacl_Hash_SHA1 \
  Hacl_Hash_SHA2 \
  Hacl_Hash_SHA3 \
  Hacl_IntTypes_Intrinsics \
  Hacl_IntTypes_Intrinsics_128 \
  Hacl_Krmllib \
  Hacl_Lib \
  Hacl_MAC_Poly1305_Simd128 \
  Hacl_MAC_Poly1305_Simd256 \
  Hacl_MAC_Poly1305 \
  Hacl_P256 \
  Hacl_P256_PrecompTable \
  Hacl_RSAPSS \
  Hacl_SHA2_Types \
  Hacl_Spec \
  Hacl_Streaming_Types \
  Lib_Memzero0 \
  TestLib \
  Vale \
  curve25519-inline \
  curve25519-x86_64-darwin \
  curve25519-x86_64-linux \
  curve25519-x86_64-mingw \
  curve25519-x86_64-msvc \
  libintvector \
  lib_memzero0 \
  lib_intrinsics \
  configure \
  Makefile \
  Makefile.basic"

mkdir -p mozilla/internal

for f in $FILES; do
  for ext in h c asm S; do
    [ -f msvc-compatible/$f.$ext ] && cp msvc-compatible/$f.$ext mozilla/ || true
  done
  [ -f msvc-compatible/internal/$f.h ] && cp msvc-compatible/internal/$f.h mozilla/internal || true
  # Makefile, etc.
  [ -f msvc-compatible/$f ] && cp msvc-compatible/$f mozilla || true
done

# The P256 file contains variants of ECDSA that sign the message.
# We strip these functions.
# This regexp matches a separator (two new lines), followed by:
#
# <non-empty-line>*
# ... _p256_sha ... {
#   <indented-line>*
# }
#
# The first non-empty lines are the comment block. The second ... may spill over
# the next following lines if the arguments are printed in one-per-line mode.
$sed -i -z 's/\n\n\/\*\*[^*]*\*\/\n\([^\n]\+\n\)*[^\n]*_p256_sha[^{]*{\n\?\(  [^\n]*\n\)*}//g' mozilla/Hacl_P256.c

# Same thing with function prototypes
$sed -i -z 's/\n\n\/\*\*[^*]*\*\/\n\([^\n]\+\n\)*[^\n]*_p256_sha[^;]*;//g' mozilla/Hacl_P256.h

# Remove the SHA2 header from P256
$sed -i -z 's/\n#include "Hacl_Hash_SHA2.h"\n/\n/g' mozilla/Hacl_P256.h

# Remove the "should-hash" recommendation
$sed -i -z 's/\n\n\/\*\n  As per[^/]*\*\///g' mozilla/Hacl_P256.h

# Remove the "should-hash" recommendation
$sed -i -z 's/\n\n\/\*\n  As per[^/]*\*\///g' mozilla/Hacl_P256.c

# Add an include for "builtin.h" to Hacl_Bignum_Base.h
sed -i -z 's!\(#include.*types.h"\)!\1\n#include "krml/internal/builtin.h"!g' mozilla/internal/Hacl_Bignum_Base.h


cat <<EOF > mozilla/Makefile.include
USER_TARGET=libevercrypt.a
USER_CFLAGS=-Wno-unused
USER_C_FILES=Lib_Memzero0.c
ALL_C_FILES=$(ls mozilla/*.c | xargs basename -a | xargs echo)
ALL_H_FILES=$(ls mozilla/*.h | xargs basename -a | xargs echo)
EOF
