#!/usr/bin/env bash

set -o pipefail
set -e

# If FOO appears in FILES, then FOO.h, FOO.c, internal/FOO.h, FOO.asm, FOO.S and
# FOO all get copied unconditionally to dist/mozilla (as long as they exist)
FILES=" \
  Hacl_Bignum \
  Hacl_Bignum25519_51 \
  Hacl_Bignum_Base \
  Hacl_Chacha20 \
  Hacl_Chacha20Poly1305_128 \
  Hacl_Chacha20Poly1305_256 \
  Hacl_Chacha20Poly1305_32 \
  Hacl_Chacha20_Vec128 \
  Hacl_Chacha20_Vec256 \
  Hacl_Curve25519_51 \
  Hacl_Curve25519_64 \
  Hacl_Hash_SHA1 \
  Hacl_Hash_SHA2 \
  Hacl_IntTypes_Intrinsics \
  Hacl_IntTypes_Intrinsics_128 \
  Hacl_Lib \
  Hacl_Poly1305_128 \
  Hacl_Poly1305_256 \
  Hacl_Poly1305_32 \
  Hacl_RSAPSS \
  Hacl_SHA2_Types \
  Hacl_SHA3 \
  Hacl_Spec \
  Hacl_Streaming_SHA1 \
  Hacl_Streaming_SHA3 \
  Lib_Memzero0 \
  TestLib \
  Vale \
  curve25519-inline \
  curve25519-x86_64-darwin \
  curve25519-x86_64-linux \
  curve25519-x86_64-mingw \
  curve25519-x86_64-msvc \
  libintvector \
  lib_intrinsics \
  configure \
  Makefile \
  Makefile.basic"

mkdir -p mozilla/internal

# For these, we want just the header
cp gcc-compatible/Hacl_Krmllib.h mozilla/
cp gcc-compatible/internal/Hacl_Streaming_SHA2.h mozilla/internal/
cp gcc-compatible/Hacl_Streaming_SHA2.h mozilla/
cp gcc-compatible/Hacl_Hash_SHA2.h mozilla/
cp gcc-compatible/Hacl_SHA2_Generic.h mozilla/

for f in $FILES; do
  for ext in h c asm S; do
    [ -f gcc-compatible/$f.$ext ] && cp gcc-compatible/$f.$ext mozilla/ || true
  done
  [ -f gcc-compatible/internal/$f.h ] && cp gcc-compatible/internal/$f.h mozilla/internal || true
  # Makefile, etc.
  [ -f gcc-compatible/$f ] && cp gcc-compatible/$f mozilla || true
done

cat <<EOF > mozilla/Makefile.include
USER_TARGET=libevercrypt.a
USER_CFLAGS=-Wno-unused
USER_C_FILES=Lib_Memzero0.c
ALL_C_FILES=$(ls mozilla/*.c | xargs basename -a | xargs echo)
ALL_H_FILES=$(ls mozilla/*.h | xargs basename -a | xargs echo)
EOF
