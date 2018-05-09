#include <stdio.h>
#include <stdlib.h>

#include "EverCrypt_Hacl.h"
#include "Hacl_SHA2_256.h"
#include "Hacl_SHA2_384.h"
#include "Hacl_SHA2_512.h"
#include "Hacl_Curve25519.h"

void EverCrypt_Hacl_sha256_init(uint32_t *x0) {
  Hacl_SHA2_256_init(x0);
}

void EverCrypt_Hacl_sha256_update(uint32_t *x0, uint8_t *x1) {
  Hacl_SHA2_256_update(x0, x1);
}

void EverCrypt_Hacl_sha256_update_multi(uint32_t *x0, uint8_t *x1, uint32_t x2) {
  Hacl_SHA2_256_update_multi(x0, x1, x2);
}

void EverCrypt_Hacl_sha256_update_last(uint32_t *x0, uint8_t *x1, uint32_t x2) {
  Hacl_SHA2_256_update_last(x0, x1, x2);
}

void EverCrypt_Hacl_sha256_finish(uint32_t *x0, uint8_t *x1) {
  Hacl_SHA2_256_finish(x0, x1);
}

void EverCrypt_Hacl_sha256_hash(uint8_t *x0, uint8_t *x1, uint32_t x2) {
  Hacl_SHA2_256_hash(x0, x1, x2);
}

void EverCrypt_Hacl_sha384_init(uint64_t *x0) {
  Hacl_SHA2_384_init(x0);
}

void EverCrypt_Hacl_sha384_update(uint64_t *x0, uint8_t *x1) {
  Hacl_SHA2_384_update(x0, x1);
}

void EverCrypt_Hacl_sha384_update_multi(uint64_t *x0, uint8_t *x1, uint32_t x2) {
  Hacl_SHA2_384_update_multi(x0, x1, x2);
}

void EverCrypt_Hacl_sha384_update_last(uint64_t *x0, uint8_t *x1, uint32_t x2) {
  Hacl_SHA2_384_update_last(x0, x1, x2);
}

void EverCrypt_Hacl_sha384_finish(uint64_t *x0, uint8_t *x1) {
  Hacl_SHA2_384_finish(x0, x1);
}

void EverCrypt_Hacl_sha384_hash(uint8_t *x0, uint8_t *x1, uint32_t x2) {
  Hacl_SHA2_384_hash(x0, x1, x2);
}

void EverCrypt_Hacl_sha512_init(uint64_t *x0) {
  Hacl_SHA2_512_init(x0);
}

void EverCrypt_Hacl_sha512_update(uint64_t *x0, uint8_t *x1) {
  Hacl_SHA2_512_update(x0, x1);
}

void EverCrypt_Hacl_sha512_update_multi(uint64_t *x0, uint8_t *x1, uint32_t x2) {
  Hacl_SHA2_512_update_multi(x0, x1, x2);
}

void EverCrypt_Hacl_sha512_update_last(uint64_t *x0, uint8_t *x1, uint32_t x2) {
  Hacl_SHA2_512_update_last(x0, x1, x2);
}

void EverCrypt_Hacl_sha512_finish(uint64_t *x0, uint8_t *x1) {
  Hacl_SHA2_512_finish(x0, x1);
}

void EverCrypt_Hacl_sha512_hash(uint8_t *x0, uint8_t *x1, uint32_t x2) {
  Hacl_SHA2_512_hash(x0, x1, x2);
}

void EverCrypt_Hacl_x25519(uint8_t *dst, uint8_t *secret, uint8_t *base) {
  Hacl_Curve25519_crypto_scalarmult(dst, secret, base);
}
