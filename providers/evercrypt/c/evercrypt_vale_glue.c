#include <stdio.h>
#include <stdlib.h>

#include "kremlin/internal/target.h"
#include "EverCrypt_ValeGlue.h"

// This is SUPER stale and the .h can't even be generated anymore for the module
// called Vale.Hash.SHA2_256.fst -- currently in secure_api/vale. Rather than
// fix this sad, sad, mess, write out the function prototypes as seen in the C
// file.
void Vale_Hash_SHA2_256_init(uint32_t *state);
void Vale_Hash_SHA2_256_update(uint32_t *state, uint8_t *data);
void Vale_Hash_SHA2_256_update_last(uint32_t *state, uint8_t *data, uint32_t len);
void Vale_Hash_SHA2_256_finish(uint32_t *state, uint8_t *dst);
void Vale_Hash_SHA2_256_hash(uint32_t *dst, uint8_t *data, uint32_t len);

void EverCrypt_ValeGlue_sha256_init(uint32_t *x0){
  Vale_Hash_SHA2_256_init(x0);
}

void EverCrypt_ValeGlue_sha256_update(uint32_t *x0, uint8_t *x1){
  Vale_Hash_SHA2_256_update(x0, x1);
}

void EverCrypt_ValeGlue_sha256_update_multi(uint32_t *x0, uint8_t *x1, uint32_t x2){
  for (uint32_t i = 0; i < x2; i++) {
    uint8_t *b = x1 + i * 64;
    Vale_Hash_SHA2_256_update(x0, b);
  }
}

void EverCrypt_ValeGlue_sha256_update_last(uint32_t *x0, uint8_t *x1, uint32_t x2){
  Vale_Hash_SHA2_256_update_last(x0, x1, x2);
}

void EverCrypt_ValeGlue_sha256_finish(uint32_t *x0, uint8_t *x1){
  Vale_Hash_SHA2_256_finish(x0, x1);
  // Reverse byte-order in little-endian hosts
  for (int i = 0; i < 8; i++) {
    uint32_t *out = (uint32_t *) x1;
    store32_be((uint8_t *) &out[i], out[i]);
  }
}

void EverCrypt_ValeGlue_sha256_hash(uint8_t *x0, uint8_t *x1, uint32_t x2){
  KRML_HOST_EPRINTF("TODO: sha256_hash/Vale\n");
  KRML_HOST_EXIT(255);
}
