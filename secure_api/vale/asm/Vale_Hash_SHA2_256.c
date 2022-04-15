#include <stdlib.h>
#include <stdio.h>
#include <inttypes.h>

// From Vale's build tree:
#include "sha256_main_i.h"

#define SHA256_BLOCK_SIZE_B 64

struct KrmlWorkaround {
  sha256_main_i_SHA256Context ctx_value;
  uint32_t H_value[8];
  uint8_t unprocessed_bytes_value[SHA256_BLOCK_SIZE_B];
};

void Vale_Hash_SHA2_256_init(uint32_t *state) {
  struct KrmlWorkaround *k = (struct KrmlWorkaround *) state;
  k->ctx_value.H = k->H_value;
  k->ctx_value.unprocessed_bytes = k->unprocessed_bytes_value;
  k->ctx_value.num_unprocessed_bytes = (uint32_t)0U;
  k->ctx_value.num_total_bytes = (uint64_t)0U;

  sha256_main_i_SHA256_Init(&k->ctx_value);
}

void Vale_Hash_SHA2_256_update(uint32_t *state, uint8_t *data) {
  sha256_main_i_SHA256_Update((sha256_main_i_SHA256Context *) state,
    data, 0, SHA256_BLOCK_SIZE_B);
}

void Vale_Hash_SHA2_256_update_last(uint32_t *state, uint8_t *data, uint32_t len) {
  sha256_main_i_SHA256_Update((sha256_main_i_SHA256Context *) state,
    data, 0, (uint64_t) len);
}

void Vale_Hash_SHA2_256_finish(uint32_t *state, uint8_t *dst) {
  sha256_main_i_SHA256_Final((sha256_main_i_SHA256Context *) state,
    (uint32_t *) dst);
}
