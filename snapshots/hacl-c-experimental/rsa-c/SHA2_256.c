#include "SHA2_256.h"

uint32_t SHA2_256_size_hash = (uint32_t )32;

uint32_t SHA2_256_size_block = (uint32_t )64;

uint32_t SHA2_256_size_state = (uint32_t )137;

void SHA2_256_init(uint32_t *state)
{
  Hacl_Hash_SHA2_256_init(state);
}

void SHA2_256_update(uint32_t *state, uint8_t *data_8)
{
  Hacl_Hash_SHA2_256_update(state, data_8);
}

void SHA2_256_update_multi(uint32_t *state, uint8_t *data, uint32_t n1)
{
  Hacl_Hash_SHA2_256_update_multi(state, data, n1);
}

void SHA2_256_update_last(uint32_t *state, uint8_t *data, uint32_t len)
{
  Hacl_Hash_SHA2_256_update_last(state, data, len);
}

void SHA2_256_finish(uint32_t *state, uint8_t *hash1)
{
  Hacl_Hash_SHA2_256_finish(state, hash1);
}

void SHA2_256_hash(uint8_t *hash1, uint8_t *input, uint32_t len)
{
  Hacl_Hash_SHA2_256_hash(hash1, input, len);
}

