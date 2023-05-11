#include "Hacl_Hash_SHA3.h"
#include "Hacl_Spec.h"
#include <assert.h>
#include "test_helpers.h"

const uint8_t expected_hash[] = { 0x64, 0x4b, 0xcc, 0x7e, 0x56, 0x43, 0x73,
                                  0x04, 0x09, 0x99, 0xaa, 0xc8, 0x9e, 0x76,
                                  0x22, 0xf3, 0xca, 0x71, 0xfb, 0xa1, 0xd9,
                                  0x72, 0xfd, 0x94, 0xa3, 0x1c, 0x3b, 0xfb,
                                  0xf2, 0x4e, 0x39, 0x38 };

const uint8_t expected_hash1[] = {
  0xe2, 0xd4, 0x53, 0x5e, 0x3b, 0x61, 0x31, 0x35, 0xc1, 0x4f, 0x2f, 0xe4, 0xe0,
  0x26, 0xd7, 0xad, 0x8d, 0x56, 0x9d, 0xb4, 0x49, 0x01, 0x74, 0x0b, 0xef, 0xfa,
  0x30, 0xd4, 0x30, 0xac, 0xb0, 0x38
};

int
main()
{
  Hacl_Streaming_Keccak_state* s = Hacl_Streaming_Keccak_malloc(Spec_Hash_Definitions_SHA3_256);
  uint8_t hash[32] = { 0 };

  assert(Hacl_Streaming_Keccak_update(s, (uint8_t*)"hello world", 11) == 0);
  Hacl_Streaming_Keccak_finish(s, hash);
  if (!compare_and_print(32, expected_hash, hash))
    exit(1);

  Hacl_Streaming_Keccak_reset(s);
  uint8_t *zeroes_1mb = (uint8_t*)calloc(1048576,1);
  for (int i = 0; i < 4096; ++i)
    Hacl_Streaming_Keccak_update(s, zeroes_1mb, 1048576);
  Hacl_Streaming_Keccak_update(s, "hello world", 11);
  Hacl_Streaming_Keccak_finish(s, hash);
  if (!compare_and_print(32, expected_hash1, hash))
    exit(1);

  Hacl_Streaming_Keccak_free(s);
  exit(0);
}
