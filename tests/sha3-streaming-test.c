#include "Hacl_Hash_SHA3.h"
#include "Hacl_Spec.h"
#include <assert.h>

const uint8_t expected_hash[] = { 0x64, 0x4b, 0xcc, 0x7e, 0x56, 0x43, 0x73,
                                  0x04, 0x09, 0x99, 0xaa, 0xc8, 0x9e, 0x76,
                                  0x22, 0xf3, 0xca, 0x71, 0xfb, 0xa1, 0xd9,
                                  0x72, 0xfd, 0x94, 0xa3, 0x1c, 0x3b, 0xfb,
                                  0xf2, 0x4e, 0x39, 0x38 };

int
main()
{
  Hacl_Streaming_Keccak_state* s = Hacl_Streaming_Keccak_malloc(Spec_Hash_Definitions_SHA3_256);
  assert(Hacl_Streaming_Keccak_update(s, (uint8_t*)"hello world", 11) == 0);
  uint8_t hash[32] = { 0 };
  Hacl_Streaming_Keccak_finish(s, hash);
  Hacl_Streaming_Keccak_free(s);
  for (int i = 0; i < 32; ++i) {
    if (hash[i] != expected_hash[i]) {
      printf("Hash and reference differ at index %d\n", i);
      exit(1);
    }
  }
  printf("Success!\n");
  exit(0);
}
