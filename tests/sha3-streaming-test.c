#include "Hacl_Streaming_SHA3.h"

const uint8_t expected_hash[] = {
  0x64, 0x4b, 0xcc, 0x7e, 0x56, 0x43, 0x73, 0x04, 0x09, 0x99, 0xaa, 0xc8, 0x9e,
  0x76, 0x22, 0xf3, 0xca, 0x71, 0xfb, 0xa1, 0xd9, 0x72, 0xfd, 0x94, 0xa3, 0x1c,
  0x3b, 0xfb, 0xf2, 0x4e, 0x39, 0x38
};

int main() {
  Hacl_Streaming_SHA3_state_sha3_256 *s = Hacl_Streaming_SHA3_create_in_256();
  Hacl_Streaming_SHA3_update_256(s, (uint8_t *)"hello world", 11);
  uint8_t hash[32] = { 0 };
  Hacl_Streaming_SHA3_finish_256(s, hash);
  Hacl_Streaming_SHA3_free_256(s);
  for (int i = 0; i < 32; ++i) {
    if (hash[i] != expected_hash[i]) {
      printf("Hash and reference differ at index %d\n", i);
      exit(1);
    }
  }
  printf("Success!\n");
  exit(0);
}
