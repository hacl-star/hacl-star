#include "sha256_main_i.h"

int main()
{
  uint8_t  plaintext[3U] = { (uint8_t)0x61U, (uint8_t)0x62U, (uint8_t)0x63U };
  uint32_t plaintext_len = (uint32_t)3U;

  uint32_t output[8];
  uint32_t output_len = (uint32_t)32U;

  /*
  // This is equivalent to what sha256_main_i_SHA256_Complete does:
  uint32_t h[8];
  uint8_t unprocessed[64];

  sha256_main_i_SHA256Context ctx;
  ctx.H = h;
  ctx.unprocessed_bytes = unprocessed;
  ctx.num_unprocessed_bytes = 0;
  ctx.num_total_bytes = 0;
  
  sha256_main_i_SHA256_Init(&ctx);
  sha256_main_i_SHA256_Update(&ctx, plaintext, 0, 3);
  sha256_main_i_SHA256_Final(&ctx, output);
  */
  
  sha256_main_i_SHA256_Complete(plaintext, 0, 3, output);

  /*
  // Reverse byte order of 4-byte chunks of output
  for (int i = 0; i < 8; i++) {
    uint32_t v = ((uint32_t *) output)[i];
    output[i * 4]     = v >> 24;
    output[i * 4 + 1] = v >> 16;
    output[i * 4 + 2] = v >> 8;
    output[i * 4 + 3] = v;
  }
  */

  printf("Expected digest                      : ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad\n");
   
  printf("4-byte chunks of digest as uint32_t's: ");
  for (int i = 0; i < 8; i++) {
    printf("%02x", ((uint32_t *) output)[i]);
  }
  printf("\n");

  printf("Digest byte by byte                  : ");
  for (int i = 0; i < 32; i++) {
    printf("%02x", ((uint8_t *) output)[i]);
  }
  printf("\n");

  return 0;
}

