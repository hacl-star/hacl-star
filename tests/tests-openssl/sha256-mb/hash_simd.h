#include <stdint.h>

void sha256_4way_simd(uint8_t *input[4], uint16_t input_len, uint8_t *digest[4]);

void sha256_8way_simd(uint8_t *input[8], uint16_t input_len, uint8_t *digest[8]);
