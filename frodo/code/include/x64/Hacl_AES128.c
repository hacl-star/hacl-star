#include <inttypes.h>
#include "Hacl_AesNI.h"

void Hacl_AES128_aes128_key_expansion(uint8_t *key, uint8_t *expanded_key)
{
  Hacl_AesNI_aes128_key_expansion(key, expanded_key);
}

void Hacl_AES128_aes128_encrypt_block(uint16_t *output, uint8_t *input, uint8_t *expanded_key)
{
  Hacl_AesNI_aes128_encrypt_block((uint8_t*)output, (uint8_t*)input, expanded_key);
}
