#include <inttypes.h>
#include "aes.h"

void Vale_AES128_aes128_key_expansion(uint8_t *key, uint8_t *expanded_key)
{
  KeyExpansionStdcall(key, expanded_key);
}

void Vale_AES128_aes128_encrypt_block(uint16_t *output, uint8_t *input, uint8_t *expanded_key)
{
  AES128EncryptOneBlockStdcall((uint8_t*)output, (uint8_t*)input, expanded_key);
}
