#include "Hacl_Hash.h"

void Hacl_SHA512_hash(uint8_t *mHash, uint32_t len, uint8_t *m)
{
  Hacl_Hash_SHA2_hash_512(mHash, m, len);
}
