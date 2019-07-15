#include "Hacl_Hash_SHA2.h"

void Hacl_Hash_SHA2_hash_512(uint8_t *m, uint32_t len, uint8_t *mHash)
{
  Hacl_SHA2_512_hash(mHash, m, len);
}
