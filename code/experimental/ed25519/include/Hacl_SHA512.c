#include "Hacl_SHA512.h"

void Hacl_SHA512_hash(uint8_t *mHash, uint32_t len, uint8_t *m)
{
  Hacl_SHA2_512_hash(mHash, m, len);
}
