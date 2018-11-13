#include "Hacl_SHA2_256.h"

void Hacl_SHA256_hash(uint8_t *mHash, uint32_t len, uint8_t *m)
{
  Hacl_SHA2_256_hash(mHash, m, len);
}
