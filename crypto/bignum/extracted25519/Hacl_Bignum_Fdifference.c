#include "Hacl_Bignum_Fdifference.h"

void Hacl_Bignum_Fdifference_fdifference_(uint64_t *a, uint64_t *b, uint32_t i)
{
  if (i == (uint32_t )0)
    return;
  else
  {
    uint32_t i0 = i - (uint32_t )1;
    uint64_t ai = a[i0];
    uint64_t bi = b[i0];
    a[i0] = bi - ai;
    Hacl_Bignum_Fdifference_fdifference_(a, b, i0);
    return;
  }
}

