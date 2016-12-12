#include "Hacl_Bignum_Fscalar.h"

void Hacl_Bignum_Fscalar_fscalar_(FStar_UInt128_t *output, uint64_t *b, uint64_t s, uint32_t i)
{
  if (i == (uint32_t )0)
    return;
  else
  {
    uint32_t i0 = i - (uint32_t )1;
    uint64_t bi = b[i0];
    output[i0] = FStar_UInt128_mul_wide(bi, s);
    Hacl_Bignum_Fscalar_fscalar_(output, b, s, i0);
    return;
  }
}

void Hacl_Bignum_Fscalar_fscalar(FStar_UInt128_t *output, uint64_t *b, uint64_t s)
{
  Hacl_Bignum_Fscalar_fscalar_(output, b, s, (uint32_t )5);
  return;
}

