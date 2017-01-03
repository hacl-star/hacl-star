#include "Hacl_Bignum_Crecip.h"

void Hacl_Bignum_Crecip_crecip(uint64_t *out, uint64_t *z)
{
  uint64_t buf[20] = { 0 };
  uint64_t *a = buf + (uint32_t )0;
  uint64_t *t0 = buf + (uint32_t )5;
  uint64_t *b = buf + (uint32_t )10;
  uint64_t *c = buf + (uint32_t )15;
  Hacl_Bignum_Fproduct_fsquare_times(a, z, (uint32_t )1);
  Hacl_Bignum_Fproduct_fsquare_times(t0, a, (uint32_t )2);
  Hacl_Bignum_Fproduct_fmul(b, t0, z);
  Hacl_Bignum_Fproduct_fmul(a, b, a);
  Hacl_Bignum_Fproduct_fsquare_times(t0, a, (uint32_t )1);
  Hacl_Bignum_Fproduct_fmul(b, t0, b);
  Hacl_Bignum_Fproduct_fsquare_times(t0, b, (uint32_t )5);
  Hacl_Bignum_Fproduct_fmul(b, t0, b);
  Hacl_Bignum_Fproduct_fsquare_times(t0, b, (uint32_t )10);
  Hacl_Bignum_Fproduct_fmul(c, t0, b);
  Hacl_Bignum_Fproduct_fsquare_times(t0, c, (uint32_t )20);
  Hacl_Bignum_Fproduct_fmul(t0, t0, c);
  Hacl_Bignum_Fproduct_fsquare_times(t0, t0, (uint32_t )10);
  Hacl_Bignum_Fproduct_fmul(b, t0, b);
  Hacl_Bignum_Fproduct_fsquare_times(t0, b, (uint32_t )50);
  Hacl_Bignum_Fproduct_fmul(c, t0, b);
  Hacl_Bignum_Fproduct_fsquare_times(t0, c, (uint32_t )100);
  Hacl_Bignum_Fproduct_fmul(t0, t0, c);
  Hacl_Bignum_Fproduct_fsquare_times(t0, t0, (uint32_t )50);
  Hacl_Bignum_Fproduct_fmul(t0, t0, b);
  Hacl_Bignum_Fproduct_fsquare_times(t0, t0, (uint32_t )5);
  Hacl_Bignum_Fproduct_fmul(out, t0, a);
}

