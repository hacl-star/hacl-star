#include "Hacl_Bignum.h"

void Hacl_Bignum_fsum(uint64_t *a, uint64_t *b)
{
  Hacl_Bignum_Fsum_fsum_(a, b, (uint32_t )5);
  return;
}

void Hacl_Bignum_fdifference(uint64_t *a, uint64_t *b)
{
  uint64_t tmp[5] = { 0 };
  memcpy(tmp, b, (uint32_t )5 * sizeof b[0]);
  Hacl_Bignum_Modulo_add_zero(tmp);
  Hacl_Bignum_Fdifference_fdifference_(a, tmp, (uint32_t )5);
}

void Hacl_Bignum_fscalar(uint64_t *output, uint64_t *b, uint64_t s)
{
  FStar_UInt128_t tmp[5];
  for (uintmax_t i = 0; i < (uint32_t )5; ++i)
    tmp[i] = FStar_Int_Cast_uint64_to_uint128((uint64_t )0);
  Hacl_Bignum_Fscalar_fscalar(tmp, b, s);
  Hacl_Bignum_Fproduct_carry_wide_(tmp, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top_wide(tmp);
  Hacl_Bignum_Fproduct_copy_from_wide_(output, tmp, (uint32_t )5);
}

void Hacl_Bignum_fmul(uint64_t *output, uint64_t *a, uint64_t *b)
{
  Hacl_Bignum_Fproduct_fmul(output, a, b);
  return;
}

void Hacl_Bignum_fsquare_times(uint64_t *output, uint64_t *input, uint32_t count)
{
  Hacl_Bignum_Fproduct_fsquare_times(output, input, count);
  return;
}

void Hacl_Bignum_crecip(uint64_t *output, uint64_t *input)
{
  Hacl_Bignum_Crecip_crecip(output, input);
  return;
}

