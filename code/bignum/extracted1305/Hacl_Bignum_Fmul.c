#include "Hacl_Bignum_Fmul.h"

void Hacl_Bignum_Fmul_fmul_(uint64_t *output, uint64_t *input, uint64_t *input2)
{
  FStar_UInt128_t t[3];
  for (uintmax_t i = 0; i < (uint32_t )3; ++i)
    t[i] = FStar_Int_Cast_uint64_to_uint128((uint64_t )0);
  Hacl_Bignum_Fproduct_mul_shift_reduce_(t, input, input2, (uint32_t )3);
  Hacl_Bignum_Fproduct_carry_wide_(t, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top_wide(t);
  Hacl_Bignum_Fproduct_copy_from_wide_(output, t, (uint32_t )3);
  Hacl_Bignum_Fproduct_carry_0_to_1(output);
}

void Hacl_Bignum_Fmul_fmul(uint64_t *output, uint64_t *input, uint64_t *input2)
{
  uint64_t tmp[3] = { 0 };
  memcpy(tmp, input, (uint32_t )3 * sizeof input[0]);
  Hacl_Bignum_Fmul_fmul_(output, tmp, input2);
}

void Hacl_Bignum_Fmul_fsquare_times_(uint64_t *tmp, uint32_t count)
{
  if (count == (uint32_t )0)
    return;
  else
  {
    Hacl_Bignum_Fmul_fmul(tmp, tmp, tmp);
    Hacl_Bignum_Fmul_fsquare_times_(tmp, count - (uint32_t )1);
    return;
  }
}

void Hacl_Bignum_Fmul_fsquare_times(uint64_t *output, uint64_t *input, uint32_t count)
{
  uint64_t tmp[3] = { 0 };
  memcpy(tmp, input, (uint32_t )3 * sizeof input[0]);
  Hacl_Bignum_Fmul_fsquare_times_(tmp, count);
  memcpy(output, tmp, (uint32_t )3 * sizeof tmp[0]);
}

