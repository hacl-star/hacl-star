#include "Hacl_Bignum_Fproduct.h"

void
Hacl_Bignum_Fproduct_copy_from_wide_(uint64_t *output, FStar_UInt128_t *input, uint32_t ctr)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    FStar_UInt128_t inputi = input[i];
    output[i] = FStar_Int_Cast_uint128_to_uint64(inputi);
    Hacl_Bignum_Fproduct_copy_from_wide_(output, input, i);
    return;
  }
}

void Hacl_Bignum_Fproduct_shift_(uint64_t *output, uint32_t ctr)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint64_t z = output[ctr - (uint32_t )1];
    output[ctr] = z;
    Hacl_Bignum_Fproduct_shift_(output, ctr - (uint32_t )1);
    return;
  }
}

void Hacl_Bignum_Fproduct_shift(uint64_t *output)
{
  uint64_t tmp = output[(uint32_t )4];
  Hacl_Bignum_Fproduct_shift_(output, (uint32_t )4);
  output[(uint32_t )0] = tmp;
}

void
Hacl_Bignum_Fproduct_sum_scalar_multiplication_(
  FStar_UInt128_t *output,
  uint64_t *input,
  uint64_t s,
  uint32_t ctr
)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    FStar_UInt128_t oi = output[i];
    uint64_t ii = input[i];
    output[i] = FStar_UInt128_add(oi, FStar_UInt128_mul_wide(ii, s));
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, s, i);
    return;
  }
}

void Hacl_Bignum_Fproduct_shift_reduce(uint64_t *output)
{
  Hacl_Bignum_Fproduct_shift(output);
  Hacl_Bignum_Modulo_reduce(output);
  return;
}

void
Hacl_Bignum_Fproduct_mul_shift_reduce_(
  FStar_UInt128_t *output,
  uint64_t *input,
  uint64_t *input2,
  uint32_t ctr
)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    uint32_t j = (uint32_t )4 - i;
    uint64_t input2i = input2[j];
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2i, (uint32_t )5);
    if (ctr > (uint32_t )1)
      Hacl_Bignum_Fproduct_shift_reduce(input);
    Hacl_Bignum_Fproduct_mul_shift_reduce_(output, input, input2, i);
    return;
  }
}

void Hacl_Bignum_Fproduct_carry_wide_(FStar_UInt128_t *tmp, uint32_t ctr)
{
  if (ctr == (uint32_t )4)
    return;
  else
  {
    FStar_UInt128_t tctr = tmp[ctr];
    FStar_UInt128_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint64_t
    r0 = FStar_Int_Cast_uint128_to_uint64(tctr) & ((uint64_t )1 << (uint32_t )51) - (uint64_t )1;
    FStar_UInt128_t c = FStar_UInt128_shift_right(tctr, (uint32_t )51);
    tmp[ctr] = FStar_Int_Cast_uint64_to_uint128(r0);
    tmp[ctr + (uint32_t )1] = FStar_UInt128_add(tctrp1, c);
    Hacl_Bignum_Fproduct_carry_wide_(tmp, ctr + (uint32_t )1);
    return;
  }
}

void Hacl_Bignum_Fproduct_carry_0_to_1(uint64_t *output)
{
  uint64_t i0 = output[(uint32_t )0];
  uint64_t i1 = output[(uint32_t )1];
  uint64_t i0_ = i0 & ((uint64_t )1 << (uint32_t )51) - (uint64_t )1;
  uint64_t i1_ = i1 + (i0 >> (uint32_t )51);
  output[(uint32_t )0] = i0_;
  output[(uint32_t )1] = i1_;
}

void Hacl_Bignum_Fproduct_fmul_(uint64_t *output, uint64_t *input, uint64_t *input2)
{
  FStar_UInt128_t t[5];
  for (uintmax_t i = 0; i < (uint32_t )5; ++i)
    t[i] = FStar_Int_Cast_uint64_to_uint128((uint64_t )0);
  Hacl_Bignum_Fproduct_mul_shift_reduce_(t, input, input2, (uint32_t )5);
  Hacl_Bignum_Fproduct_carry_wide_(t, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top_wide(t);
  Hacl_Bignum_Fproduct_copy_from_wide_(output, t, (uint32_t )5);
  Hacl_Bignum_Fproduct_carry_0_to_1(output);
}

void Hacl_Bignum_Fproduct_fmul(uint64_t *output, uint64_t *input, uint64_t *input2)
{
  uint64_t tmp[5] = { 0 };
  memcpy(tmp, input, (uint32_t )5 * sizeof input[0]);
  Hacl_Bignum_Fproduct_fmul_(output, tmp, input2);
}

void Hacl_Bignum_Fproduct_fsquare_times_(uint64_t *tmp, uint32_t count)
{
  if (count == (uint32_t )0)
    return;
  else
  {
    Hacl_Bignum_Fproduct_fmul(tmp, tmp, tmp);
    Hacl_Bignum_Fproduct_fsquare_times_(tmp, count - (uint32_t )1);
    return;
  }
}

void Hacl_Bignum_Fproduct_fsquare_times(uint64_t *output, uint64_t *input, uint32_t count)
{
  uint64_t tmp[5] = { 0 };
  memcpy(tmp, input, (uint32_t )5 * sizeof input[0]);
  Hacl_Bignum_Fproduct_fsquare_times_(tmp, count);
  memcpy(output, tmp, (uint32_t )5 * sizeof tmp[0]);
}

