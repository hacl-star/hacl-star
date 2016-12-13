#include "Hacl_Bignum_Modulo.h"

uint64_t Hacl_Bignum_Modulo_mask_2_44 = (uint64_t )0xfffffffffff;

uint64_t Hacl_Bignum_Modulo_mask_2_42 = (uint64_t )0x3ffffffffff;

uint64_t Hacl_Bignum_Modulo_five = (uint64_t )5;

void Hacl_Bignum_Modulo_add_zero(uint64_t *b)
{
  return;
}

void Hacl_Bignum_Modulo_carry_top(uint64_t *b)
{
  return;
}

bool Hacl_Bignum_Modulo_reduce_pre(void *s)
{
  return (bool )(uint8_t )0;
}

void *Hacl_Bignum_Modulo_reduce_spec(void *s)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void Hacl_Bignum_Modulo_reduce(uint64_t *b)
{
  uint64_t b0 = b[(uint32_t )0];
  b[(uint32_t )0] = ((uint64_t )5 << (uint32_t )2) * b0;
}

void *Hacl_Bignum_Modulo_carry_top_wide_spec(void *s)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void Hacl_Bignum_Modulo_carry_top_wide(FStar_UInt128_t *b)
{
  FStar_UInt128_t b2 = b[(uint32_t )2];
  FStar_UInt128_t b0 = b[(uint32_t )0];
  FStar_UInt128_t
  mask =
    FStar_UInt128_sub(FStar_UInt128_shift_left(FStar_Int_Cast_uint64_to_uint128((uint64_t )1),
        (uint32_t )42),
      FStar_Int_Cast_uint64_to_uint128((uint64_t )1));
  FStar_UInt128_t b2_ = FStar_UInt128_logand(b2, mask);
  FStar_UInt128_t
  b0_ =
    FStar_UInt128_add(b0,
      FStar_UInt128_mul_wide((uint64_t )5,
        FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_shift_right(b2, (uint32_t )42))));
  b[(uint32_t )2] = b2_;
  b[(uint32_t )0] = b0_;
}

