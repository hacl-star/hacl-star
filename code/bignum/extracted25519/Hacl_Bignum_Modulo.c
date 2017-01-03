#include "Hacl_Bignum_Modulo.h"

uint64_t Hacl_Bignum_Modulo_two54m152 = (uint64_t )0x3fffffffffff68;

uint64_t Hacl_Bignum_Modulo_two54m8 = (uint64_t )0x3ffffffffffff8;

uint64_t Hacl_Bignum_Modulo_nineteen = (uint64_t )19;

uint64_t Hacl_Bignum_Modulo_mask_51 = (uint64_t )0x7ffffffffffff;

void *Hacl_Bignum_Modulo_add_zero_spec(void *s)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void Hacl_Bignum_Modulo_add_zero(uint64_t *b)
{
  uint64_t b0 = b[(uint32_t )0];
  uint64_t b1 = b[(uint32_t )1];
  uint64_t b2 = b[(uint32_t )2];
  uint64_t b3 = b[(uint32_t )3];
  uint64_t b4 = b[(uint32_t )4];
  b[(uint32_t )0] = b0 + (uint64_t )0x3fffffffffff68;
  b[(uint32_t )1] = b1 + (uint64_t )0x3ffffffffffff8;
  b[(uint32_t )2] = b2 + (uint64_t )0x3ffffffffffff8;
  b[(uint32_t )3] = b3 + (uint64_t )0x3ffffffffffff8;
  b[(uint32_t )4] = b4 + (uint64_t )0x3ffffffffffff8;
}

void *Hacl_Bignum_Modulo_carry_top_spec(void *s)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void Hacl_Bignum_Modulo_carry_top(uint64_t *b)
{
  uint64_t b4 = b[(uint32_t )4];
  uint64_t b0 = b[(uint32_t )0];
  uint64_t mask = ((uint64_t )1 << (uint32_t )51) - (uint64_t )1;
  uint64_t
  nineteen = ((uint64_t )1 << (uint32_t )4) + ((uint64_t )1 << (uint32_t )1) + (uint64_t )1;
  uint64_t b4_ = b4 & mask;
  uint64_t b0_ = b0 + nineteen * (b4 >> (uint32_t )51);
  b[(uint32_t )4] = b4_;
  b[(uint32_t )0] = b0_;
}

void *Hacl_Bignum_Modulo_reduce_spec(void *s)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void Hacl_Bignum_Modulo_reduce(uint64_t *b)
{
  uint64_t
  nineteen = ((uint64_t )1 << (uint32_t )4) + ((uint64_t )1 << (uint32_t )1) + (uint64_t )1;
  uint64_t b0 = b[(uint32_t )0];
  b[(uint32_t )0] = nineteen * b0;
}

void *Hacl_Bignum_Modulo_carry_top_wide_spec(void *s)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void Hacl_Bignum_Modulo_carry_top_wide(FStar_UInt128_t *b)
{
  FStar_UInt128_t b4 = b[(uint32_t )4];
  FStar_UInt128_t b0 = b[(uint32_t )0];
  uint64_t
  nineteen = ((uint64_t )1 << (uint32_t )4) + ((uint64_t )1 << (uint32_t )1) + (uint64_t )1;
  FStar_UInt128_t
  mask =
    FStar_UInt128_sub(FStar_UInt128_shift_left(FStar_Int_Cast_uint64_to_uint128((uint64_t )1),
        (uint32_t )51),
      FStar_Int_Cast_uint64_to_uint128((uint64_t )1));
  FStar_UInt128_t b4_ = FStar_UInt128_logand(b4, mask);
  FStar_UInt128_t
  b0_ =
    FStar_UInt128_add(b0,
      FStar_UInt128_mul_wide(nineteen,
        FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_shift_right(b4, (uint32_t )51))));
  b[(uint32_t )4] = b4_;
  b[(uint32_t )0] = b0_;
}

