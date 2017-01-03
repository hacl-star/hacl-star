#include "Hacl_Bignum_Parameters.h"

Prims_int Hacl_Bignum_Parameters_prime;

Prims_int Hacl_Bignum_Parameters_word_size;

Prims_int Hacl_Bignum_Parameters_len;

uint32_t Hacl_Bignum_Parameters_clen = (uint32_t )5;

uint32_t Hacl_Bignum_Parameters_climb_size = (uint32_t )51;

void Hacl_Bignum_Parameters_lemma_prime_limb_size()
{
  return;
}

Prims_int Hacl_Bignum_Parameters_limb_n;

Prims_int Hacl_Bignum_Parameters_v(uint64_t x)
{
  return (Prims_int )(uint8_t )0;
}

void Hacl_Bignum_Parameters_lemma_limb_injectivity(uint64_t a, uint64_t b)
{
  return;
}

uint64_t Hacl_Bignum_Parameters_limb_zero = (uint64_t )0;

uint64_t Hacl_Bignum_Parameters_limb_one = (uint64_t )1;

uint64_t Hacl_Bignum_Parameters_limb_add(uint64_t a, uint64_t b)
{
  return a + b;
}

uint64_t Hacl_Bignum_Parameters_limb_add_mod(uint64_t a, uint64_t b)
{
  return a + b;
}

uint64_t Hacl_Bignum_Parameters_limb_sub(uint64_t a, uint64_t b)
{
  return a - b;
}

uint64_t Hacl_Bignum_Parameters_limb_sub_mod(uint64_t a, uint64_t b)
{
  return a - b;
}

uint64_t Hacl_Bignum_Parameters_limb_mul(uint64_t a, uint64_t b)
{
  return a * b;
}

uint64_t Hacl_Bignum_Parameters_limb_mul_mod(uint64_t a, uint64_t b)
{
  return a * b;
}

uint64_t Hacl_Bignum_Parameters_limb_logand(uint64_t a, uint64_t b)
{
  return a & b;
}

uint64_t Hacl_Bignum_Parameters_limb_logxor(uint64_t a, uint64_t b)
{
  return a ^ b;
}

uint64_t Hacl_Bignum_Parameters_limb_logor(uint64_t a, uint64_t b)
{
  return a | b;
}

uint64_t Hacl_Bignum_Parameters_limb_lognot(uint64_t a)
{
  return ~a;
}

uint64_t Hacl_Bignum_Parameters_limb_shift_right(uint64_t a, uint32_t s)
{
  return a >> s;
}

uint64_t Hacl_Bignum_Parameters_limb_shift_left(uint64_t a, uint32_t s)
{
  return a << s;
}

uint64_t Hacl_Bignum_Parameters_limb_eq_mask(uint64_t a, uint64_t b)
{
  return FStar_UInt64_eq_mask(a, b);
}

uint64_t Hacl_Bignum_Parameters_limb_gte_mask(uint64_t a, uint64_t b)
{
  return FStar_UInt64_gte_mask(a, b);
}

uint64_t Hacl_Bignum_Parameters_limb_gt_mask(uint64_t a, uint64_t b)
{
  return ~FStar_UInt64_gte_mask(b, a);
}

uint64_t Hacl_Bignum_Parameters_limb_lt_mask(uint64_t a, uint64_t b)
{
  return ~FStar_UInt64_gte_mask(a, b);
}

uint64_t Hacl_Bignum_Parameters_limb_lte_mask(uint64_t a, uint64_t b)
{
  return ~~FStar_UInt64_gte_mask(b, a);
}

uint8_t Hacl_Bignum_Parameters_limb_to_byte(uint64_t x)
{
  return (uint8_t )x;
}

uint64_t Hacl_Bignum_Parameters_byte_to_limb(uint8_t x)
{
  return (uint64_t )x;
}

Prims_int Hacl_Bignum_Parameters_wide_n;

Prims_int Hacl_Bignum_Parameters_w(FStar_UInt128_t x)
{
  return (Prims_int )(uint8_t )0;
}

void Hacl_Bignum_Parameters_lemma_wide_injectivity(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return;
}

FStar_UInt128_t
Hacl_Bignum_Parameters_wide_zero = FStar_Int_Cast_uint64_to_uint128((uint64_t )0);

FStar_UInt128_t
Hacl_Bignum_Parameters_wide_one = FStar_Int_Cast_uint64_to_uint128((uint64_t )1);

FStar_UInt128_t Hacl_Bignum_Parameters_wide_add(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_add(a, b);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_add_mod(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_add_mod(a, b);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_sub(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_sub(a, b);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_sub_mod(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_sub_mod(a, b);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_logand(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logand(a, b);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_logxor(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logxor(a, b);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_logor(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logor(a, b);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_lognot(FStar_UInt128_t a)
{
  return FStar_UInt128_lognot(a);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_shift_right(FStar_UInt128_t a, uint32_t s)
{
  return FStar_UInt128_shift_right(a, s);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_shift_left(FStar_UInt128_t a, uint32_t s)
{
  return FStar_UInt128_shift_left(a, s);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_eq_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_eq_mask(a, b);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_gte_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_gte_mask(a, b);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_gt_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_lognot(FStar_UInt128_gte_mask(b, a));
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_lt_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_lognot(FStar_UInt128_gte_mask(a, b));
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_lte_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_lognot(FStar_UInt128_lognot(FStar_UInt128_gte_mask(b, a)));
}

FStar_UInt128_t Hacl_Bignum_Parameters_mul_wide(uint64_t x, uint64_t y)
{
  return FStar_UInt128_mul_wide(x, y);
}

FStar_UInt128_t Hacl_Bignum_Parameters_limb_to_wide(uint64_t x)
{
  return FStar_Int_Cast_uint64_to_uint128(x);
}

uint64_t Hacl_Bignum_Parameters_wide_to_limb(FStar_UInt128_t x)
{
  return FStar_Int_Cast_uint128_to_uint64(x);
}

uint64_t Hacl_Bignum_Parameters_uint64_to_limb(uint64_t x)
{
  return x;
}

