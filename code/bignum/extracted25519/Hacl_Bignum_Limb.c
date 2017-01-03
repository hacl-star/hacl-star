#include "Hacl_Bignum_Limb.h"

Prims_int Hacl_Bignum_Limb_n;

Prims_int Hacl_Bignum_Limb_v(uint64_t x)
{
  return (Prims_int )(uint8_t )0;
}

uint64_t Hacl_Bignum_Limb_add(uint64_t a, uint64_t b)
{
  return a + b;
}

uint64_t Hacl_Bignum_Limb_add_mod(uint64_t a, uint64_t b)
{
  return a + b;
}

uint64_t Hacl_Bignum_Limb_sub(uint64_t a, uint64_t b)
{
  return a - b;
}

uint64_t Hacl_Bignum_Limb_sub_mod(uint64_t a, uint64_t b)
{
  return a - b;
}

uint64_t Hacl_Bignum_Limb_mul(uint64_t a, uint64_t b)
{
  return a * b;
}

uint64_t Hacl_Bignum_Limb_mul_mod(uint64_t a, uint64_t b)
{
  return a * b;
}

uint64_t Hacl_Bignum_Limb_logand(uint64_t a, uint64_t b)
{
  return a & b;
}

uint64_t Hacl_Bignum_Limb_logxor(uint64_t a, uint64_t b)
{
  return a ^ b;
}

uint64_t Hacl_Bignum_Limb_logor(uint64_t a, uint64_t b)
{
  return a | b;
}

uint64_t Hacl_Bignum_Limb_lognot(uint64_t a)
{
  return ~a;
}

uint64_t Hacl_Bignum_Limb_shift_right(uint64_t a, uint32_t s)
{
  return a >> s;
}

uint64_t Hacl_Bignum_Limb_shift_left(uint64_t a, uint32_t s)
{
  return a << s;
}

uint64_t Hacl_Bignum_Limb_eq_mask(uint64_t a, uint64_t b)
{
  return FStar_UInt64_eq_mask(a, b);
}

uint64_t Hacl_Bignum_Limb_gte_mask(uint64_t a, uint64_t b)
{
  return FStar_UInt64_gte_mask(a, b);
}

uint64_t Hacl_Bignum_Limb_gt_mask(uint64_t a, uint64_t b)
{
  return ~FStar_UInt64_gte_mask(b, a);
}

uint64_t Hacl_Bignum_Limb_lt_mask(uint64_t a, uint64_t b)
{
  return ~FStar_UInt64_gte_mask(a, b);
}

uint64_t Hacl_Bignum_Limb_lte_mask(uint64_t a, uint64_t b)
{
  return ~~FStar_UInt64_gte_mask(b, a);
}

uint64_t Hacl_Bignum_Limb_op_Plus_Hat(uint64_t a, uint64_t b)
{
  return a + b;
}

uint64_t Hacl_Bignum_Limb_op_Plus_Percent_Hat(uint64_t a, uint64_t b)
{
  return a + b;
}

uint64_t Hacl_Bignum_Limb_op_Subtraction_Hat(uint64_t a, uint64_t b)
{
  return a - b;
}

uint64_t Hacl_Bignum_Limb_op_Subtraction_Percent_Hat(uint64_t a, uint64_t b)
{
  return a - b;
}

uint64_t Hacl_Bignum_Limb_op_Star_Hat(uint64_t a, uint64_t b)
{
  return a * b;
}

uint64_t Hacl_Bignum_Limb_op_Star_Percent_Hat(uint64_t a, uint64_t b)
{
  return a * b;
}

uint64_t Hacl_Bignum_Limb_op_Amp_Hat(uint64_t a, uint64_t b)
{
  return a & b;
}

uint64_t Hacl_Bignum_Limb_op_Hat_Hat(uint64_t a, uint64_t b)
{
  return a ^ b;
}

uint64_t Hacl_Bignum_Limb_op_Bar_Hat(uint64_t a, uint64_t b)
{
  return a | b;
}

uint64_t Hacl_Bignum_Limb_op_Greater_Greater_Hat(uint64_t a, uint32_t s)
{
  return a >> s;
}

uint64_t Hacl_Bignum_Limb_op_Less_Less_Hat(uint64_t a, uint32_t s)
{
  return a << s;
}

