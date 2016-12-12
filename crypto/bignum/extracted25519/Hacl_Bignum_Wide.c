#include "Hacl_Bignum_Wide.h"

Prims_int Hacl_Bignum_Wide_n;

Prims_int Hacl_Bignum_Wide_v(FStar_UInt128_t x)
{
  return (Prims_int )(uint8_t )0;
}

FStar_UInt128_t Hacl_Bignum_Wide_add(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_add(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_add_mod(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_add_mod(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_sub(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_sub(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_sub_mod(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_sub_mod(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_logand(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logand(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_logxor(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logxor(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_logor(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logor(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_lognot(FStar_UInt128_t a)
{
  return FStar_UInt128_lognot(a);
}

FStar_UInt128_t Hacl_Bignum_Wide_shift_right(FStar_UInt128_t a, uint32_t s)
{
  return FStar_UInt128_shift_right(a, s);
}

FStar_UInt128_t Hacl_Bignum_Wide_shift_left(FStar_UInt128_t a, uint32_t s)
{
  return FStar_UInt128_shift_left(a, s);
}

FStar_UInt128_t Hacl_Bignum_Wide_eq_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_eq_mask(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_gte_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_gte_mask(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_gt_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_lognot(FStar_UInt128_gte_mask(b, a));
}

FStar_UInt128_t Hacl_Bignum_Wide_lt_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_lognot(FStar_UInt128_gte_mask(a, b));
}

FStar_UInt128_t Hacl_Bignum_Wide_lte_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_lognot(FStar_UInt128_lognot(FStar_UInt128_gte_mask(b, a)));
}

FStar_UInt128_t Hacl_Bignum_Wide_op_Plus_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_add(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_op_Plus_Percent_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_add_mod(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_op_Subtraction_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_sub(a, b);
}

FStar_UInt128_t
Hacl_Bignum_Wide_op_Subtraction_Percent_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_sub_mod(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_op_Amp_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logand(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_op_Hat_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logxor(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_op_Bar_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logor(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_op_Greater_Greater_Hat(FStar_UInt128_t a, uint32_t s)
{
  return FStar_UInt128_shift_right(a, s);
}

FStar_UInt128_t Hacl_Bignum_Wide_op_Less_Less_Hat(FStar_UInt128_t a, uint32_t s)
{
  return FStar_UInt128_shift_left(a, s);
}

FStar_UInt128_t Hacl_Bignum_Wide_mul_wide(uint64_t a, uint64_t b)
{
  return FStar_UInt128_mul_wide(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_op_Star_Hat(uint64_t a, uint64_t b)
{
  return FStar_UInt128_mul_wide(a, b);
}

