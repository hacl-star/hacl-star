#include "Hacl_UInt128.h"

Prims_int Hacl_UInt128_n;

Prims_int Hacl_UInt128_v(FStar_UInt128_t x)
{
  return (Prims_int )(uint8_t )0;
}

FStar_UInt128_t Hacl_UInt128_add(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_add(a, b);
}

FStar_UInt128_t Hacl_UInt128_add_mod(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_add_mod(a, b);
}

FStar_UInt128_t Hacl_UInt128_sub(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_sub(a, b);
}

FStar_UInt128_t Hacl_UInt128_sub_mod(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_sub_mod(a, b);
}

FStar_UInt128_t Hacl_UInt128_logand(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logand(a, b);
}

FStar_UInt128_t Hacl_UInt128_logxor(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logxor(a, b);
}

FStar_UInt128_t Hacl_UInt128_logor(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logor(a, b);
}

FStar_UInt128_t Hacl_UInt128_lognot(FStar_UInt128_t a)
{
  return FStar_UInt128_lognot(a);
}

FStar_UInt128_t Hacl_UInt128_shift_right(FStar_UInt128_t a, uint32_t s)
{
  return FStar_UInt128_shift_right(a, s);
}

FStar_UInt128_t Hacl_UInt128_shift_left(FStar_UInt128_t a, uint32_t s)
{
  return FStar_UInt128_shift_left(a, s);
}

FStar_UInt128_t Hacl_UInt128_eq_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_eq_mask(a, b);
}

FStar_UInt128_t Hacl_UInt128_gte_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_gte_mask(a, b);
}

FStar_UInt128_t Hacl_UInt128_gt_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_lognot(FStar_UInt128_gte_mask(b, a));
}

FStar_UInt128_t Hacl_UInt128_lt_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_lognot(FStar_UInt128_gte_mask(a, b));
}

FStar_UInt128_t Hacl_UInt128_lte_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_lognot(FStar_UInt128_lognot(FStar_UInt128_gte_mask(b, a)));
}

FStar_UInt128_t Hacl_UInt128_op_Plus_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_add(a, b);
}

FStar_UInt128_t Hacl_UInt128_op_Plus_Percent_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_add_mod(a, b);
}

FStar_UInt128_t Hacl_UInt128_op_Subtraction_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_sub(a, b);
}

FStar_UInt128_t Hacl_UInt128_op_Subtraction_Percent_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_sub_mod(a, b);
}

FStar_UInt128_t Hacl_UInt128_op_Amp_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logand(a, b);
}

FStar_UInt128_t Hacl_UInt128_op_Hat_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logxor(a, b);
}

FStar_UInt128_t Hacl_UInt128_op_Bar_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logor(a, b);
}

FStar_UInt128_t Hacl_UInt128_op_Greater_Greater_Hat(FStar_UInt128_t a, uint32_t s)
{
  return FStar_UInt128_shift_right(a, s);
}

FStar_UInt128_t Hacl_UInt128_op_Less_Less_Hat(FStar_UInt128_t a, uint32_t s)
{
  return FStar_UInt128_shift_left(a, s);
}

FStar_UInt128_t Hacl_UInt128_mul_wide(uint64_t a, uint64_t b)
{
  return FStar_UInt128_mul_wide(a, b);
}

FStar_UInt128_t Hacl_UInt128_op_Star_Hat(uint64_t a, uint64_t b)
{
  return FStar_UInt128_mul_wide(a, b);
}

