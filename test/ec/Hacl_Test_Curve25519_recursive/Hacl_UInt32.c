#include "Hacl_UInt32.h"

Prims_int Hacl_UInt32_n;

Prims_int Hacl_UInt32_v(uint32_t x)
{
  return (Prims_int )(uint8_t )0;
}

uint32_t Hacl_UInt32_add(uint32_t a, uint32_t b)
{
  return a + b;
}

uint32_t Hacl_UInt32_add_mod(uint32_t a, uint32_t b)
{
  return a + b;
}

uint32_t Hacl_UInt32_sub(uint32_t a, uint32_t b)
{
  return a - b;
}

uint32_t Hacl_UInt32_sub_mod(uint32_t a, uint32_t b)
{
  return a - b;
}

uint32_t Hacl_UInt32_mul(uint32_t a, uint32_t b)
{
  return a * b;
}

uint32_t Hacl_UInt32_mul_mod(uint32_t a, uint32_t b)
{
  return a * b;
}

uint32_t Hacl_UInt32_logand(uint32_t a, uint32_t b)
{
  return a & b;
}

uint32_t Hacl_UInt32_logxor(uint32_t a, uint32_t b)
{
  return a ^ b;
}

uint32_t Hacl_UInt32_logor(uint32_t a, uint32_t b)
{
  return a | b;
}

uint32_t Hacl_UInt32_lognot(uint32_t a)
{
  return ~a;
}

uint32_t Hacl_UInt32_shift_right(uint32_t a, uint32_t s)
{
  return a >> s;
}

uint32_t Hacl_UInt32_shift_left(uint32_t a, uint32_t s)
{
  return a << s;
}

uint32_t Hacl_UInt32_eq_mask(uint32_t a, uint32_t b)
{
  return FStar_UInt32_eq_mask(a, b);
}

uint32_t Hacl_UInt32_gte_mask(uint32_t a, uint32_t b)
{
  return FStar_UInt32_gte_mask(a, b);
}

uint32_t Hacl_UInt32_gt_mask(uint32_t a, uint32_t b)
{
  return ~FStar_UInt32_gte_mask(b, a);
}

uint32_t Hacl_UInt32_lt_mask(uint32_t a, uint32_t b)
{
  return ~FStar_UInt32_gte_mask(a, b);
}

uint32_t Hacl_UInt32_lte_mask(uint32_t a, uint32_t b)
{
  return ~~FStar_UInt32_gte_mask(b, a);
}

uint32_t Hacl_UInt32_op_Plus_Hat(uint32_t a, uint32_t b)
{
  return a + b;
}

uint32_t Hacl_UInt32_op_Plus_Percent_Hat(uint32_t a, uint32_t b)
{
  return a + b;
}

uint32_t Hacl_UInt32_op_Subtraction_Hat(uint32_t a, uint32_t b)
{
  return a - b;
}

uint32_t Hacl_UInt32_op_Subtraction_Percent_Hat(uint32_t a, uint32_t b)
{
  return a - b;
}

uint32_t Hacl_UInt32_op_Star_Hat(uint32_t a, uint32_t b)
{
  return a * b;
}

uint32_t Hacl_UInt32_op_Star_Percent_Hat(uint32_t a, uint32_t b)
{
  return a * b;
}

uint32_t Hacl_UInt32_op_Amp_Hat(uint32_t a, uint32_t b)
{
  return a & b;
}

uint32_t Hacl_UInt32_op_Hat_Hat(uint32_t a, uint32_t b)
{
  return a ^ b;
}

uint32_t Hacl_UInt32_op_Bar_Hat(uint32_t a, uint32_t b)
{
  return a | b;
}

uint32_t Hacl_UInt32_op_Greater_Greater_Hat(uint32_t a, uint32_t s)
{
  return a >> s;
}

uint32_t Hacl_UInt32_op_Less_Less_Hat(uint32_t a, uint32_t s)
{
  return a << s;
}

