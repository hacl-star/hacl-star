#include "Hacl_UInt16.h"

Prims_int Hacl_UInt16_n;

Prims_int Hacl_UInt16_v(uint16_t x)
{
  return (Prims_int )(uint8_t )0;
}

uint16_t Hacl_UInt16_add(uint16_t a, uint16_t b)
{
  return a + b;
}

uint16_t Hacl_UInt16_add_mod(uint16_t a, uint16_t b)
{
  return a + b;
}

uint16_t Hacl_UInt16_sub(uint16_t a, uint16_t b)
{
  return a - b;
}

uint16_t Hacl_UInt16_sub_mod(uint16_t a, uint16_t b)
{
  return a - b;
}

uint16_t Hacl_UInt16_mul(uint16_t a, uint16_t b)
{
  return a * b;
}

uint16_t Hacl_UInt16_mul_mod(uint16_t a, uint16_t b)
{
  return a * b;
}

uint16_t Hacl_UInt16_logand(uint16_t a, uint16_t b)
{
  return a & b;
}

uint16_t Hacl_UInt16_logxor(uint16_t a, uint16_t b)
{
  return a ^ b;
}

uint16_t Hacl_UInt16_logor(uint16_t a, uint16_t b)
{
  return a | b;
}

uint16_t Hacl_UInt16_lognot(uint16_t a)
{
  return ~a;
}

uint16_t Hacl_UInt16_shift_right(uint16_t a, uint32_t s)
{
  return a >> s;
}

uint16_t Hacl_UInt16_shift_left(uint16_t a, uint32_t s)
{
  return a << s;
}

uint16_t Hacl_UInt16_eq_mask(uint16_t a, uint16_t b)
{
  return FStar_UInt16_eq_mask(a, b);
}

uint16_t Hacl_UInt16_gte_mask(uint16_t a, uint16_t b)
{
  return FStar_UInt16_gte_mask(a, b);
}

uint16_t Hacl_UInt16_gt_mask(uint16_t a, uint16_t b)
{
  return ~FStar_UInt16_gte_mask(b, a);
}

uint16_t Hacl_UInt16_lt_mask(uint16_t a, uint16_t b)
{
  return ~FStar_UInt16_gte_mask(a, b);
}

uint16_t Hacl_UInt16_lte_mask(uint16_t a, uint16_t b)
{
  return ~~FStar_UInt16_gte_mask(b, a);
}

uint16_t Hacl_UInt16_op_Plus_Hat(uint16_t a, uint16_t b)
{
  return a + b;
}

uint16_t Hacl_UInt16_op_Plus_Percent_Hat(uint16_t a, uint16_t b)
{
  return a + b;
}

uint16_t Hacl_UInt16_op_Subtraction_Hat(uint16_t a, uint16_t b)
{
  return a - b;
}

uint16_t Hacl_UInt16_op_Subtraction_Percent_Hat(uint16_t a, uint16_t b)
{
  return a - b;
}

uint16_t Hacl_UInt16_op_Star_Hat(uint16_t a, uint16_t b)
{
  return a * b;
}

uint16_t Hacl_UInt16_op_Star_Percent_Hat(uint16_t a, uint16_t b)
{
  return a * b;
}

uint16_t Hacl_UInt16_op_Amp_Hat(uint16_t a, uint16_t b)
{
  return a & b;
}

uint16_t Hacl_UInt16_op_Hat_Hat(uint16_t a, uint16_t b)
{
  return a ^ b;
}

uint16_t Hacl_UInt16_op_Bar_Hat(uint16_t a, uint16_t b)
{
  return a | b;
}

uint16_t Hacl_UInt16_op_Greater_Greater_Hat(uint16_t a, uint32_t s)
{
  return a >> s;
}

uint16_t Hacl_UInt16_op_Less_Less_Hat(uint16_t a, uint32_t s)
{
  return a << s;
}

