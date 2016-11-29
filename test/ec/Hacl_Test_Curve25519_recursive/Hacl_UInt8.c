#include "Hacl_UInt8.h"

Prims_int Hacl_UInt8_n;

Prims_int Hacl_UInt8_v(uint8_t x)
{
  return (Prims_int )(uint8_t )0;
}

uint8_t Hacl_UInt8_add(uint8_t a, uint8_t b)
{
  return a + b;
}

uint8_t Hacl_UInt8_add_mod(uint8_t a, uint8_t b)
{
  return a + b;
}

uint8_t Hacl_UInt8_sub(uint8_t a, uint8_t b)
{
  return a - b;
}

uint8_t Hacl_UInt8_sub_mod(uint8_t a, uint8_t b)
{
  return a - b;
}

uint8_t Hacl_UInt8_mul(uint8_t a, uint8_t b)
{
  return a * b;
}

uint8_t Hacl_UInt8_mul_mod(uint8_t a, uint8_t b)
{
  return a * b;
}

uint8_t Hacl_UInt8_logand(uint8_t a, uint8_t b)
{
  return a & b;
}

uint8_t Hacl_UInt8_logxor(uint8_t a, uint8_t b)
{
  return a ^ b;
}

uint8_t Hacl_UInt8_logor(uint8_t a, uint8_t b)
{
  return a | b;
}

uint8_t Hacl_UInt8_lognot(uint8_t a)
{
  return ~a;
}

uint8_t Hacl_UInt8_shift_right(uint8_t a, uint32_t s)
{
  return a >> s;
}

uint8_t Hacl_UInt8_shift_left(uint8_t a, uint32_t s)
{
  return a << s;
}

uint8_t Hacl_UInt8_eq_mask(uint8_t a, uint8_t b)
{
  return FStar_UInt8_eq_mask(a, b);
}

uint8_t Hacl_UInt8_gte_mask(uint8_t a, uint8_t b)
{
  return FStar_UInt8_gte_mask(a, b);
}

uint8_t Hacl_UInt8_gt_mask(uint8_t a, uint8_t b)
{
  return ~FStar_UInt8_gte_mask(b, a);
}

uint8_t Hacl_UInt8_lt_mask(uint8_t a, uint8_t b)
{
  return ~FStar_UInt8_gte_mask(a, b);
}

uint8_t Hacl_UInt8_lte_mask(uint8_t a, uint8_t b)
{
  return ~~FStar_UInt8_gte_mask(b, a);
}

uint8_t Hacl_UInt8_op_Plus_Hat(uint8_t a, uint8_t b)
{
  return a + b;
}

uint8_t Hacl_UInt8_op_Plus_Percent_Hat(uint8_t a, uint8_t b)
{
  return a + b;
}

uint8_t Hacl_UInt8_op_Subtraction_Hat(uint8_t a, uint8_t b)
{
  return a - b;
}

uint8_t Hacl_UInt8_op_Subtraction_Percent_Hat(uint8_t a, uint8_t b)
{
  return a - b;
}

uint8_t Hacl_UInt8_op_Star_Hat(uint8_t a, uint8_t b)
{
  return a * b;
}

uint8_t Hacl_UInt8_op_Star_Percent_Hat(uint8_t a, uint8_t b)
{
  return a * b;
}

uint8_t Hacl_UInt8_op_Amp_Hat(uint8_t a, uint8_t b)
{
  return a & b;
}

uint8_t Hacl_UInt8_op_Hat_Hat(uint8_t a, uint8_t b)
{
  return a ^ b;
}

uint8_t Hacl_UInt8_op_Bar_Hat(uint8_t a, uint8_t b)
{
  return a | b;
}

uint8_t Hacl_UInt8_op_Greater_Greater_Hat(uint8_t a, uint32_t s)
{
  return a >> s;
}

uint8_t Hacl_UInt8_op_Less_Less_Hat(uint8_t a, uint32_t s)
{
  return a << s;
}

