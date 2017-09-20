#include "Hacl_Policies.h"

uint8_t Hacl_Policies_declassify_u8(uint8_t x)
{
  return x;
}

uint32_t Hacl_Policies_declassify_u32(uint32_t x)
{
  return x;
}

uint64_t Hacl_Policies_declassify_u64(uint64_t x)
{
  return x;
}

void Hacl_Policies_declassify_u128(FStar_UInt128_uint128 *x, FStar_UInt128_uint128 *ret)
{
  ret[0] = x[0];
}

uint8_t Hacl_Policies_leak_byte(uint8_t *b, uint32_t n1)
{
  return b[n1];
}

uint8_t Hacl_Policies_cmp_bytes_(uint8_t *b1, uint8_t *b2, uint32_t len, uint8_t tmp)
{
  if (len == (uint32_t )0)
    return tmp;
  else
  {
    uint32_t i = len - (uint32_t )1;
    uint8_t bi1 = Hacl_Policies_leak_byte(b1, i);
    uint8_t bi2 = Hacl_Policies_leak_byte(b2, i);
    uint8_t z = Hacl_Policies_cmp_bytes_(b1, b2, i, FStar_UInt8_eq_mask(bi1, bi2) & tmp);
    return z;
  }
}

uint8_t Hacl_Policies_cmp_bytes(uint8_t *b1, uint8_t *b2, uint32_t len)
{
  uint8_t z = Hacl_Policies_cmp_bytes_(b1, b2, len, (uint8_t )255);
  return ~z;
}

