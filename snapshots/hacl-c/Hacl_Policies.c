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

FStar_UInt128_t Hacl_Policies_declassify_u128(FStar_UInt128_t x)
{
  return x;
}

uint8_t Hacl_Policies_cmp_bytes_(uint8_t *b1, uint8_t *b2, uint32_t len, uint8_t *tmp)
{
  for (uint32_t i = (uint32_t )0; i < len; i = i + (uint32_t )1)
  {
    uint8_t bi1 = b1[i];
    uint8_t bi2 = b2[i];
    uint8_t z0 = tmp[0];
    tmp[0] = FStar_UInt8_eq_mask(bi1, bi2) & z0;
  }
  return tmp[0];
}

uint8_t Hacl_Policies_cmp_bytes(uint8_t *b1, uint8_t *b2, uint32_t len)
{
  uint8_t tmp[1];
  tmp[0] = (uint8_t )255;
  uint8_t z = Hacl_Policies_cmp_bytes_(b1, b2, len, tmp);
  return ~z;
}

