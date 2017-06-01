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

uint8_t Hacl_Policies_leak_byte(uint8_t *b, uint32_t n1)
{
  return b[n1];
}

uint8_t Hacl_Policies_cmp_bytes_(uint8_t *b, uint8_t *b_, uint32_t len, uint8_t tmp)
{
  if (len == (uint32_t )0)
    return ~tmp;
  else
  {
    uint32_t i = len - (uint32_t )1;
    uint8_t bi = Hacl_Policies_leak_byte(b, i);
    uint8_t bi_ = Hacl_Policies_leak_byte(b_, i);
    uint8_t tmp1 = FStar_UInt8_eq_mask(bi, bi_) & tmp;
    return Hacl_Policies_cmp_bytes_(b, b_, i, tmp1);
  }
}

uint8_t Hacl_Policies_cmp_bytes(uint8_t *b, uint8_t *b_, uint32_t len)
{
  return Hacl_Policies_cmp_bytes_(b, b_, len, (uint8_t )255);
}

