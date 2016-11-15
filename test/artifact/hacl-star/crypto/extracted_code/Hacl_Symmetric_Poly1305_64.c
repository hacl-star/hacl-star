#include "Hacl_Symmetric_Poly1305_64.h"

uint64_t Hacl_Symmetric_Poly1305_64_load64_le(uint8_t *b)
{
  uint8_t b0 = b[(uint32_t )0];
  uint8_t b1 = b[(uint32_t )1];
  uint8_t b2 = b[(uint32_t )2];
  uint8_t b3 = b[(uint32_t )3];
  uint8_t b4 = b[(uint32_t )4];
  uint8_t b5 = b[(uint32_t )5];
  uint8_t b6 = b[(uint32_t )6];
  uint8_t b7 = b[(uint32_t )7];
  return
    (uint64_t )b0
    | (uint64_t )b1 << (uint32_t )8
    | (uint64_t )b2 << (uint32_t )16
    | (uint64_t )b3 << (uint32_t )24
    | (uint64_t )b4 << (uint32_t )32
    | (uint64_t )b5 << (uint32_t )40
    | (uint64_t )b6 << (uint32_t )48
    | (uint64_t )b7 << (uint32_t )56;
}

void Hacl_Symmetric_Poly1305_64_store64_le(uint8_t *b, uint64_t z)
{
  b[(uint32_t )0] = (uint8_t )z;
  b[(uint32_t )1] = (uint8_t )(z >> (uint32_t )8);
  b[(uint32_t )2] = (uint8_t )(z >> (uint32_t )16);
  b[(uint32_t )3] = (uint8_t )(z >> (uint32_t )24);
  b[(uint32_t )4] = (uint8_t )(z >> (uint32_t )32);
  b[(uint32_t )5] = (uint8_t )(z >> (uint32_t )40);
  b[(uint32_t )6] = (uint8_t )(z >> (uint32_t )48);
  b[(uint32_t )7] = (uint8_t )(z >> (uint32_t )56);
}

void Hacl_Symmetric_Poly1305_64_poly1305_init(uint64_t *st, uint8_t *key)
{
  uint64_t *r = st + (uint32_t )0;
  uint64_t *h = st + (uint32_t )3;
  uint64_t t0 = Hacl_Symmetric_Poly1305_64_load64_le(key);
  uint64_t t1 = Hacl_Symmetric_Poly1305_64_load64_le(key + (uint32_t )8);
  r[(uint32_t )0] = t0 & (uint64_t )0xffc0fffffff;
  r[(uint32_t )1] = (t0 >> (uint32_t )44 | t1 << (uint32_t )20) & (uint64_t )0xfffffc0ffff;
  r[(uint32_t )2] = t1 >> (uint32_t )24 & (uint64_t )0x00ffffffc0f;
  uint64_t zero = (uint64_t )0;
  h[(uint32_t )0] = zero;
  h[(uint32_t )1] = zero;
  h[(uint32_t )2] = zero;
}

void
Hacl_Symmetric_Poly1305_64_poly1305_blocks_loop(
  uint64_t *st,
  uint8_t *m,
  uint64_t len,
  uint64_t r0,
  uint64_t r1,
  uint64_t r2,
  uint64_t s1,
  uint64_t s2,
  uint64_t h0,
  uint64_t h1,
  uint64_t h2
)
{
  uint64_t *h = st + (uint32_t )3;
  if (len < (uint64_t )16)
  {
    h[(uint32_t )0] = h0;
    h[(uint32_t )1] = h1;
    h[(uint32_t )2] = h2;
  }
  else
  {
    uint64_t t0 = Hacl_Symmetric_Poly1305_64_load64_le(m);
    uint64_t t1 = Hacl_Symmetric_Poly1305_64_load64_le(m + (uint32_t )8);
    uint64_t mask_2_44 = (uint64_t )0xfffffffffff;
    uint64_t mask_2_42 = (uint64_t )0x3ffffffffff;
    uint64_t h00 = h0 + (t0 & mask_2_44);
    uint64_t h10 = h1 + ((t0 >> (uint32_t )44 | t1 << (uint32_t )20) & mask_2_44);
    uint64_t h20 = h2 + (t1 >> (uint32_t )24 & mask_2_42 | (uint64_t )1 << (uint32_t )40);
    FStar_UInt128_t d0 = FStar_UInt128_mul_wide(h00, r0);
    FStar_UInt128_t d3 = FStar_UInt128_mul_wide(h10, s2);
    FStar_UInt128_t d00 = FStar_UInt128_add_mod(d0, d3);
    FStar_UInt128_t d4 = FStar_UInt128_mul_wide(h20, s1);
    FStar_UInt128_t d01 = FStar_UInt128_add_mod(d00, d4);
    FStar_UInt128_t d10 = FStar_UInt128_mul_wide(h00, r1);
    FStar_UInt128_t d5 = FStar_UInt128_mul_wide(h10, r0);
    FStar_UInt128_t d11 = FStar_UInt128_add_mod(d10, d5);
    FStar_UInt128_t d6 = FStar_UInt128_mul_wide(h20, s2);
    FStar_UInt128_t d12 = FStar_UInt128_add_mod(d11, d6);
    FStar_UInt128_t d20 = FStar_UInt128_mul_wide(h00, r2);
    FStar_UInt128_t d7 = FStar_UInt128_mul_wide(h10, r1);
    FStar_UInt128_t d21 = FStar_UInt128_add_mod(d20, d7);
    FStar_UInt128_t d = FStar_UInt128_mul_wide(h20, r0);
    FStar_UInt128_t d22 = FStar_UInt128_add_mod(d21, d);
    uint64_t c0 = FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_shift_right(d01, (uint32_t )44));
    uint64_t h01 = FStar_Int_Cast_uint128_to_uint64(d01) & mask_2_44;
    FStar_UInt128_t d1 = FStar_UInt128_add_mod(d12, FStar_Int_Cast_uint64_to_uint128(c0));
    uint64_t c1 = FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_shift_right(d1, (uint32_t )44));
    uint64_t h11 = FStar_Int_Cast_uint128_to_uint64(d1) & mask_2_44;
    FStar_UInt128_t d2 = FStar_UInt128_add_mod(d22, FStar_Int_Cast_uint64_to_uint128(c1));
    uint64_t c2 = FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_shift_right(d2, (uint32_t )42));
    uint64_t h2 = FStar_Int_Cast_uint128_to_uint64(d2) & mask_2_42;
    uint64_t h02 = h01 + c2 * (uint64_t )5;
    uint64_t c = h02 >> (uint32_t )44;
    uint64_t h0 = h02 & mask_2_44;
    uint64_t h1 = h11 + c;
    uint64_t len0 = len - (uint64_t )16;
    uint8_t *m0 = m + (uint32_t )16;
    Hacl_Symmetric_Poly1305_64_poly1305_blocks_loop(st, m0, len0, r0, r1, r2, s1, s2, h0, h1, h2);
    return;
  }
}

void Hacl_Symmetric_Poly1305_64_poly1305_blocks(uint64_t *st, uint8_t *m, uint64_t len)
{
  uint64_t *r = st + (uint32_t )0;
  uint64_t *h = st + (uint32_t )3;
  uint64_t r0 = r[(uint32_t )0];
  uint64_t r1 = r[(uint32_t )1];
  uint64_t r2 = r[(uint32_t )2];
  uint64_t h0 = h[(uint32_t )0];
  uint64_t h1 = h[(uint32_t )1];
  uint64_t h2 = h[(uint32_t )2];
  uint64_t five = (uint64_t )5;
  uint64_t s1 = r1 * (five << (uint32_t )2);
  uint64_t s2 = r2 * (five << (uint32_t )2);
  Hacl_Symmetric_Poly1305_64_poly1305_blocks_loop(st, m, len, r0, r1, r2, s1, s2, h0, h1, h2);
  return;
}

void Hacl_Symmetric_Poly1305_64_poly1305_finish_(uint8_t *m, uint64_t rem, uint64_t *st)
{
  uint64_t *r = st + (uint32_t )0;
  uint64_t *h = st + (uint32_t )3;
  uint64_t h00 = h[(uint32_t )0];
  uint64_t h10 = h[(uint32_t )1];
  uint64_t h20 = h[(uint32_t )2];
  uint64_t r0 = r[(uint32_t )0];
  uint64_t r1 = r[(uint32_t )1];
  uint64_t r2 = r[(uint32_t )2];
  uint64_t mask_2_44 = (uint64_t )0xfffffffffff;
  uint64_t mask_2_42 = (uint64_t )0x3ffffffffff;
  uint64_t five = (uint64_t )5;
  uint64_t s1 = r1 * (five << (uint32_t )2);
  uint64_t s2 = r2 * (five << (uint32_t )2);
  uint8_t zero = (uint8_t )0;
  uint8_t block[16];
  for (uintmax_t i = 0; i < (uint32_t )16; ++i)
    block[i] = zero;
  uint32_t i = (uint32_t )rem;
  memcpy(block, m, i * sizeof m[0]);
  block[i] = (uint8_t )1;
  uint64_t t0 = Hacl_Symmetric_Poly1305_64_load64_le(block);
  uint64_t t1 = Hacl_Symmetric_Poly1305_64_load64_le(block + (uint32_t )8);
  uint64_t h01 = h00 + (t0 & mask_2_44);
  uint64_t h11 = h10 + ((t0 >> (uint32_t )44 | t1 << (uint32_t )20) & mask_2_44);
  uint64_t h21 = h20 + (t1 >> (uint32_t )24 & mask_2_42);
  FStar_UInt128_t d0 = FStar_UInt128_mul_wide(h01, r0);
  FStar_UInt128_t d3 = FStar_UInt128_mul_wide(h11, s2);
  FStar_UInt128_t d00 = FStar_UInt128_add_mod(d0, d3);
  FStar_UInt128_t d4 = FStar_UInt128_mul_wide(h21, s1);
  FStar_UInt128_t d01 = FStar_UInt128_add_mod(d00, d4);
  FStar_UInt128_t d10 = FStar_UInt128_mul_wide(h01, r1);
  FStar_UInt128_t d5 = FStar_UInt128_mul_wide(h11, r0);
  FStar_UInt128_t d11 = FStar_UInt128_add_mod(d10, d5);
  FStar_UInt128_t d6 = FStar_UInt128_mul_wide(h21, s2);
  FStar_UInt128_t d12 = FStar_UInt128_add_mod(d11, d6);
  FStar_UInt128_t d20 = FStar_UInt128_mul_wide(h01, r2);
  FStar_UInt128_t d7 = FStar_UInt128_mul_wide(h11, r1);
  FStar_UInt128_t d21 = FStar_UInt128_add_mod(d20, d7);
  FStar_UInt128_t d = FStar_UInt128_mul_wide(h21, r0);
  FStar_UInt128_t d22 = FStar_UInt128_add_mod(d21, d);
  uint64_t c0 = FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_shift_right(d01, (uint32_t )44));
  uint64_t h02 = FStar_Int_Cast_uint128_to_uint64(d01) & mask_2_44;
  FStar_UInt128_t d1 = FStar_UInt128_add_mod(d12, FStar_Int_Cast_uint64_to_uint128(c0));
  uint64_t c1 = FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_shift_right(d1, (uint32_t )44));
  uint64_t h12 = FStar_Int_Cast_uint128_to_uint64(d1) & mask_2_44;
  FStar_UInt128_t d2 = FStar_UInt128_add_mod(d22, FStar_Int_Cast_uint64_to_uint128(c1));
  uint64_t c2 = FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_shift_right(d2, (uint32_t )42));
  uint64_t h2 = FStar_Int_Cast_uint128_to_uint64(d2) & mask_2_42;
  uint64_t h03 = h02 + c2 * (uint64_t )5;
  uint64_t c = h03 >> (uint32_t )44;
  uint64_t h0 = h03 & mask_2_44;
  uint64_t h1 = h12 + c;
  h[(uint32_t )0] = h0;
  h[(uint32_t )1] = h1;
  h[(uint32_t )2] = h2;
}

void Hacl_Symmetric_Poly1305_64_poly1305_finish__(uint8_t *mac, uint8_t *key, uint64_t *st)
{
  uint64_t mask_2_44 = (uint64_t )0xfffffffffff;
  uint64_t mask_2_42 = (uint64_t )0x3ffffffffff;
  uint64_t *h = st + (uint32_t )3;
  uint64_t h00 = h[(uint32_t )0];
  uint64_t h10 = h[(uint32_t )1];
  uint64_t h20 = h[(uint32_t )2];
  uint64_t c0 = h10 >> (uint32_t )44;
  uint64_t h11 = h10 & mask_2_44;
  uint64_t h21 = h20 + c0;
  uint64_t c1 = h21 >> (uint32_t )42;
  uint64_t h22 = h21 & mask_2_42;
  uint64_t h01 = h00 + c1 * (uint64_t )5;
  uint64_t c2 = h01 >> (uint32_t )44;
  uint64_t h02 = h01 & mask_2_44;
  uint64_t h12 = h11 + c2;
  uint64_t c3 = h12 >> (uint32_t )44;
  uint64_t h13 = h12 & mask_2_44;
  uint64_t h23 = h22 + c3;
  uint64_t c4 = h23 >> (uint32_t )42;
  uint64_t h24 = h23 & mask_2_42;
  uint64_t h03 = h02 + c4 * (uint64_t )5;
  uint64_t c5 = h03 >> (uint32_t )44;
  uint64_t h04 = h03 & mask_2_44;
  uint64_t h14 = h13 + c5;
  uint64_t
  mask =
    FStar_UInt64_eq_mask(h04,
      mask_2_44)
    & FStar_UInt64_eq_mask(h14, mask_2_44)
    & FStar_UInt64_gte_mask(h24, (uint64_t )0x3fffffffffb);
  uint64_t h05 = h04 & ~mask;
  uint64_t h15 = h14 & ~mask;
  uint64_t h25 = h24 - ((uint64_t )0x3fffffffffb & mask);
  uint64_t t0 = Hacl_Symmetric_Poly1305_64_load64_le(key + (uint32_t )16);
  uint64_t t1 = Hacl_Symmetric_Poly1305_64_load64_le(key + (uint32_t )24);
  uint64_t h06 = h05 + (t0 & mask_2_44);
  uint64_t c6 = h06 >> (uint32_t )44;
  uint64_t h07 = h06 & mask_2_44;
  uint64_t h16 = h15 + ((t0 >> (uint32_t )44 | t1 << (uint32_t )20) & mask_2_44) + c6;
  uint64_t c = h16 >> (uint32_t )44;
  uint64_t h17 = h16 & mask_2_44;
  uint64_t h2 = h25 + (t1 >> (uint32_t )24 & mask_2_42) + c;
  uint64_t h26 = h2 & mask_2_42;
  uint64_t h0 = h07 | h17 << (uint32_t )44;
  uint64_t h1 = h17 >> (uint32_t )20 | h26 << (uint32_t )24;
  Hacl_Symmetric_Poly1305_64_store64_le(mac, h0);
  Hacl_Symmetric_Poly1305_64_store64_le(mac + (uint32_t )8, h1);
  return;
}

void
Hacl_Symmetric_Poly1305_64_poly1305_finish(
  uint8_t *mac,
  uint8_t *m,
  uint64_t len,
  uint8_t *key,
  uint64_t *st
)
{
  uint64_t rem = len & (uint64_t )0xf;
  uint64_t *r = st + (uint32_t )0;
  uint64_t *h = st + (uint32_t )3;
  if (rem == (uint64_t )0)
  {
    
  }
  else
  {
    uint8_t *m0 = m + (uint32_t )(len - rem);
    Hacl_Symmetric_Poly1305_64_poly1305_finish_(m0, rem, st);
  }
  Hacl_Symmetric_Poly1305_64_poly1305_finish__(mac, key, st);
  return;
}

void
Hacl_Symmetric_Poly1305_64_crypto_onetimeauth(
  uint8_t *output,
  uint8_t *input,
  uint64_t len,
  uint8_t *k
)
{
  uint64_t zero = (uint64_t )0;
  uint64_t st[6];
  for (uintmax_t i = 0; i < (uint32_t )6; ++i)
    st[i] = zero;
  Hacl_Symmetric_Poly1305_64_poly1305_init(st, k);
  Hacl_Symmetric_Poly1305_64_poly1305_blocks(st, input, len);
  Hacl_Symmetric_Poly1305_64_poly1305_finish(output, input, len, k, st);
}

