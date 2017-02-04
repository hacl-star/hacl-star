#include "Chacha20.h"

inline static uint32_t Hacl_Symmetric_Chacha20_load32_le(uint8_t *k)
{
  return load32_le(k);
}

inline static void Hacl_Symmetric_Chacha20_store32_le(uint8_t *k, uint32_t x)
{
  store32_le(k, x);
  return;
}

inline void Hacl_Symmetric_Chacha20_chacha_keysetup(uint32_t *ctx, uint8_t *k)
{
  ctx[0] = (uint32_t )0x61707865;
  ctx[1] = (uint32_t )0x3320646e;
  ctx[2] = (uint32_t )0x79622d32;
  ctx[3] = (uint32_t )0x6b206574;
  uint32_t _0_33 = Hacl_Symmetric_Chacha20_load32_le(k);
  ctx[4] = _0_33;
  uint32_t _0_34 = Hacl_Symmetric_Chacha20_load32_le(k + (uint32_t )4);
  ctx[5] = _0_34;
  uint32_t _0_35 = Hacl_Symmetric_Chacha20_load32_le(k + (uint32_t )8);
  ctx[6] = _0_35;
  uint32_t _0_36 = Hacl_Symmetric_Chacha20_load32_le(k + (uint32_t )12);
  ctx[7] = _0_36;
  uint32_t _0_37 = Hacl_Symmetric_Chacha20_load32_le(k + (uint32_t )16);
  ctx[8] = _0_37;
  uint32_t _0_38 = Hacl_Symmetric_Chacha20_load32_le(k + (uint32_t )20);
  ctx[9] = _0_38;
  uint32_t _0_39 = Hacl_Symmetric_Chacha20_load32_le(k + (uint32_t )24);
  ctx[10] = _0_39;
  uint32_t _0_40 = Hacl_Symmetric_Chacha20_load32_le(k + (uint32_t )28);
  ctx[11] = _0_40;
}

inline void
Hacl_Symmetric_Chacha20_chacha_ietf_ivsetup(uint32_t *ctx, uint8_t *iv, uint32_t counter)
{
  ctx[12] = counter;
  uint32_t _0_41 = Hacl_Symmetric_Chacha20_load32_le(iv);
  ctx[13] = _0_41;
  uint32_t _0_42 = Hacl_Symmetric_Chacha20_load32_le(iv + (uint32_t )4);
  ctx[14] = _0_42;
  uint32_t _0_43 = Hacl_Symmetric_Chacha20_load32_le(iv + (uint32_t )8);
  ctx[15] = _0_43;
}

inline static void
Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_quarter_round(
  uint32_t *ctx,
  uint32_t a,
  uint32_t b,
  uint32_t c,
  uint32_t d
)
{
  uint32_t xa0 = ctx[a];
  uint32_t xb0 = ctx[b];
  uint32_t xc0 = ctx[c];
  uint32_t xd0 = ctx[d];
  uint32_t xa1 = xa0 + xb0;
  uint32_t xd1 = xd0 ^ xa1;
  uint32_t xd2 = xd1 << (uint32_t )16 | xd1 >> (uint32_t )16;
  uint32_t xc1 = xc0 + xd2;
  uint32_t xb1 = xb0 ^ xc1;
  uint32_t xb2 = xb1 << (uint32_t )12 | xb1 >> (uint32_t )20;
  uint32_t xa = xa1 + xb2;
  uint32_t xd = xd2 ^ xa;
  uint32_t xd3 = xd << (uint32_t )8 | xd >> (uint32_t )24;
  uint32_t xc = xc1 + xd3;
  uint32_t xb = xb2 ^ xc;
  uint32_t xb3 = xb << (uint32_t )7 | xb >> (uint32_t )25;
  ctx[a] = xa;
  ctx[b] = xb3;
  ctx[c] = xc;
  ctx[d] = xd3;
}

inline static void Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_round(uint32_t *ctx)
{
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_quarter_round(ctx,
    (uint32_t )0,
    (uint32_t )4,
    (uint32_t )8,
    (uint32_t )12);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_quarter_round(ctx,
    (uint32_t )1,
    (uint32_t )5,
    (uint32_t )9,
    (uint32_t )13);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_quarter_round(ctx,
    (uint32_t )2,
    (uint32_t )6,
    (uint32_t )10,
    (uint32_t )14);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_quarter_round(ctx,
    (uint32_t )3,
    (uint32_t )7,
    (uint32_t )11,
    (uint32_t )15);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_quarter_round(ctx,
    (uint32_t )0,
    (uint32_t )5,
    (uint32_t )10,
    (uint32_t )15);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_quarter_round(ctx,
    (uint32_t )1,
    (uint32_t )6,
    (uint32_t )11,
    (uint32_t )12);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_quarter_round(ctx,
    (uint32_t )2,
    (uint32_t )7,
    (uint32_t )8,
    (uint32_t )13);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_quarter_round(ctx,
    (uint32_t )3,
    (uint32_t )4,
    (uint32_t )9,
    (uint32_t )14);
  return;
}

inline static void Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_rounds(uint32_t *ctx)
{
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_round(ctx);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_round(ctx);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_round(ctx);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_round(ctx);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_round(ctx);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_round(ctx);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_round(ctx);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_round(ctx);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_round(ctx);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_round(ctx);
  return;
}

inline static void
Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_core(uint32_t* tmp1, uint32_t *ctx, uint8_t *m, uint8_t *c)
{
  uint32_t tmp[16] = { 0 };
  memcpy(tmp, ctx, (uint32_t )16 * sizeof ctx[0]);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_rounds(tmp);
  uint32_t j0 = ctx[0];
  uint32_t j1 = ctx[1];
  uint32_t j2 = ctx[2];
  uint32_t j3 = ctx[3];
  uint32_t j4 = ctx[4];
  uint32_t j5 = ctx[5];
  uint32_t j6 = ctx[6];
  uint32_t j7 = ctx[7];
  uint32_t j8 = ctx[8];
  uint32_t j9 = ctx[9];
  uint32_t j10 = ctx[10];
  uint32_t j11 = ctx[11];
  uint32_t j12 = ctx[12];
  uint32_t j13 = ctx[13];
  uint32_t j14 = ctx[14];
  uint32_t j15 = ctx[15];
  uint32_t x00 = tmp[0];
  uint32_t x16 = tmp[1];
  uint32_t x20 = tmp[2];
  uint32_t x30 = tmp[3];
  uint32_t x40 = tmp[4];
  uint32_t x50 = tmp[5];
  uint32_t x60 = tmp[6];
  uint32_t x70 = tmp[7];
  uint32_t x80 = tmp[8];
  uint32_t x90 = tmp[9];
  uint32_t x100 = tmp[10];
  uint32_t x110 = tmp[11];
  uint32_t x120 = tmp[12];
  uint32_t x130 = tmp[13];
  uint32_t x140 = tmp[14];
  uint32_t x150 = tmp[15];
  uint32_t x01 = x00 + j0;
  uint32_t x17 = x16 + j1;
  uint32_t x21 = x20 + j2;
  uint32_t x31 = x30 + j3;
  uint32_t x41 = x40 + j4;
  uint32_t x51 = x50 + j5;
  uint32_t x61 = x60 + j6;
  uint32_t x71 = x70 + j7;
  uint32_t x81 = x80 + j8;
  uint32_t x91 = x90 + j9;
  uint32_t x101 = x100 + j10;
  uint32_t x111 = x110 + j11;
  uint32_t x121 = x120 + j12;
  uint32_t x131 = x130 + j13;
  uint32_t x141 = x140 + j14;
  uint32_t x151 = x150 + j15;
  uint32_t m0 = Hacl_Symmetric_Chacha20_load32_le(m);
  uint32_t m1 = Hacl_Symmetric_Chacha20_load32_le(m + (uint32_t )4);
  uint32_t m2 = Hacl_Symmetric_Chacha20_load32_le(m + (uint32_t )8);
  uint32_t m3 = Hacl_Symmetric_Chacha20_load32_le(m + (uint32_t )12);
  uint32_t m4 = Hacl_Symmetric_Chacha20_load32_le(m + (uint32_t )16);
  uint32_t m5 = Hacl_Symmetric_Chacha20_load32_le(m + (uint32_t )20);
  uint32_t m6 = Hacl_Symmetric_Chacha20_load32_le(m + (uint32_t )24);
  uint32_t m7 = Hacl_Symmetric_Chacha20_load32_le(m + (uint32_t )28);
  uint32_t m8 = Hacl_Symmetric_Chacha20_load32_le(m + (uint32_t )32);
  uint32_t m9 = Hacl_Symmetric_Chacha20_load32_le(m + (uint32_t )36);
  uint32_t m10 = Hacl_Symmetric_Chacha20_load32_le(m + (uint32_t )40);
  uint32_t m11 = Hacl_Symmetric_Chacha20_load32_le(m + (uint32_t )44);
  uint32_t m12 = Hacl_Symmetric_Chacha20_load32_le(m + (uint32_t )48);
  uint32_t m13 = Hacl_Symmetric_Chacha20_load32_le(m + (uint32_t )52);
  uint32_t m14 = Hacl_Symmetric_Chacha20_load32_le(m + (uint32_t )56);
  uint32_t m15 = Hacl_Symmetric_Chacha20_load32_le(m + (uint32_t )60);
  uint32_t x02 = x01 ^ m0;
  uint32_t x1 = x17 ^ m1;
  uint32_t x2 = x21 ^ m2;
  uint32_t x3 = x31 ^ m3;
  uint32_t x4 = x41 ^ m4;
  uint32_t x5 = x51 ^ m5;
  uint32_t x6 = x61 ^ m6;
  uint32_t x7 = x71 ^ m7;
  uint32_t x8 = x81 ^ m8;
  uint32_t x9 = x91 ^ m9;
  uint32_t x10 = x101 ^ m10;
  uint32_t x11 = x111 ^ m11;
  uint32_t x12 = x121 ^ m12;
  uint32_t x13 = x131 ^ m13;
  uint32_t x14 = x141 ^ m14;
  uint32_t x15 = x151 ^ m15;
  uint8_t *x0 = c;
  Hacl_Symmetric_Chacha20_store32_le(x0, x02);
  Hacl_Symmetric_Chacha20_store32_le(x0 + (uint32_t )4, x1);
  Hacl_Symmetric_Chacha20_store32_le(x0 + (uint32_t )8, x2);
  Hacl_Symmetric_Chacha20_store32_le(x0 + (uint32_t )12, x3);
  Hacl_Symmetric_Chacha20_store32_le(x0 + (uint32_t )16, x4);
  Hacl_Symmetric_Chacha20_store32_le(x0 + (uint32_t )20, x5);
  Hacl_Symmetric_Chacha20_store32_le(x0 + (uint32_t )24, x6);
  Hacl_Symmetric_Chacha20_store32_le(x0 + (uint32_t )28, x7);
  Hacl_Symmetric_Chacha20_store32_le(x0 + (uint32_t )32, x8);
  Hacl_Symmetric_Chacha20_store32_le(x0 + (uint32_t )36, x9);
  Hacl_Symmetric_Chacha20_store32_le(x0 + (uint32_t )40, x10);
  Hacl_Symmetric_Chacha20_store32_le(x0 + (uint32_t )44, x11);
  Hacl_Symmetric_Chacha20_store32_le(x0 + (uint32_t )48, x12);
  Hacl_Symmetric_Chacha20_store32_le(x0 + (uint32_t )52, x13);
  Hacl_Symmetric_Chacha20_store32_le(x0 + (uint32_t )56, x14);
  /* start inlining Hacl.Symmetric.Chacha20.chacha_encrypt_bytes_store */
  Hacl_Symmetric_Chacha20_store32_le(x0 + (uint32_t )60, x15);
  /* end inlining Hacl.Symmetric.Chacha20.chacha_encrypt_bytes_store */
}

inline static void
Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_loop(
  uint32_t *block,
  uint32_t *ctx,
  uint8_t *m,
  uint8_t *c,
  uint32_t len
)
{
  if (len < (uint32_t )64)
    return;
  else
  {
    Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_core(block,ctx, m, c);
    uint32_t ctr = ctx[12];
    uint32_t one = (uint32_t )1;
    ctx[12] = ctr + one;
    Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_loop(block,ctx,
      m + (uint32_t )64,
      c + (uint32_t )64,
      len - (uint32_t )64);
    return;
  }
}

inline static void
Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_finish(
  uint32_t *block,
  uint32_t *ctx,
  uint8_t *m,
  uint8_t *c,
  uint32_t len
)
{
  uint8_t zero = (uint8_t )0;
  uint8_t tmp[64];
  for (uintmax_t i = 0; i < (uint32_t )64; ++i)
    tmp[i] = zero;
  memcpy(tmp, m, len * sizeof m[0]);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_core(block,ctx, tmp, tmp);
  memcpy(c, tmp, len * sizeof tmp[0]);
}

void
Hacl_Symmetric_Chacha20_chacha_encrypt_bytes(
  uint32_t *ctx,
  uint8_t *m,
  uint8_t *c,
  uint32_t len
)
{
  uint32_t block[16] = { 0 };
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_loop(block,ctx, m, c, len);
  uint32_t rema = len & (uint32_t )63;
  uint32_t q = len >> (uint32_t )6;
  if (rema >= (uint32_t )0)
  {
    uint8_t *m0 = m + len - rema;
    uint8_t *c0 = c + len - rema;
    Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_finish(block,ctx, m0, c0, rema);
    return;
  }
  else
    return;
}

