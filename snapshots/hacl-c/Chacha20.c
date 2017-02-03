#include "Chacha20.h"

static inline uint32_t Hacl_Symmetric_Chacha20_load32_le(uint8_t *k)
{
  return le32toh(load32(k));
}

static inline void Hacl_Symmetric_Chacha20_store32_le(uint8_t *k, uint32_t x)
{
  store32(k,htole32(x));
}

void Hacl_Symmetric_Chacha20_chacha_keysetup(uint32_t *ctx, uint8_t *k)
{
  ctx[(uint32_t )0] = (uint32_t )0x61707865;
  ctx[(uint32_t )1] = (uint32_t )0x3320646e;
  ctx[(uint32_t )2] = (uint32_t )0x79622d32;
  ctx[(uint32_t )3] = (uint32_t )0x6b206574;
  uint32_t _0_24 = Hacl_Symmetric_Chacha20_load32_le(k + (uint32_t )0);
  ctx[(uint32_t )4] = _0_24;
  uint32_t _0_25 = Hacl_Symmetric_Chacha20_load32_le(k + (uint32_t )4);
  ctx[(uint32_t )5] = _0_25;
  uint32_t _0_26 = Hacl_Symmetric_Chacha20_load32_le(k + (uint32_t )8);
  ctx[(uint32_t )6] = _0_26;
  uint32_t _0_27 = Hacl_Symmetric_Chacha20_load32_le(k + (uint32_t )12);
  ctx[(uint32_t )7] = _0_27;
  uint32_t _0_28 = Hacl_Symmetric_Chacha20_load32_le(k + (uint32_t )16);
  ctx[(uint32_t )8] = _0_28;
  uint32_t _0_29 = Hacl_Symmetric_Chacha20_load32_le(k + (uint32_t )20);
  ctx[(uint32_t )9] = _0_29;
  uint32_t _0_30 = Hacl_Symmetric_Chacha20_load32_le(k + (uint32_t )24);
  ctx[(uint32_t )10] = _0_30;
  uint32_t _0_31 = Hacl_Symmetric_Chacha20_load32_le(k + (uint32_t )28);
  ctx[(uint32_t )11] = _0_31;
}

void Hacl_Symmetric_Chacha20_chacha_ietf_ivsetup(uint32_t *ctx, uint8_t *iv, uint32_t counter)
{
  ctx[(uint32_t )12] = counter;
  uint32_t _0_32 = Hacl_Symmetric_Chacha20_load32_le(iv);
  ctx[(uint32_t )13] = _0_32;
  uint32_t _0_33 = Hacl_Symmetric_Chacha20_load32_le(iv + (uint32_t )4);
  ctx[(uint32_t )14] = _0_33;
  uint32_t _0_34 = Hacl_Symmetric_Chacha20_load32_le(iv + (uint32_t )8);
  ctx[(uint32_t )15] = _0_34;
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
Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_core(uint32_t *ctx, uint8_t *m, uint8_t *c)
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
  uint8_t *x02 = m;
  uint32_t
  m0 =
    /* start inlining Hacl.Symmetric.Chacha20.load32_le */
      load32_le(x02)
    /* end inlining Hacl.Symmetric.Chacha20.load32_le */;
  uint8_t *x03 = m + (uint32_t )4;
  uint32_t
  m1 =
    /* start inlining Hacl.Symmetric.Chacha20.load32_le */
      load32_le(x03)
    /* end inlining Hacl.Symmetric.Chacha20.load32_le */;
  uint8_t *x04 = m + (uint32_t )8;
  uint32_t
  m2 =
    /* start inlining Hacl.Symmetric.Chacha20.load32_le */
      load32_le(x04)
    /* end inlining Hacl.Symmetric.Chacha20.load32_le */;
  uint8_t *x05 = m + (uint32_t )12;
  uint32_t
  m3 =
    /* start inlining Hacl.Symmetric.Chacha20.load32_le */
      load32_le(x05)
    /* end inlining Hacl.Symmetric.Chacha20.load32_le */;
  uint8_t *x06 = m + (uint32_t )16;
  uint32_t
  m4 =
    /* start inlining Hacl.Symmetric.Chacha20.load32_le */
      load32_le(x06)
    /* end inlining Hacl.Symmetric.Chacha20.load32_le */;
  uint8_t *x07 = m + (uint32_t )20;
  uint32_t
  m5 =
    /* start inlining Hacl.Symmetric.Chacha20.load32_le */
      load32_le(x07)
    /* end inlining Hacl.Symmetric.Chacha20.load32_le */;
  uint8_t *x08 = m + (uint32_t )24;
  uint32_t
  m6 =
    /* start inlining Hacl.Symmetric.Chacha20.load32_le */
      load32_le(x08)
    /* end inlining Hacl.Symmetric.Chacha20.load32_le */;
  uint8_t *x09 = m + (uint32_t )28;
  uint32_t
  m7 =
    /* start inlining Hacl.Symmetric.Chacha20.load32_le */
      load32_le(x09)
    /* end inlining Hacl.Symmetric.Chacha20.load32_le */;
  uint8_t *x010 = m + (uint32_t )32;
  uint32_t
  m8 =
    /* start inlining Hacl.Symmetric.Chacha20.load32_le */
      load32_le(x010)
    /* end inlining Hacl.Symmetric.Chacha20.load32_le */;
  uint8_t *x011 = m + (uint32_t )36;
  uint32_t
  m9 =
    /* start inlining Hacl.Symmetric.Chacha20.load32_le */
      load32_le(x011)
    /* end inlining Hacl.Symmetric.Chacha20.load32_le */;
  uint8_t *x012 = m + (uint32_t )40;
  uint32_t
  m10 =
    /* start inlining Hacl.Symmetric.Chacha20.load32_le */
      load32_le(x012)
    /* end inlining Hacl.Symmetric.Chacha20.load32_le */;
  uint8_t *x013 = m + (uint32_t )44;
  uint32_t
  m11 =
    /* start inlining Hacl.Symmetric.Chacha20.load32_le */
      load32_le(x013)
    /* end inlining Hacl.Symmetric.Chacha20.load32_le */;
  uint8_t *x014 = m + (uint32_t )48;
  uint32_t
  m12 =
    /* start inlining Hacl.Symmetric.Chacha20.load32_le */
      load32_le(x014)
    /* end inlining Hacl.Symmetric.Chacha20.load32_le */;
  uint8_t *x015 = m + (uint32_t )52;
  uint32_t
  m13 =
    /* start inlining Hacl.Symmetric.Chacha20.load32_le */
      load32_le(x015)
    /* end inlining Hacl.Symmetric.Chacha20.load32_le */;
  uint8_t *x016 = m + (uint32_t )56;
  uint32_t
  m14 =
    /* start inlining Hacl.Symmetric.Chacha20.load32_le */
      load32_le(x016)
    /* end inlining Hacl.Symmetric.Chacha20.load32_le */;
  uint8_t *x017 = m + (uint32_t )60;
  uint32_t
  m15 =
    /* start inlining Hacl.Symmetric.Chacha20.load32_le */
      load32_le(x017)
    /* end inlining Hacl.Symmetric.Chacha20.load32_le */;
  uint32_t x018 = x01 ^ m0;
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
  uint8_t *x019 = c;
  uint8_t *x0 = x019;
  /* start inlining Hacl.Symmetric.Chacha20.store32_le */
  store32_le(x0, x018);
  /* end inlining Hacl.Symmetric.Chacha20.store32_le */
  uint8_t *x020 = x019 + (uint32_t )4;
  /* start inlining Hacl.Symmetric.Chacha20.store32_le */
  store32_le(x020, x1);
  /* end inlining Hacl.Symmetric.Chacha20.store32_le */
  uint8_t *x021 = x019 + (uint32_t )8;
  /* start inlining Hacl.Symmetric.Chacha20.store32_le */
  store32_le(x021, x2);
  /* end inlining Hacl.Symmetric.Chacha20.store32_le */
  uint8_t *x022 = x019 + (uint32_t )12;
  /* start inlining Hacl.Symmetric.Chacha20.store32_le */
  store32_le(x022, x3);
  /* end inlining Hacl.Symmetric.Chacha20.store32_le */
  uint8_t *x023 = x019 + (uint32_t )16;
  /* start inlining Hacl.Symmetric.Chacha20.store32_le */
  store32_le(x023, x4);
  /* end inlining Hacl.Symmetric.Chacha20.store32_le */
  uint8_t *x024 = x019 + (uint32_t )20;
  /* start inlining Hacl.Symmetric.Chacha20.store32_le */
  store32_le(x024, x5);
  /* end inlining Hacl.Symmetric.Chacha20.store32_le */
  uint8_t *x025 = x019 + (uint32_t )24;
  /* start inlining Hacl.Symmetric.Chacha20.store32_le */
  store32_le(x025, x6);
  /* end inlining Hacl.Symmetric.Chacha20.store32_le */
  uint8_t *x026 = x019 + (uint32_t )28;
  /* start inlining Hacl.Symmetric.Chacha20.store32_le */
  store32_le(x026, x7);
  /* end inlining Hacl.Symmetric.Chacha20.store32_le */
  uint8_t *x027 = x019 + (uint32_t )32;
  /* start inlining Hacl.Symmetric.Chacha20.store32_le */
  store32_le(x027, x8);
  /* end inlining Hacl.Symmetric.Chacha20.store32_le */
  uint8_t *x028 = x019 + (uint32_t )36;
  /* start inlining Hacl.Symmetric.Chacha20.store32_le */
  store32_le(x028, x9);
  /* end inlining Hacl.Symmetric.Chacha20.store32_le */
  uint8_t *x029 = x019 + (uint32_t )40;
  /* start inlining Hacl.Symmetric.Chacha20.store32_le */
  store32_le(x029, x10);
  /* end inlining Hacl.Symmetric.Chacha20.store32_le */
  uint8_t *x030 = x019 + (uint32_t )44;
  /* start inlining Hacl.Symmetric.Chacha20.store32_le */
  store32_le(x030, x11);
  /* end inlining Hacl.Symmetric.Chacha20.store32_le */
  uint8_t *x031 = x019 + (uint32_t )48;
  /* start inlining Hacl.Symmetric.Chacha20.store32_le */
  store32_le(x031, x12);
  /* end inlining Hacl.Symmetric.Chacha20.store32_le */
  uint8_t *x032 = x019 + (uint32_t )52;
  /* start inlining Hacl.Symmetric.Chacha20.store32_le */
  store32_le(x032, x13);
  /* end inlining Hacl.Symmetric.Chacha20.store32_le */
  uint8_t *x033 = x019 + (uint32_t )56;
  /* start inlining Hacl.Symmetric.Chacha20.store32_le */
  store32_le(x033, x14);
  /* end inlining Hacl.Symmetric.Chacha20.store32_le */
  uint8_t *x034 = x019 + (uint32_t )60;
  /* start inlining Hacl.Symmetric.Chacha20.chacha_encrypt_bytes_store */
  /* start inlining Hacl.Symmetric.Chacha20.store32_le */
  store32_le(x034, x15);
  /* end inlining Hacl.Symmetric.Chacha20.store32_le */
  /* end inlining Hacl.Symmetric.Chacha20.chacha_encrypt_bytes_store */
}

inline static void
Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_loop(
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
    Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_core(ctx, m, c);
    uint32_t ctr = ctx[12];
    uint32_t one = (uint32_t )1;
    ctx[12] = ctr + one;
    Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_loop(ctx,
      m + (uint32_t )64,
      c + (uint32_t )64,
      len - (uint32_t )64);
    return;
  }
}

inline static void
Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_finish(
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
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_core(ctx, tmp, tmp);
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
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_loop(ctx, m, c, len);
  uint32_t rema = len & (uint32_t )63;
  uint32_t q = len >> (uint32_t )6;
  if (rema >= (uint32_t )0)
  {
    uint8_t *m0 = m + len - rema;
    uint8_t *c0 = c + len - rema;
    Hacl_Symmetric_Chacha20_chacha_encrypt_bytes_finish(ctx, m0, c0, rema);
    return;
  }
  else
    return;
}

