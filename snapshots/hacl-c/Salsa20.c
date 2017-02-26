#include "Salsa20.h"

inline static uint32_t Hacl_Symmetric_Salsa20_rol32(uint32_t a, uint32_t s)
{
  return a << s | a >> (uint32_t )32 - s;
}

force_inline static void
Hacl_Symmetric_Salsa20_salsa20_quarter_round(
  uint32_t *ctx,
  uint32_t a,
  uint32_t b,
  uint32_t c,
  uint32_t d
)
{
  uint32_t y00 = ctx[a];
  uint32_t y10 = ctx[b];
  uint32_t y20 = ctx[c];
  uint32_t y30 = ctx[d];
  uint32_t y1 = y10 ^ Hacl_Symmetric_Salsa20_rol32(y00 + y30, (uint32_t )7);
  uint32_t y2 = y20 ^ Hacl_Symmetric_Salsa20_rol32(y1 + y00, (uint32_t )9);
  uint32_t y3 = y30 ^ Hacl_Symmetric_Salsa20_rol32(y2 + y1, (uint32_t )13);
  uint32_t y0 = y00 ^ Hacl_Symmetric_Salsa20_rol32(y3 + y2, (uint32_t )18);
  ctx[a] = y0;
  ctx[b] = y1;
  ctx[c] = y2;
  ctx[d] = y3;
}

inline static void Hacl_Symmetric_Salsa20_salsa20_row_round(uint32_t *ctx)
{
  Hacl_Symmetric_Salsa20_salsa20_quarter_round(ctx,
    (uint32_t )0,
    (uint32_t )1,
    (uint32_t )2,
    (uint32_t )3);
  Hacl_Symmetric_Salsa20_salsa20_quarter_round(ctx,
    (uint32_t )5,
    (uint32_t )6,
    (uint32_t )7,
    (uint32_t )4);
  Hacl_Symmetric_Salsa20_salsa20_quarter_round(ctx,
    (uint32_t )10,
    (uint32_t )11,
    (uint32_t )8,
    (uint32_t )9);
  Hacl_Symmetric_Salsa20_salsa20_quarter_round(ctx,
    (uint32_t )15,
    (uint32_t )12,
    (uint32_t )13,
    (uint32_t )14);
  return;
}

inline static void Hacl_Symmetric_Salsa20_salsa20_column_round(uint32_t *ctx)
{
  Hacl_Symmetric_Salsa20_salsa20_quarter_round(ctx,
    (uint32_t )0,
    (uint32_t )4,
    (uint32_t )8,
    (uint32_t )12);
  Hacl_Symmetric_Salsa20_salsa20_quarter_round(ctx,
    (uint32_t )5,
    (uint32_t )9,
    (uint32_t )13,
    (uint32_t )1);
  Hacl_Symmetric_Salsa20_salsa20_quarter_round(ctx,
    (uint32_t )10,
    (uint32_t )14,
    (uint32_t )2,
    (uint32_t )6);
  Hacl_Symmetric_Salsa20_salsa20_quarter_round(ctx,
    (uint32_t )15,
    (uint32_t )3,
    (uint32_t )7,
    (uint32_t )11);
  return;
}

inline static void Hacl_Symmetric_Salsa20_salsa20_double_round_10(uint32_t *ctx)
{
  Hacl_Symmetric_Salsa20_salsa20_column_round(ctx);
  Hacl_Symmetric_Salsa20_salsa20_row_round(ctx);
  Hacl_Symmetric_Salsa20_salsa20_column_round(ctx);
  Hacl_Symmetric_Salsa20_salsa20_row_round(ctx);
  Hacl_Symmetric_Salsa20_salsa20_column_round(ctx);
  Hacl_Symmetric_Salsa20_salsa20_row_round(ctx);
  Hacl_Symmetric_Salsa20_salsa20_column_round(ctx);
  Hacl_Symmetric_Salsa20_salsa20_row_round(ctx);
  Hacl_Symmetric_Salsa20_salsa20_column_round(ctx);
  Hacl_Symmetric_Salsa20_salsa20_row_round(ctx);
  Hacl_Symmetric_Salsa20_salsa20_column_round(ctx);
  Hacl_Symmetric_Salsa20_salsa20_row_round(ctx);
  Hacl_Symmetric_Salsa20_salsa20_column_round(ctx);
  Hacl_Symmetric_Salsa20_salsa20_row_round(ctx);
  Hacl_Symmetric_Salsa20_salsa20_column_round(ctx);
  Hacl_Symmetric_Salsa20_salsa20_row_round(ctx);
  Hacl_Symmetric_Salsa20_salsa20_column_round(ctx);
  Hacl_Symmetric_Salsa20_salsa20_row_round(ctx);
  Hacl_Symmetric_Salsa20_salsa20_column_round(ctx);
  Hacl_Symmetric_Salsa20_salsa20_row_round(ctx);
  return;
}

inline static void
Hacl_Symmetric_Salsa20_salsa20_init(uint32_t *ctx, uint8_t *key, uint8_t *n, uint64_t ic)
{
  ctx[0] = (uint32_t )0x61707865;
  ctx[5] = (uint32_t )0x3320646e;
  ctx[10] = (uint32_t )0x79622d32;
  ctx[15] = (uint32_t )0x6b206574;
  uint8_t *x0 = key;
  uint32_t
  _0_33 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x0)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  ctx[1] = _0_33;
  uint8_t *x00 = key + (uint32_t )4;
  uint32_t
  _0_34 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x00)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  ctx[2] = _0_34;
  uint8_t *x01 = key + (uint32_t )8;
  uint32_t
  _0_35 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x01)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  ctx[3] = _0_35;
  uint8_t *x02 = key + (uint32_t )12;
  uint32_t
  _0_36 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x02)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  ctx[4] = _0_36;
  uint8_t *x03 = key + (uint32_t )16;
  uint32_t
  _0_37 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x03)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  ctx[11] = _0_37;
  uint8_t *x04 = key + (uint32_t )20;
  uint32_t
  _0_38 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x04)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  ctx[12] = _0_38;
  uint8_t *x05 = key + (uint32_t )24;
  uint32_t
  _0_39 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x05)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  ctx[13] = _0_39;
  uint8_t *x06 = key + (uint32_t )28;
  uint32_t
  _0_40 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x06)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  ctx[14] = _0_40;
  uint8_t *x07 = n;
  uint32_t
  _0_41 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x07)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  ctx[6] = _0_41;
  uint8_t *x08 = n + (uint32_t )4;
  uint32_t
  _0_42 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x08)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  ctx[7] = _0_42;
  uint64_t ic0 = ic;
  ctx[8] = (uint32_t )ic0;
  ctx[9] = (uint32_t )(ic0 >> (uint32_t )32);
}

inline static void Hacl_Symmetric_Salsa20_salsa20(uint32_t *output, uint32_t *ctx)
{
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
  output[0] = j0;
  output[1] = j1;
  output[2] = j2;
  output[3] = j3;
  output[4] = j4;
  output[5] = j5;
  output[6] = j6;
  output[7] = j7;
  output[8] = j8;
  output[9] = j9;
  output[10] = j10;
  output[11] = j11;
  output[12] = j12;
  output[13] = j13;
  output[14] = j14;
  output[15] = j15;
  Hacl_Symmetric_Salsa20_salsa20_double_round_10(output);
  uint32_t x00 = output[0];
  uint32_t x16 = output[1];
  uint32_t x20 = output[2];
  uint32_t x30 = output[3];
  uint32_t x40 = output[4];
  uint32_t x50 = output[5];
  uint32_t x60 = output[6];
  uint32_t x70 = output[7];
  uint32_t x80 = output[8];
  uint32_t x90 = output[9];
  uint32_t x100 = output[10];
  uint32_t x110 = output[11];
  uint32_t x120 = output[12];
  uint32_t x130 = output[13];
  uint32_t x140 = output[14];
  uint32_t x150 = output[15];
  uint32_t x0 = x00 + j0;
  uint32_t x1 = x16 + j1;
  uint32_t x2 = x20 + j2;
  uint32_t x3 = x30 + j3;
  uint32_t x4 = x40 + j4;
  uint32_t x5 = x50 + j5;
  uint32_t x6 = x60 + j6;
  uint32_t x7 = x70 + j7;
  uint32_t x8 = x80 + j8;
  uint32_t x9 = x90 + j9;
  uint32_t x10 = x100 + j10;
  uint32_t x11 = x110 + j11;
  uint32_t x12 = x120 + j12;
  uint32_t x13 = x130 + j13;
  uint32_t x14 = x140 + j14;
  uint32_t x15 = x150 + j15;
  output[0] = x0;
  output[1] = x1;
  output[2] = x2;
  output[3] = x3;
  output[4] = x4;
  output[5] = x5;
  output[6] = x6;
  output[7] = x7;
  output[8] = x8;
  output[9] = x9;
  output[10] = x10;
  output[11] = x11;
  output[12] = x12;
  output[13] = x13;
  output[14] = x14;
  output[15] = x15;
}

inline static void Hacl_Symmetric_Salsa20_xor_(uint8_t *c, uint8_t *m, uint32_t *b)
{
  uint8_t *x00 = m;
  uint32_t
  m0 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x00)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  uint8_t *x01 = m + (uint32_t )4;
  uint32_t
  m1 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x01)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  uint8_t *x02 = m + (uint32_t )8;
  uint32_t
  m2 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x02)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  uint8_t *x03 = m + (uint32_t )12;
  uint32_t
  m3 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x03)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  uint8_t *x04 = m + (uint32_t )16;
  uint32_t
  m4 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x04)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  uint8_t *x05 = m + (uint32_t )20;
  uint32_t
  m5 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x05)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  uint8_t *x06 = m + (uint32_t )24;
  uint32_t
  m6 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x06)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  uint8_t *x07 = m + (uint32_t )28;
  uint32_t
  m7 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x07)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  uint8_t *x08 = m + (uint32_t )32;
  uint32_t
  m8 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x08)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  uint8_t *x09 = m + (uint32_t )36;
  uint32_t
  m9 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x09)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  uint8_t *x010 = m + (uint32_t )40;
  uint32_t
  m10 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x010)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  uint8_t *x011 = m + (uint32_t )44;
  uint32_t
  m11 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x011)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  uint8_t *x012 = m + (uint32_t )48;
  uint32_t
  m12 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x012)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  uint8_t *x013 = m + (uint32_t )52;
  uint32_t
  m13 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x013)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  uint8_t *x014 = m + (uint32_t )56;
  uint32_t
  m14 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x014)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  uint8_t *x015 = m + (uint32_t )60;
  uint32_t
  m15 =
    /* start inlining Hacl.Endianness.hload32_le */
      /* start inlining Hacl.Endianness.load32_le */
        load32_le(x015)
      /* end inlining Hacl.Endianness.load32_le */
    /* end inlining Hacl.Endianness.hload32_le */;
  uint32_t b0 = b[0];
  uint32_t b1 = b[1];
  uint32_t b2 = b[2];
  uint32_t b3 = b[3];
  uint32_t b4 = b[4];
  uint32_t b5 = b[5];
  uint32_t b6 = b[6];
  uint32_t b7 = b[7];
  uint32_t b8 = b[8];
  uint32_t b9 = b[9];
  uint32_t b10 = b[10];
  uint32_t b11 = b[11];
  uint32_t b12 = b[12];
  uint32_t b13 = b[13];
  uint32_t b14 = b[14];
  uint32_t b15 = b[15];
  uint32_t c0 = m0 ^ b0;
  uint32_t c1 = m1 ^ b1;
  uint32_t c2 = m2 ^ b2;
  uint32_t c3 = m3 ^ b3;
  uint32_t c4 = m4 ^ b4;
  uint32_t c5 = m5 ^ b5;
  uint32_t c6 = m6 ^ b6;
  uint32_t c7 = m7 ^ b7;
  uint32_t c8 = m8 ^ b8;
  uint32_t c9 = m9 ^ b9;
  uint32_t c10 = m10 ^ b10;
  uint32_t c11 = m11 ^ b11;
  uint32_t c12 = m12 ^ b12;
  uint32_t c13 = m13 ^ b13;
  uint32_t c14 = m14 ^ b14;
  uint32_t c15 = m15 ^ b15;
  uint8_t *x0 = c;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x0, c0);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint8_t *x016 = c + (uint32_t )4;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x016, c1);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint8_t *x017 = c + (uint32_t )8;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x017, c2);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint8_t *x018 = c + (uint32_t )12;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x018, c3);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint8_t *x019 = c + (uint32_t )16;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x019, c4);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint8_t *x020 = c + (uint32_t )20;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x020, c5);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint8_t *x021 = c + (uint32_t )24;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x021, c6);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint8_t *x022 = c + (uint32_t )28;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x022, c7);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint8_t *x023 = c + (uint32_t )32;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x023, c8);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint8_t *x024 = c + (uint32_t )36;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x024, c9);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint8_t *x025 = c + (uint32_t )40;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x025, c10);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint8_t *x026 = c + (uint32_t )44;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x026, c11);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint8_t *x027 = c + (uint32_t )48;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x027, c12);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint8_t *x028 = c + (uint32_t )52;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x028, c13);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint8_t *x029 = c + (uint32_t )56;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x029, c14);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.hstore32_le */
  uint8_t *x030 = c + (uint32_t )60;
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x030, c15);
  return;
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
}

inline static void Hacl_Symmetric_Salsa20_salsa20_xor(uint8_t *c, uint8_t *m, uint32_t *ctx)
{
  uint32_t block[16] = { 0 };
  Hacl_Symmetric_Salsa20_salsa20(block, ctx);
  Hacl_Symmetric_Salsa20_xor_(c, m, block);
}

inline static uint64_t Hacl_Symmetric_Salsa20_incr_counter(uint32_t *ctx, uint64_t ctr)
{
  uint64_t ctr1 = ctr + (uint64_t )1;
  uint64_t sctr1 = ctr1;
  ctx[8] = (uint32_t )sctr1;
  ctx[9] = (uint32_t )(sctr1 >> (uint32_t )32);
  return ctr1;
}

inline static uint64_t
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic_loop(
  uint8_t *c,
  uint8_t *m,
  uint32_t *ctx,
  uint64_t ctr,
  uint64_t mlen
)
{
  if (mlen < (uint64_t )64)
    return mlen;
  else
  {
    Hacl_Symmetric_Salsa20_salsa20_xor(c, m, ctx);
    uint64_t ctr1 = Hacl_Symmetric_Salsa20_incr_counter(ctx, ctr);
    uint64_t mlen0 = mlen - (uint64_t )64;
    uint8_t *c_ = c + (uint32_t )64;
    uint8_t *m_ = m + (uint32_t )64;
    return Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic_loop(c_, m_, ctx, ctr1, mlen0);
  }
}

inline static void
Hacl_Symmetric_Salsa20_xor_bytes(uint8_t *x, uint8_t *y, uint32_t *b, uint32_t i, uint32_t len)
{
  uint32_t curr = i * (uint32_t )4;
  uint32_t r = len - curr;
  if (r == (uint32_t )0)
    return;
  else if (r == (uint32_t )1)
  {
    uint32_t bi = b[i];
    uint8_t y0 = y[curr];
    uint8_t b0 = (uint8_t )bi;
    x[curr] = y0 ^ b0;
  }
  else if (r == (uint32_t )2)
  {
    uint32_t bi = b[i];
    uint8_t y0 = y[curr];
    uint8_t y1 = y[curr + (uint32_t )1];
    uint8_t b0 = (uint8_t )bi;
    uint8_t b1 = (uint8_t )(bi >> (uint32_t )8);
    x[curr] = y0 ^ b0;
    x[curr + (uint32_t )1] = y1 ^ b1;
  }
  else if (r == (uint32_t )3)
  {
    uint32_t bi = b[i];
    uint8_t y0 = y[curr];
    uint8_t y1 = y[curr + (uint32_t )1];
    uint8_t y2 = y[curr + (uint32_t )2];
    uint8_t b0 = (uint8_t )bi;
    uint8_t b1 = (uint8_t )(bi >> (uint32_t )8);
    uint8_t b2 = (uint8_t )(bi >> (uint32_t )16);
    x[curr] = y0 ^ b0;
    x[curr + (uint32_t )1] = y1 ^ b1;
    x[curr + (uint32_t )2] = y2 ^ b2;
  }
  else
  {
    uint32_t ip1 = i + (uint32_t )1;
    uint32_t bi = b[i];
    uint8_t y0 = y[curr];
    uint8_t y1 = y[curr + (uint32_t )1];
    uint8_t y2 = y[curr + (uint32_t )2];
    uint8_t y3 = y[curr + (uint32_t )3];
    uint8_t b0 = (uint8_t )bi;
    uint8_t b1 = (uint8_t )(bi >> (uint32_t )8);
    uint8_t b2 = (uint8_t )(bi >> (uint32_t )16);
    uint8_t b3 = (uint8_t )(bi >> (uint32_t )24);
    x[curr] = y0 ^ b0;
    x[curr + (uint32_t )1] = y1 ^ b1;
    x[curr + (uint32_t )2] = y2 ^ b2;
    x[curr + (uint32_t )3] = y3 ^ b3;
    Hacl_Symmetric_Salsa20_xor_bytes(x, y, b, ip1, len);
    return;
  }
}

inline static void
Hacl_Symmetric_Salsa20_salsa20_xor_partial(uint8_t *c, uint8_t *m, uint32_t *ctx, uint32_t len)
{
  uint32_t block[16] = { 0 };
  Hacl_Symmetric_Salsa20_salsa20(block, ctx);
  Hacl_Symmetric_Salsa20_xor_bytes(c, m, block, (uint32_t )0, len);
}

inline static void
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic_(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint64_t ic,
  uint8_t *k
)
{
  uint32_t ctx[16] = { 0 };
  Hacl_Symmetric_Salsa20_salsa20_init(ctx, k, n, ic);
  uint64_t
  uu____4239 = Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic_loop(c, m, ctx, ic, mlen);
  uint32_t mlen_ = (uint32_t )(mlen & (uint64_t )63);
  uint32_t off = (uint32_t )mlen - mlen_;
  if (mlen_ >= (uint32_t )0)
    Hacl_Symmetric_Salsa20_salsa20_xor_partial(c + off, m + off, ctx, mlen_);
}

inline static void
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint64_t ic,
  uint8_t *k
)
{
  if (mlen == (uint64_t )0)
    return;
  else
  {
    Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic_(c, m, mlen, n, ic, k);
    return;
  }
}

inline static void Hacl_Symmetric_Salsa20_salsa20_store(uint8_t *c, uint32_t *ctx)
{
  uint32_t b[16] = { 0 };
  Hacl_Symmetric_Salsa20_salsa20(b, ctx);
  uint32_t _0_43 = b[0];
  uint8_t *x00 = c;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x00, _0_43);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint32_t _0_44 = b[1];
  uint8_t *x01 = c + (uint32_t )4;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x01, _0_44);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint32_t _0_45 = b[2];
  uint8_t *x02 = c + (uint32_t )8;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x02, _0_45);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint32_t _0_46 = b[3];
  uint8_t *x03 = c + (uint32_t )12;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x03, _0_46);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint32_t _0_47 = b[4];
  uint8_t *x04 = c + (uint32_t )16;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x04, _0_47);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint32_t _0_48 = b[5];
  uint8_t *x05 = c + (uint32_t )20;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x05, _0_48);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint32_t _0_49 = b[6];
  uint8_t *x06 = c + (uint32_t )24;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x06, _0_49);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint32_t _0_50 = b[7];
  uint8_t *x07 = c + (uint32_t )28;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x07, _0_50);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint32_t _0_51 = b[8];
  uint8_t *x08 = c + (uint32_t )32;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x08, _0_51);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint32_t _0_52 = b[9];
  uint8_t *x09 = c + (uint32_t )36;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x09, _0_52);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint32_t _0_53 = b[10];
  uint8_t *x010 = c + (uint32_t )40;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x010, _0_53);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint32_t _0_54 = b[11];
  uint8_t *x011 = c + (uint32_t )44;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x011, _0_54);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint32_t _0_55 = b[12];
  uint8_t *x012 = c + (uint32_t )48;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x012, _0_55);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint32_t _0_56 = b[13];
  uint8_t *x013 = c + (uint32_t )52;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x013, _0_56);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint32_t _0_57 = b[14];
  uint8_t *x014 = c + (uint32_t )56;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x014, _0_57);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
  uint32_t _0_58 = b[15];
  uint8_t *x0 = c + (uint32_t )60;
  /* start inlining Hacl.Endianness.hstore32_le */
  /* start inlining Hacl.Endianness.store32_le */
  store32_le(x0, _0_58);
  /* end inlining Hacl.Endianness.store32_le */
  /* end inlining Hacl.Endianness.hstore32_le */
}

inline static uint64_t
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_loop(
  uint8_t *c,
  uint64_t clen,
  uint32_t *ctx,
  uint64_t ctr
)
{
  if (clen < (uint64_t )64)
    return clen;
  else
  {
    Hacl_Symmetric_Salsa20_salsa20_store(c, ctx);
    uint64_t ctr1 = Hacl_Symmetric_Salsa20_incr_counter(ctx, ctr);
    uint64_t clen0 = clen - (uint64_t )64;
    uint8_t *c0 = c + (uint32_t )64;
    return Hacl_Symmetric_Salsa20_crypto_stream_salsa20_loop(c0, clen0, ctx, ctr1);
  }
}

inline static void
Hacl_Symmetric_Salsa20_store_bytes(uint8_t *x, uint32_t *b, uint32_t i, uint32_t len)
{
  uint32_t curr = i * (uint32_t )4;
  uint32_t r = len - curr;
  if (r == (uint32_t )0)
    return;
  else if (r == (uint32_t )1)
  {
    uint32_t bi = b[i];
    uint8_t b0 = (uint8_t )bi;
    x[curr] = b0;
  }
  else if (r == (uint32_t )2)
  {
    uint32_t bi = b[i];
    uint8_t b0 = (uint8_t )bi;
    uint8_t b1 = (uint8_t )(bi >> (uint32_t )8);
    x[curr] = b0;
    x[curr + (uint32_t )1] = b1;
  }
  else if (r == (uint32_t )3)
  {
    uint32_t bi = b[i];
    uint8_t b0 = (uint8_t )bi;
    uint8_t b1 = (uint8_t )(bi >> (uint32_t )8);
    uint8_t b2 = (uint8_t )(bi >> (uint32_t )16);
    x[curr] = b0;
    x[curr + (uint32_t )1] = b1;
    x[curr + (uint32_t )2] = b2;
  }
  else
  {
    uint32_t bi = b[i];
    uint8_t b0 = (uint8_t )bi;
    uint8_t b1 = (uint8_t )(bi >> (uint32_t )8);
    uint8_t b2 = (uint8_t )(bi >> (uint32_t )16);
    uint8_t b3 = (uint8_t )(bi >> (uint32_t )24);
    x[curr] = b0;
    x[curr + (uint32_t )1] = b1;
    x[curr + (uint32_t )2] = b2;
    x[curr + (uint32_t )3] = b3;
    Hacl_Symmetric_Salsa20_store_bytes(x, b, i + (uint32_t )1, len);
    return;
  }
}

inline static void
Hacl_Symmetric_Salsa20_salsa20_store_partial(uint8_t *c, uint32_t *ctx, uint32_t len)
{
  uint32_t b[16] = { 0 };
  Hacl_Symmetric_Salsa20_salsa20(b, ctx);
  Hacl_Symmetric_Salsa20_store_bytes(c, b, (uint32_t )0, len);
}

inline static void
Hacl_Symmetric_Salsa20_crypto_stream_salsa20(uint8_t *c, uint64_t clen, uint8_t *n, uint8_t *k)
{
  if (clen == (uint64_t )0)
  {
    
  }
  else
  {
    uint32_t clen_ = (uint32_t )(clen & (uint64_t )63);
    uint32_t off = (uint32_t )clen - clen_;
    uint32_t ctx[16] = { 0 };
    Hacl_Symmetric_Salsa20_salsa20_init(ctx, k, n, (uint64_t )0);
    uint64_t
    uu____4982 = Hacl_Symmetric_Salsa20_crypto_stream_salsa20_loop(c, clen, ctx, (uint64_t )0);
    if (clen_ >= (uint32_t )0)
      Hacl_Symmetric_Salsa20_salsa20_store_partial(c + off, ctx, clen_);
  }
}

void
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic(c, m, mlen, n, (uint64_t )0, k);
  return;
}

void
Salsa20_crypto_stream_salsa20_xor_ic(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint64_t ic,
  uint8_t *k
)
{
  Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic(c, m, mlen, n, ic, k);
  return;
}

void Salsa20_crypto_stream_salsa20(uint8_t *c, uint64_t clen, uint8_t *n, uint8_t *k)
{
  Hacl_Symmetric_Salsa20_crypto_stream_salsa20(c, clen, n, k);
  return;
}

void
Salsa20_crypto_stream_salsa20_xor(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor(c, m, mlen, n, k);
  return;
}

