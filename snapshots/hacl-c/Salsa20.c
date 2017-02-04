#include "Salsa20.h"

inline static uint32_t Hacl_Symmetric_Salsa20_rol32(uint32_t a, uint32_t s)
{
  return a << s | a >> (uint32_t )32 - s;
}

inline static uint32_t Hacl_Symmetric_Salsa20_load32_le(uint8_t *k)
{
  return load32_le(k);
}

inline static void Hacl_Symmetric_Salsa20_store32_le(uint8_t *k, uint32_t x)
{
  store32_le(k, x);
  return;
}

inline static void
Hacl_Symmetric_Salsa20_crypto_core_salsa20_quarter_round(
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

inline static void Hacl_Symmetric_Salsa20_crypto_core_salsa20_row_round(uint32_t *ctx)
{
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_quarter_round(ctx,
    (uint32_t )0,
    (uint32_t )1,
    (uint32_t )2,
    (uint32_t )3);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_quarter_round(ctx,
    (uint32_t )5,
    (uint32_t )6,
    (uint32_t )7,
    (uint32_t )4);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_quarter_round(ctx,
    (uint32_t )10,
    (uint32_t )11,
    (uint32_t )8,
    (uint32_t )9);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_quarter_round(ctx,
    (uint32_t )15,
    (uint32_t )12,
    (uint32_t )13,
    (uint32_t )14);
  return;
}

inline static void Hacl_Symmetric_Salsa20_crypto_core_salsa20_column_round(uint32_t *ctx)
{
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_quarter_round(ctx,
    (uint32_t )0,
    (uint32_t )4,
    (uint32_t )8,
    (uint32_t )12);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_quarter_round(ctx,
    (uint32_t )5,
    (uint32_t )9,
    (uint32_t )13,
    (uint32_t )1);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_quarter_round(ctx,
    (uint32_t )10,
    (uint32_t )14,
    (uint32_t )2,
    (uint32_t )6);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_quarter_round(ctx,
    (uint32_t )15,
    (uint32_t )3,
    (uint32_t )7,
    (uint32_t )11);
  return;
}

static void Hacl_Symmetric_Salsa20_crypto_core_salsa20_double_round_10(uint32_t *ctx)
{
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_column_round(ctx);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_row_round(ctx);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_column_round(ctx);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_row_round(ctx);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_column_round(ctx);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_row_round(ctx);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_column_round(ctx);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_row_round(ctx);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_column_round(ctx);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_row_round(ctx);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_column_round(ctx);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_row_round(ctx);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_column_round(ctx);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_row_round(ctx);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_column_round(ctx);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_row_round(ctx);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_column_round(ctx);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_row_round(ctx);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_column_round(ctx);
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_row_round(ctx);
  return;
}

static void
Hacl_Symmetric_Salsa20_crypto_core_salsa20(uint8_t *output, uint8_t *input, uint8_t *key)
{
  uint32_t ctx[16] = { 0 };
  ctx[0] = (uint32_t )0x61707865;
  ctx[5] = (uint32_t )0x3320646e;
  ctx[10] = (uint32_t )0x79622d32;
  ctx[15] = (uint32_t )0x6b206574;
  uint32_t _0_33 = Hacl_Symmetric_Salsa20_load32_le(key);
  ctx[1] = _0_33;
  uint32_t _0_34 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )4);
  ctx[2] = _0_34;
  uint32_t _0_35 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )8);
  ctx[3] = _0_35;
  uint32_t _0_36 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )12);
  ctx[4] = _0_36;
  uint32_t _0_37 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )16);
  ctx[11] = _0_37;
  uint32_t _0_38 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )20);
  ctx[12] = _0_38;
  uint32_t _0_39 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )24);
  ctx[13] = _0_39;
  uint32_t _0_40 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )28);
  ctx[14] = _0_40;
  uint32_t _0_41 = Hacl_Symmetric_Salsa20_load32_le(input);
  ctx[6] = _0_41;
  uint32_t _0_42 = Hacl_Symmetric_Salsa20_load32_le(input + (uint32_t )4);
  ctx[7] = _0_42;
  uint32_t _0_43 = Hacl_Symmetric_Salsa20_load32_le(input + (uint32_t )8);
  ctx[8] = _0_43;
  uint32_t _0_44 = Hacl_Symmetric_Salsa20_load32_le(input + (uint32_t )12);
  ctx[9] = _0_44;
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
  Hacl_Symmetric_Salsa20_crypto_core_salsa20_double_round_10(ctx);
  uint32_t x00 = ctx[0];
  uint32_t x16 = ctx[1];
  uint32_t x20 = ctx[2];
  uint32_t x30 = ctx[3];
  uint32_t x40 = ctx[4];
  uint32_t x50 = ctx[5];
  uint32_t x60 = ctx[6];
  uint32_t x70 = ctx[7];
  uint32_t x80 = ctx[8];
  uint32_t x90 = ctx[9];
  uint32_t x100 = ctx[10];
  uint32_t x110 = ctx[11];
  uint32_t x120 = ctx[12];
  uint32_t x130 = ctx[13];
  uint32_t x140 = ctx[14];
  uint32_t x150 = ctx[15];
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
  Hacl_Symmetric_Salsa20_store32_le(output, x0);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )4, x1);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )8, x2);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )12, x3);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )16, x4);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )20, x5);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )24, x6);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )28, x7);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )32, x8);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )36, x9);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )40, x10);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )44, x11);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )48, x12);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )52, x13);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )56, x14);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )60, x15);
}

inline static void Hacl_Symmetric_Salsa20_xor_(uint8_t *c, uint8_t *m, uint8_t *block)
{
  FStar_UInt128_t m0 = load128(m);
  FStar_UInt128_t m1 = load128(m + (uint32_t )16);
  FStar_UInt128_t m2 = load128(m + (uint32_t )32);
  FStar_UInt128_t m3 = load128(m + (uint32_t )48);
  FStar_UInt128_t b0 = load128(block);
  FStar_UInt128_t b1 = load128(block + (uint32_t )16);
  FStar_UInt128_t b2 = load128(block + (uint32_t )32);
  FStar_UInt128_t b3 = load128(block + (uint32_t )48);
  FStar_UInt128_t c0 = FStar_UInt128_logxor(m0, b0);
  FStar_UInt128_t c1 = FStar_UInt128_logxor(m1, b1);
  FStar_UInt128_t c2 = FStar_UInt128_logxor(m2, b2);
  FStar_UInt128_t c3 = FStar_UInt128_logxor(m3, b3);
  store128(c, c0);
  store128(c + (uint32_t )16, c1);
  store128(c + (uint32_t )32, c2);
  store128(c + (uint32_t )48, c3);
  return;
}

inline static uint64_t
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic_loop(
  uint8_t *c,
  uint8_t *m,
  uint8_t *block,
  uint8_t *input,
  uint8_t *kcopy,
  uint64_t mlen
)
{
  if (mlen < (uint64_t )64)
    return mlen;
  else
  {
    Hacl_Symmetric_Salsa20_crypto_core_salsa20(block, input, kcopy);
    Hacl_Symmetric_Salsa20_xor_(c, m, block);
    uint8_t i8 = input[8];
    uint8_t i9 = input[9];
    uint8_t i10 = input[10];
    uint8_t i11 = input[11];
    uint8_t i12 = input[12];
    uint8_t i13 = input[13];
    uint8_t i14 = input[14];
    uint8_t i15 = input[15];
    uint64_t
    u =
      (uint64_t )i8
      + ((uint64_t )i9 << (uint32_t )8)
      + ((uint64_t )i10 << (uint32_t )16)
      + ((uint64_t )i11 << (uint32_t )24)
      + ((uint64_t )i12 << (uint32_t )32)
      + ((uint64_t )i13 << (uint32_t )40)
      + ((uint64_t )i14 << (uint32_t )48)
      + ((uint64_t )i15 << (uint32_t )56)
      + (uint64_t )1;
    input[8] = (uint8_t )u;
    input[9] = (uint8_t )(u >> (uint32_t )8);
    input[10] = (uint8_t )(u >> (uint32_t )16);
    input[11] = (uint8_t )(u >> (uint32_t )24);
    input[12] = (uint8_t )(u >> (uint32_t )32);
    input[13] = (uint8_t )(u >> (uint32_t )40);
    input[14] = (uint8_t )(u >> (uint32_t )48);
    input[15] = (uint8_t )(u >> (uint32_t )56);
    uint64_t mlen0 = mlen - (uint64_t )64;
    uint8_t *c_ = c + (uint32_t )64;
    uint8_t *m0 = m + (uint32_t )64;
    uint64_t
    res =
      Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic_loop(c_,
        m0,
        block,
        input,
        kcopy,
        mlen0);
    return res;
  }
}

inline static void
Hacl_Symmetric_Salsa20_xor_bytes(uint8_t *x, uint8_t *y, uint8_t *z, uint32_t len)
{
  if (len == (uint32_t )0)
    return;
  else
  {
    uint32_t i = len - (uint32_t )1;
    uint8_t yi = y[i];
    uint8_t zi = z[i];
    x[i] = yi ^ zi;
    Hacl_Symmetric_Salsa20_xor_bytes(x, y, z, i);
    return;
  }
}

inline static void
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic__(
  uint8_t *n,
  uint64_t ic,
  uint8_t *k,
  uint8_t *local_state
)
{
  uint8_t *input = local_state;
  uint8_t *block = local_state + (uint32_t )16;
  uint8_t *kcopy = local_state + (uint32_t )80;
  uint8_t k0 = k[0];
  uint8_t k1 = k[1];
  uint8_t k2 = k[2];
  uint8_t k3 = k[3];
  uint8_t k4 = k[4];
  uint8_t k5 = k[5];
  uint8_t k6 = k[6];
  uint8_t k7 = k[7];
  uint8_t k8 = k[8];
  uint8_t k9 = k[9];
  uint8_t k10 = k[10];
  uint8_t k11 = k[11];
  uint8_t k12 = k[12];
  uint8_t k13 = k[13];
  uint8_t k14 = k[14];
  uint8_t k15 = k[15];
  uint8_t k16 = k[16];
  uint8_t k17 = k[17];
  uint8_t k18 = k[18];
  uint8_t k19 = k[19];
  uint8_t k20 = k[20];
  uint8_t k21 = k[21];
  uint8_t k22 = k[22];
  uint8_t k23 = k[23];
  uint8_t k24 = k[24];
  uint8_t k25 = k[25];
  uint8_t k26 = k[26];
  uint8_t k27 = k[27];
  uint8_t k28 = k[28];
  uint8_t k29 = k[29];
  uint8_t k30 = k[30];
  uint8_t k31 = k[31];
  uint8_t n0 = n[0];
  uint8_t n1 = n[1];
  uint8_t n2 = n[2];
  uint8_t n3 = n[3];
  uint8_t n4 = n[4];
  uint8_t n5 = n[5];
  uint8_t n6 = n[6];
  uint8_t n7 = n[7];
  kcopy[0] = k0;
  kcopy[1] = k1;
  kcopy[2] = k2;
  kcopy[3] = k3;
  kcopy[4] = k4;
  kcopy[5] = k5;
  kcopy[6] = k6;
  kcopy[7] = k7;
  kcopy[8] = k8;
  kcopy[9] = k9;
  kcopy[10] = k10;
  kcopy[11] = k11;
  kcopy[12] = k12;
  kcopy[13] = k13;
  kcopy[14] = k14;
  kcopy[15] = k15;
  kcopy[16] = k16;
  kcopy[17] = k17;
  kcopy[18] = k18;
  kcopy[19] = k19;
  kcopy[20] = k20;
  kcopy[21] = k21;
  kcopy[22] = k22;
  kcopy[23] = k23;
  kcopy[24] = k24;
  kcopy[25] = k25;
  kcopy[26] = k26;
  kcopy[27] = k27;
  kcopy[28] = k28;
  kcopy[29] = k29;
  kcopy[30] = k30;
  kcopy[31] = k31;
  input[0] = n0;
  input[1] = n1;
  input[2] = n2;
  input[3] = n3;
  input[4] = n4;
  input[5] = n5;
  input[6] = n6;
  input[7] = n7;
  input[8] = (uint8_t )ic;
  input[9] = (uint8_t )(ic >> (uint32_t )8);
  input[10] = (uint8_t )(ic >> (uint32_t )16);
  input[11] = (uint8_t )(ic >> (uint32_t )24);
  input[12] = (uint8_t )(ic >> (uint32_t )32);
  input[13] = (uint8_t )(ic >> (uint32_t )40);
  input[14] = (uint8_t )(ic >> (uint32_t )48);
  input[15] = (uint8_t )(ic >> (uint32_t )56);
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
  uint8_t zero = (uint8_t )0;
  uint8_t local_state[112];
  for (uintmax_t i = 0; i < (uint32_t )112; ++i)
    local_state[i] = zero;
  uint8_t *input = local_state;
  uint8_t *block = local_state + (uint32_t )16;
  uint8_t *kcopy = local_state + (uint32_t )80;
  Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic__(n, ic, k, local_state);
  uint64_t
  uu____1524 =
    Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic_loop(c,
      m,
      block,
      input,
      kcopy,
      mlen);
  uint32_t mlen_ = (uint32_t )(mlen & (uint64_t )63);
  uint32_t off = (uint32_t )mlen - mlen_;
  if (mlen_ >= (uint32_t )0)
  {
    Hacl_Symmetric_Salsa20_crypto_core_salsa20(block, input, kcopy);
    Hacl_Symmetric_Salsa20_xor_bytes(c + off, m + off, block, mlen_);
  }
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

inline static uint64_t
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_loop(
  uint8_t *c,
  uint64_t clen,
  uint8_t *n,
  uint8_t *k,
  uint8_t *input
)
{
  if (clen < (uint64_t )64)
    return clen;
  else
  {
    Hacl_Symmetric_Salsa20_crypto_core_salsa20(c, input, k);
    uint8_t i8 = input[8];
    uint8_t i9 = input[9];
    uint8_t i10 = input[10];
    uint8_t i11 = input[11];
    uint8_t i12 = input[12];
    uint8_t i13 = input[13];
    uint8_t i14 = input[14];
    uint8_t i15 = input[15];
    uint64_t
    u =
      (uint64_t )i8
      + ((uint64_t )i9 << (uint32_t )8)
      + ((uint64_t )i10 << (uint32_t )16)
      + ((uint64_t )i11 << (uint32_t )24)
      + ((uint64_t )i12 << (uint32_t )32)
      + ((uint64_t )i13 << (uint32_t )40)
      + ((uint64_t )i14 << (uint32_t )48)
      + ((uint64_t )i15 << (uint32_t )56)
      + (uint64_t )1;
    input[8] = (uint8_t )u;
    input[9] = (uint8_t )(u >> (uint32_t )8);
    input[10] = (uint8_t )(u >> (uint32_t )16);
    input[11] = (uint8_t )(u >> (uint32_t )24);
    input[12] = (uint8_t )(u >> (uint32_t )32);
    input[13] = (uint8_t )(u >> (uint32_t )40);
    input[14] = (uint8_t )(u >> (uint32_t )48);
    input[15] = (uint8_t )(u >> (uint32_t )56);
    uint64_t clen0 = clen - (uint64_t )64;
    uint8_t *c0 = c + (uint32_t )64;
    return Hacl_Symmetric_Salsa20_crypto_stream_salsa20_loop(c0, clen0, n, k, input);
  }
}

inline static void
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_(uint8_t *n, uint8_t *k, uint8_t *local_state)
{
  uint8_t zero = (uint8_t )0;
  uint8_t *input = local_state;
  uint8_t *block = local_state + (uint32_t )16;
  uint8_t *kcopy = local_state + (uint32_t )80;
  uint8_t k0 = k[0];
  uint8_t k1 = k[1];
  uint8_t k2 = k[2];
  uint8_t k3 = k[3];
  uint8_t k4 = k[4];
  uint8_t k5 = k[5];
  uint8_t k6 = k[6];
  uint8_t k7 = k[7];
  uint8_t k8 = k[8];
  uint8_t k9 = k[9];
  uint8_t k10 = k[10];
  uint8_t k11 = k[11];
  uint8_t k12 = k[12];
  uint8_t k13 = k[13];
  uint8_t k14 = k[14];
  uint8_t k15 = k[15];
  uint8_t k16 = k[16];
  uint8_t k17 = k[17];
  uint8_t k18 = k[18];
  uint8_t k19 = k[19];
  uint8_t k20 = k[20];
  uint8_t k21 = k[21];
  uint8_t k22 = k[22];
  uint8_t k23 = k[23];
  uint8_t k24 = k[24];
  uint8_t k25 = k[25];
  uint8_t k26 = k[26];
  uint8_t k27 = k[27];
  uint8_t k28 = k[28];
  uint8_t k29 = k[29];
  uint8_t k30 = k[30];
  uint8_t k31 = k[31];
  uint8_t n0 = n[0];
  uint8_t n1 = n[1];
  uint8_t n2 = n[2];
  uint8_t n3 = n[3];
  uint8_t n4 = n[4];
  uint8_t n5 = n[5];
  uint8_t n6 = n[6];
  uint8_t n7 = n[7];
  kcopy[0] = k0;
  kcopy[1] = k1;
  kcopy[2] = k2;
  kcopy[3] = k3;
  kcopy[4] = k4;
  kcopy[5] = k5;
  kcopy[6] = k6;
  kcopy[7] = k7;
  kcopy[8] = k8;
  kcopy[9] = k9;
  kcopy[10] = k10;
  kcopy[11] = k11;
  kcopy[12] = k12;
  kcopy[13] = k13;
  kcopy[14] = k14;
  kcopy[15] = k15;
  kcopy[16] = k16;
  kcopy[17] = k17;
  kcopy[18] = k18;
  kcopy[19] = k19;
  kcopy[20] = k20;
  kcopy[21] = k21;
  kcopy[22] = k22;
  kcopy[23] = k23;
  kcopy[24] = k24;
  kcopy[25] = k25;
  kcopy[26] = k26;
  kcopy[27] = k27;
  kcopy[28] = k28;
  kcopy[29] = k29;
  kcopy[30] = k30;
  kcopy[31] = k31;
  input[0] = n0;
  input[1] = n1;
  input[2] = n2;
  input[3] = n3;
  input[4] = n4;
  input[5] = n5;
  input[6] = n6;
  input[7] = n7;
  input[8] = zero;
  input[9] = zero;
  input[10] = zero;
  input[11] = zero;
  input[12] = zero;
  input[13] = zero;
  input[14] = zero;
  input[15] = zero;
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
    uint8_t zero = (uint8_t )0;
    uint8_t local_state[112];
    for (uintmax_t i = 0; i < (uint32_t )112; ++i)
      local_state[i] = zero;
    uint8_t *input = local_state;
    uint8_t *block = local_state + (uint32_t )16;
    uint8_t *kcopy = local_state + (uint32_t )80;
    Hacl_Symmetric_Salsa20_crypto_stream_salsa20_(n, k, local_state);
    uint64_t
    uu____2217 = Hacl_Symmetric_Salsa20_crypto_stream_salsa20_loop(c, clen, n, kcopy, input);
    if (clen_ >= (uint32_t )0)
    {
      Hacl_Symmetric_Salsa20_crypto_core_salsa20(block, input, kcopy);
      memcpy(c + off, block, clen_ * sizeof block[0]);
    }
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

