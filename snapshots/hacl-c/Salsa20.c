#include "Salsa20.h"

static void
Hacl_Lib_Create_make_h32_4(uint32_t *b, uint32_t s0, uint32_t s1, uint32_t s2, uint32_t s3)
{
  b[0] = s0;
  b[1] = s1;
  b[2] = s2;
  b[3] = s3;
}

static void
Hacl_Lib_Create_make_h32_8(
  uint32_t *b,
  uint32_t s0,
  uint32_t s1,
  uint32_t s2,
  uint32_t s3,
  uint32_t s4,
  uint32_t s5,
  uint32_t s6,
  uint32_t s7
)
{
  Hacl_Lib_Create_make_h32_4(b, s0, s1, s2, s3);
  Hacl_Lib_Create_make_h32_4(b + (uint32_t )4, s4, s5, s6, s7);
}

static void
Hacl_Lib_Create_make_h32_16(
  uint32_t *b,
  uint32_t s0,
  uint32_t s1,
  uint32_t s2,
  uint32_t s3,
  uint32_t s4,
  uint32_t s5,
  uint32_t s6,
  uint32_t s7,
  uint32_t s8,
  uint32_t s9,
  uint32_t s10,
  uint32_t s11,
  uint32_t s12,
  uint32_t s13,
  uint32_t s14,
  uint32_t s15
)
{
  Hacl_Lib_Create_make_h32_8(b, s0, s1, s2, s3, s4, s5, s6, s7);
  Hacl_Lib_Create_make_h32_8(b + (uint32_t )8, s8, s9, s10, s11, s12, s13, s14, s15);
}

static void
Hacl_Lib_LoadStore32_uint32s_from_le_bytes(uint32_t *output, uint8_t *input, uint32_t len)
{
  for (uint32_t i = (uint32_t )0; i < len; i = i + (uint32_t )1)
  {
    uint8_t *x0 = input + (uint32_t )4 * i;
    uint32_t inputi = load32_le(x0);
    output[i] = inputi;
  }
}

static void
Hacl_Lib_LoadStore32_uint32s_to_le_bytes(uint8_t *output, uint32_t *input, uint32_t len)
{
  for (uint32_t i = (uint32_t )0; i < len; i = i + (uint32_t )1)
  {
    uint32_t hd1 = input[i];
    uint8_t *x0 = output + (uint32_t )4 * i;
    store32_le(x0, hd1);
  }
}

inline static void Hacl_Impl_Salsa20_setup(uint32_t *st, uint8_t *k, uint8_t *n1, uint64_t c)
{
  uint32_t tmp[10] = { 0 };
  uint32_t *k_ = tmp;
  uint32_t *n_ = tmp + (uint32_t )8;
  Hacl_Lib_LoadStore32_uint32s_from_le_bytes(k_, k, (uint32_t )8);
  Hacl_Lib_LoadStore32_uint32s_from_le_bytes(n_, n1, (uint32_t )2);
  uint32_t c0 = (uint32_t )c;
  uint32_t c1 = (uint32_t )(c >> (uint32_t )32);
  uint32_t k0 = k_[0];
  uint32_t k1 = k_[1];
  uint32_t k2 = k_[2];
  uint32_t k3 = k_[3];
  uint32_t k4 = k_[4];
  uint32_t k5 = k_[5];
  uint32_t k6 = k_[6];
  uint32_t k7 = k_[7];
  uint32_t n0 = n_[0];
  uint32_t n11 = n_[1];
  Hacl_Lib_Create_make_h32_16(st,
    (uint32_t )0x61707865,
    k0,
    k1,
    k2,
    k3,
    (uint32_t )0x3320646e,
    n0,
    n11,
    c0,
    c1,
    (uint32_t )0x79622d32,
    k4,
    k5,
    k6,
    k7,
    (uint32_t )0x6b206574);
}

inline static void
Hacl_Impl_Salsa20_line(uint32_t *st, uint32_t a, uint32_t b, uint32_t d, uint32_t s)
{
  uint32_t sa = st[a];
  uint32_t sb = st[b];
  uint32_t sd = st[d];
  uint32_t sbd = sb + sd;
  uint32_t sbds = sbd << s | sbd >> (uint32_t )32 - s;
  st[a] = sa ^ sbds;
}

inline static void
Hacl_Impl_Salsa20_quarter_round(uint32_t *st, uint32_t a, uint32_t b, uint32_t c, uint32_t d)
{
  Hacl_Impl_Salsa20_line(st, b, a, d, (uint32_t )7);
  Hacl_Impl_Salsa20_line(st, c, b, a, (uint32_t )9);
  Hacl_Impl_Salsa20_line(st, d, c, b, (uint32_t )13);
  Hacl_Impl_Salsa20_line(st, a, d, c, (uint32_t )18);
}

inline static void Hacl_Impl_Salsa20_double_round(uint32_t *st)
{
  Hacl_Impl_Salsa20_quarter_round(st, (uint32_t )0, (uint32_t )4, (uint32_t )8, (uint32_t )12);
  Hacl_Impl_Salsa20_quarter_round(st, (uint32_t )5, (uint32_t )9, (uint32_t )13, (uint32_t )1);
  Hacl_Impl_Salsa20_quarter_round(st, (uint32_t )10, (uint32_t )14, (uint32_t )2, (uint32_t )6);
  Hacl_Impl_Salsa20_quarter_round(st, (uint32_t )15, (uint32_t )3, (uint32_t )7, (uint32_t )11);
  Hacl_Impl_Salsa20_quarter_round(st, (uint32_t )0, (uint32_t )1, (uint32_t )2, (uint32_t )3);
  Hacl_Impl_Salsa20_quarter_round(st, (uint32_t )5, (uint32_t )6, (uint32_t )7, (uint32_t )4);
  Hacl_Impl_Salsa20_quarter_round(st, (uint32_t )10, (uint32_t )11, (uint32_t )8, (uint32_t )9);
  Hacl_Impl_Salsa20_quarter_round(st,
    (uint32_t )15,
    (uint32_t )12,
    (uint32_t )13,
    (uint32_t )14);
}

inline static void Hacl_Impl_Salsa20_rounds(uint32_t *st)
{
  for (uint32_t i = (uint32_t )0; i < (uint32_t )10; i = i + (uint32_t )1)
    Hacl_Impl_Salsa20_double_round(st);
}

inline static void Hacl_Impl_Salsa20_sum_states(uint32_t *st, uint32_t *st_)
{
  for (uint32_t i = (uint32_t )0; i < (uint32_t )16; i = i + (uint32_t )1)
  {
    uint32_t uu____871 = st[i];
    uint32_t uu____874 = st_[i];
    uint32_t uu____870 = uu____871 + uu____874;
    st[i] = uu____870;
  }
}

inline static void Hacl_Impl_Salsa20_copy_state(uint32_t *st, uint32_t *st_)
{
  memcpy(st, st_, (uint32_t )16 * sizeof st_[0]);
}

inline static void Hacl_Impl_Salsa20_salsa20_core(uint32_t *k, uint32_t *st, uint64_t ctr)
{
  uint32_t c0 = (uint32_t )ctr;
  uint32_t c1 = (uint32_t )(ctr >> (uint32_t )32);
  st[8] = c0;
  st[9] = c1;
  Hacl_Impl_Salsa20_copy_state(k, st);
  Hacl_Impl_Salsa20_rounds(k);
  Hacl_Impl_Salsa20_sum_states(k, st);
}

inline static void
Hacl_Impl_Salsa20_salsa20_block(uint8_t *stream_block, uint32_t *st, uint64_t ctr)
{
  uint32_t st_[16] = { 0 };
  Hacl_Impl_Salsa20_salsa20_core(st_, st, ctr);
  Hacl_Lib_LoadStore32_uint32s_to_le_bytes(stream_block, st_, (uint32_t )16);
}

inline static void Hacl_Impl_Salsa20_init(uint32_t *st, uint8_t *k, uint8_t *n1)
{
  Hacl_Impl_Salsa20_setup(st, k, n1, (uint64_t )0);
}

static void
Hacl_Impl_Salsa20_update_last(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint32_t *st,
  uint64_t ctr
)
{
  uint8_t block[64] = { 0 };
  Hacl_Impl_Salsa20_salsa20_block(block, st, ctr);
  uint8_t *mask = block;
  for (uint32_t i = (uint32_t )0; i < len; i = i + (uint32_t )1)
  {
    uint8_t uu____602 = plain[i];
    uint8_t uu____605 = mask[i];
    uint8_t uu____601 = uu____602 ^ uu____605;
    output[i] = uu____601;
  }
}

static void
Hacl_Impl_Salsa20_update(uint8_t *output, uint8_t *plain, uint32_t *st, uint64_t ctr)
{
  uint32_t b[48] = { 0 };
  uint32_t *k = b;
  uint32_t *ib = b + (uint32_t )16;
  uint32_t *ob = b + (uint32_t )32;
  Hacl_Impl_Salsa20_salsa20_core(k, st, ctr);
  Hacl_Lib_LoadStore32_uint32s_from_le_bytes(ib, plain, (uint32_t )16);
  for (uint32_t i = (uint32_t )0; i < (uint32_t )16; i = i + (uint32_t )1)
  {
    uint32_t uu____602 = ib[i];
    uint32_t uu____605 = k[i];
    uint32_t uu____601 = uu____602 ^ uu____605;
    ob[i] = uu____601;
  }
  Hacl_Lib_LoadStore32_uint32s_to_le_bytes(output, ob, (uint32_t )16);
}

static void
Hacl_Impl_Salsa20_salsa20_counter_mode_blocks(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint32_t *st,
  uint64_t ctr
)
{
  for (uint32_t i = (uint32_t )0; i < len; i = i + (uint32_t )1)
  {
    uint8_t *b = plain + (uint32_t )64 * i;
    uint8_t *o = output + (uint32_t )64 * i;
    Hacl_Impl_Salsa20_update(o, b, st, ctr + (uint64_t )i);
  }
}

static void
Hacl_Impl_Salsa20_salsa20_counter_mode(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint32_t *st,
  uint64_t ctr
)
{
  uint32_t blocks_len = len >> (uint32_t )6;
  uint32_t part_len = len & (uint32_t )0x3f;
  uint8_t *output_ = output;
  uint8_t *plain_ = plain;
  uint8_t *output__ = output + (uint32_t )64 * blocks_len;
  uint8_t *plain__ = plain + (uint32_t )64 * blocks_len;
  Hacl_Impl_Salsa20_salsa20_counter_mode_blocks(output_, plain_, blocks_len, st, ctr);
  if (part_len > (uint32_t )0)
    Hacl_Impl_Salsa20_update_last(output__, plain__, part_len, st, ctr + (uint64_t )blocks_len);
}

static void
Hacl_Impl_Salsa20_salsa20(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint8_t *k,
  uint8_t *n1,
  uint64_t ctr
)
{
  uint32_t buf[16] = { 0 };
  uint32_t *st = buf;
  Hacl_Impl_Salsa20_init(st, k, n1);
  Hacl_Impl_Salsa20_salsa20_counter_mode(output, plain, len, st, ctr);
}

inline static void Hacl_Impl_HSalsa20_setup(uint32_t *st, uint8_t *k, uint8_t *n1)
{
  uint32_t tmp[12] = { 0 };
  uint32_t *k_ = tmp;
  uint32_t *n_ = tmp + (uint32_t )8;
  Hacl_Lib_LoadStore32_uint32s_from_le_bytes(k_, k, (uint32_t )8);
  Hacl_Lib_LoadStore32_uint32s_from_le_bytes(n_, n1, (uint32_t )4);
  uint32_t k0 = k_[0];
  uint32_t k1 = k_[1];
  uint32_t k2 = k_[2];
  uint32_t k3 = k_[3];
  uint32_t k4 = k_[4];
  uint32_t k5 = k_[5];
  uint32_t k6 = k_[6];
  uint32_t k7 = k_[7];
  uint32_t n0 = n_[0];
  uint32_t n11 = n_[1];
  uint32_t n2 = n_[2];
  uint32_t n3 = n_[3];
  Hacl_Lib_Create_make_h32_16(st,
    (uint32_t )0x61707865,
    k0,
    k1,
    k2,
    k3,
    (uint32_t )0x3320646e,
    n0,
    n11,
    n2,
    n3,
    (uint32_t )0x79622d32,
    k4,
    k5,
    k6,
    k7,
    (uint32_t )0x6b206574);
}

static void
Hacl_Impl_HSalsa20_crypto_core_hsalsa20(uint8_t *output, uint8_t *nonce, uint8_t *key)
{
  uint32_t tmp[24] = { 0 };
  uint32_t *st = tmp;
  uint32_t *hs = tmp + (uint32_t )16;
  Hacl_Impl_HSalsa20_setup(st, key, nonce);
  Hacl_Impl_Salsa20_rounds(st);
  uint32_t hs0 = st[0];
  uint32_t hs1 = st[5];
  uint32_t hs2 = st[10];
  uint32_t hs3 = st[15];
  uint32_t hs4 = st[6];
  uint32_t hs5 = st[7];
  uint32_t hs6 = st[8];
  uint32_t hs7 = st[9];
  Hacl_Lib_Create_make_h32_8(hs, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7);
  Hacl_Lib_LoadStore32_uint32s_to_le_bytes(output, hs, (uint32_t )8);
}

void *Salsa20_op_String_Access(FStar_Monotonic_HyperStack_mem h, uint8_t *b)
{
  return (void *)(uint8_t )0;
}

void
Salsa20_salsa20(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint8_t *k,
  uint8_t *n1,
  uint64_t ctr
)
{
  Hacl_Impl_Salsa20_salsa20(output, plain, len, k, n1, ctr);
}

void Salsa20_hsalsa20(uint8_t *output, uint8_t *key, uint8_t *nonce)
{
  Hacl_Impl_HSalsa20_crypto_core_hsalsa20(output, nonce, key);
}

