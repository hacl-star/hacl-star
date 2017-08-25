#include "Chacha20.h"

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

inline static void Hacl_Impl_Chacha20_setup(uint32_t *st, uint8_t *k, uint8_t *n1, uint32_t c)
{
  uint32_t *stcst = st;
  uint32_t *stk = st + (uint32_t )4;
  uint32_t *stc = st + (uint32_t )12;
  uint32_t *stn = st + (uint32_t )13;
  stcst[0] = (uint32_t )0x61707865;
  stcst[1] = (uint32_t )0x3320646e;
  stcst[2] = (uint32_t )0x79622d32;
  stcst[3] = (uint32_t )0x6b206574;
  Hacl_Lib_LoadStore32_uint32s_from_le_bytes(stk, k, (uint32_t )8);
  stc[0] = c;
  Hacl_Lib_LoadStore32_uint32s_from_le_bytes(stn, n1, (uint32_t )3);
}

inline static void
Hacl_Impl_Chacha20_quarter_round(uint32_t *st, uint32_t a, uint32_t b, uint32_t c, uint32_t d)
{
  uint32_t sa = st[a];
  uint32_t sb0 = st[b];
  st[a] = sa + sb0;
  uint32_t sd = st[d];
  uint32_t sa10 = st[a];
  uint32_t sda = sd ^ sa10;
  st[d] = sda << (uint32_t )16 | sda >> (uint32_t )32 - (uint32_t )16;
  uint32_t sa0 = st[c];
  uint32_t sb1 = st[d];
  st[c] = sa0 + sb1;
  uint32_t sd0 = st[b];
  uint32_t sa11 = st[c];
  uint32_t sda0 = sd0 ^ sa11;
  st[b] = sda0 << (uint32_t )12 | sda0 >> (uint32_t )32 - (uint32_t )12;
  uint32_t sa2 = st[a];
  uint32_t sb2 = st[b];
  st[a] = sa2 + sb2;
  uint32_t sd1 = st[d];
  uint32_t sa12 = st[a];
  uint32_t sda1 = sd1 ^ sa12;
  st[d] = sda1 << (uint32_t )8 | sda1 >> (uint32_t )32 - (uint32_t )8;
  uint32_t sa3 = st[c];
  uint32_t sb = st[d];
  st[c] = sa3 + sb;
  uint32_t sd2 = st[b];
  uint32_t sa1 = st[c];
  uint32_t sda2 = sd2 ^ sa1;
  st[b] = sda2 << (uint32_t )7 | sda2 >> (uint32_t )32 - (uint32_t )7;
}

inline static void Hacl_Impl_Chacha20_double_round(uint32_t *st)
{
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )0, (uint32_t )4, (uint32_t )8, (uint32_t )12);
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )1, (uint32_t )5, (uint32_t )9, (uint32_t )13);
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )2, (uint32_t )6, (uint32_t )10, (uint32_t )14);
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )3, (uint32_t )7, (uint32_t )11, (uint32_t )15);
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )0, (uint32_t )5, (uint32_t )10, (uint32_t )15);
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )1, (uint32_t )6, (uint32_t )11, (uint32_t )12);
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )2, (uint32_t )7, (uint32_t )8, (uint32_t )13);
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )3, (uint32_t )4, (uint32_t )9, (uint32_t )14);
}

inline static void Hacl_Impl_Chacha20_rounds(uint32_t *st)
{
  for (uint32_t i = (uint32_t )0; i < (uint32_t )10; i = i + (uint32_t )1)
    Hacl_Impl_Chacha20_double_round(st);
}

inline static void Hacl_Impl_Chacha20_sum_states(uint32_t *st, uint32_t *st_)
{
  for (uint32_t i = (uint32_t )0; i < (uint32_t )16; i = i + (uint32_t )1)
  {
    uint32_t uu____871 = st[i];
    uint32_t uu____874 = st_[i];
    uint32_t uu____870 = uu____871 + uu____874;
    st[i] = uu____870;
  }
}

inline static void Hacl_Impl_Chacha20_copy_state(uint32_t *st, uint32_t *st_)
{
  memcpy(st, st_, (uint32_t )16 * sizeof st_[0]);
}

inline static void Hacl_Impl_Chacha20_chacha20_core(uint32_t *k, uint32_t *st, uint32_t ctr)
{
  st[12] = ctr;
  Hacl_Impl_Chacha20_copy_state(k, st);
  Hacl_Impl_Chacha20_rounds(k);
  Hacl_Impl_Chacha20_sum_states(k, st);
}

inline static void
Hacl_Impl_Chacha20_chacha20_block(uint8_t *stream_block, uint32_t *st, uint32_t ctr)
{
  uint32_t st_[16] = { 0 };
  Hacl_Impl_Chacha20_chacha20_core(st_, st, ctr);
  Hacl_Lib_LoadStore32_uint32s_to_le_bytes(stream_block, st_, (uint32_t )16);
}

inline static void Hacl_Impl_Chacha20_init(uint32_t *st, uint8_t *k, uint8_t *n1)
{
  Hacl_Impl_Chacha20_setup(st, k, n1, (uint32_t )0);
}

static void
Hacl_Impl_Chacha20_update_last(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint32_t *st,
  uint32_t ctr
)
{
  uint8_t block[64] = { 0 };
  Hacl_Impl_Chacha20_chacha20_block(block, st, ctr);
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
Hacl_Impl_Chacha20_update(uint8_t *output, uint8_t *plain, uint32_t *st, uint32_t ctr)
{
  uint32_t b[48] = { 0 };
  uint32_t *k = b;
  uint32_t *ib = b + (uint32_t )16;
  uint32_t *ob = b + (uint32_t )32;
  Hacl_Impl_Chacha20_chacha20_core(k, st, ctr);
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
Hacl_Impl_Chacha20_chacha20_counter_mode_blocks(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint32_t *st,
  uint32_t ctr
)
{
  for (uint32_t i = (uint32_t )0; i < len; i = i + (uint32_t )1)
  {
    uint8_t *b = plain + (uint32_t )64 * i;
    uint8_t *o = output + (uint32_t )64 * i;
    Hacl_Impl_Chacha20_update(o, b, st, ctr + i);
  }
}

static void
Hacl_Impl_Chacha20_chacha20_counter_mode(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint32_t *st,
  uint32_t ctr
)
{
  uint32_t blocks_len = len >> (uint32_t )6;
  uint32_t part_len = len & (uint32_t )0x3f;
  uint8_t *output_ = output;
  uint8_t *plain_ = plain;
  uint8_t *output__ = output + (uint32_t )64 * blocks_len;
  uint8_t *plain__ = plain + (uint32_t )64 * blocks_len;
  Hacl_Impl_Chacha20_chacha20_counter_mode_blocks(output_, plain_, blocks_len, st, ctr);
  if (part_len > (uint32_t )0)
    Hacl_Impl_Chacha20_update_last(output__, plain__, part_len, st, ctr + blocks_len);
}

static void
Hacl_Impl_Chacha20_chacha20(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint8_t *k,
  uint8_t *n1,
  uint32_t ctr
)
{
  uint32_t buf[16] = { 0 };
  uint32_t *st = buf;
  Hacl_Impl_Chacha20_init(st, k, n1);
  Hacl_Impl_Chacha20_chacha20_counter_mode(output, plain, len, st, ctr);
}

void *Chacha20_op_String_Access(FStar_Monotonic_HyperStack_mem h, uint8_t *m)
{
  return (void *)(uint8_t )0;
}

void Chacha20_chacha20_key_block(uint8_t *block, uint8_t *k, uint8_t *n1, uint32_t ctr)
{
  uint32_t buf[16] = { 0 };
  uint32_t *st = buf;
  Hacl_Impl_Chacha20_init(st, k, n1);
  Hacl_Impl_Chacha20_chacha20_block(block, st, ctr);
}

void
Chacha20_chacha20(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint8_t *k,
  uint8_t *n1,
  uint32_t ctr
)
{
  Hacl_Impl_Chacha20_chacha20(output, plain, len, k, n1, ctr);
}

