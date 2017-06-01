#include "Chacha20.h"

static void
Hacl_Impl_Chacha20_uint32s_from_le_bytes(uint32_t *output, uint8_t *input, uint32_t len)
{
  for (int i = 0; i < len; i++) {
    output[i] = load32_le(input + (4*i));
  }
  //memcpy((uint8_t*) output, input, len * 4);
}

static void
Hacl_Impl_Chacha20_uint32s_to_le_bytes(uint8_t *output, uint32_t *input, uint32_t len)
{
  for (int i = 0; i < len; i++) {
   store32_le(output + (4*i),input[i]);
  }
  //memcpy((uint8_t*) output, (uint8_t*) input, len * 4);
}

static void Hacl_Impl_Chacha20_setup(uint32_t *st, uint8_t *k, uint8_t *n, uint32_t c)
{
  uint32_t *stcst = st;
  uint32_t *stk = st + (uint32_t )4;
  uint32_t *stc = st + (uint32_t )12;
  uint32_t *stn = st + (uint32_t )13;
  stcst[0] = (uint32_t )0x61707865;
  stcst[1] = (uint32_t )0x3320646e;
  stcst[2] = (uint32_t )0x79622d32;
  stcst[3] = (uint32_t )0x6b206574;
  Hacl_Impl_Chacha20_uint32s_from_le_bytes(stk, k, (uint32_t )8);
  stc[0] = c;
  Hacl_Impl_Chacha20_uint32s_from_le_bytes(stn, n, (uint32_t )3);
  return;
}

inline static void
Hacl_Impl_Chacha20_quarter_round(uint32_t *st, uint32_t a, uint32_t b, uint32_t c, uint32_t d)
{
  uint32_t sa0 = st[a];
  uint32_t sb0 = st[b];
  st[a] = sa0 + sb0;
  uint32_t sd = st[d];
  uint32_t sa1 = st[a];
  uint32_t sda = sd ^ sa1;
  st[d] = sda << (uint32_t )16 | sda >> (uint32_t )32 - (uint32_t )16;
  uint32_t sa2 = st[c];
  uint32_t sb1 = st[d];
  st[c] = sa2 + sb1;
  uint32_t sd0 = st[b];
  uint32_t sa3 = st[c];
  uint32_t sda0 = sd0 ^ sa3;
  st[b] = sda0 << (uint32_t )12 | sda0 >> (uint32_t )32 - (uint32_t )12;
  uint32_t sa4 = st[a];
  uint32_t sb2 = st[b];
  st[a] = sa4 + sb2;
  uint32_t sd1 = st[d];
  uint32_t sa5 = st[a];
  uint32_t sda1 = sd1 ^ sa5;
  st[d] = sda1 << (uint32_t )8 | sda1 >> (uint32_t )32 - (uint32_t )8;
  uint32_t sa6 = st[c];
  uint32_t sb = st[d];
  st[c] = sa6 + sb;
  uint32_t sd2 = st[b];
  uint32_t sa = st[c];
  uint32_t sda2 = sd2 ^ sa;
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
  return;
}

inline static void Hacl_Impl_Chacha20_rounds(uint32_t *st)
{
    Hacl_Impl_Chacha20_double_round(st);
    Hacl_Impl_Chacha20_double_round(st);
    Hacl_Impl_Chacha20_double_round(st);
    Hacl_Impl_Chacha20_double_round(st);
    Hacl_Impl_Chacha20_double_round(st);
    Hacl_Impl_Chacha20_double_round(st);
    Hacl_Impl_Chacha20_double_round(st);
    Hacl_Impl_Chacha20_double_round(st);
    Hacl_Impl_Chacha20_double_round(st);
    Hacl_Impl_Chacha20_double_round(st);
}

static void Hacl_Impl_Chacha20_sum_states(uint32_t *st, uint32_t *st_)
{
  for (uint32_t i = (uint32_t )0; i < (uint32_t )16; i = i + (uint32_t )1)
  {
    uint32_t _0_39 = st[i];
    uint32_t _0_38 = st_[i];
    uint32_t _0_40 = _0_39 + _0_38;
    st[i] = _0_40;
  }
}

static void Hacl_Impl_Chacha20_copy_state(uint32_t *st, uint32_t *st_)
{
  for (int i = 0; i < 16; i++) 
    st[i] = st_[i];
  //  memcpy(st, st_, (uint32_t )16 * sizeof st_[0]);
}

inline static void
Hacl_Impl_Chacha20_chacha20_core(void *log, uint32_t *k, uint32_t *st, uint32_t ctr)
{
  st[12] = ctr;
  Hacl_Impl_Chacha20_copy_state(k, st);
  Hacl_Impl_Chacha20_rounds(k);
  Hacl_Impl_Chacha20_sum_states(k, st);
  return;
}

inline static void
Hacl_Impl_Chacha20_chacha20_block(void *log, uint8_t *stream_block, uint32_t *st, uint32_t ctr)
{
  //  KRML_CHECK_SIZE((uint32_t )0, (uint32_t )16);
  uint32_t st_[16] = { 0 };
  Hacl_Impl_Chacha20_chacha20_core((void *)(uint8_t )0, st_, st, ctr);
  Hacl_Impl_Chacha20_uint32s_to_le_bytes(stream_block, st_, (uint32_t )16);
  return;
}

inline static void Hacl_Impl_Chacha20_init(uint32_t *st, uint8_t *k, uint8_t *n)
{
  Hacl_Impl_Chacha20_setup(st, k, n, (uint32_t )0);
  return;
}

static void
Hacl_Impl_Chacha20_update_last(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  void *log,
  uint32_t *st,
  uint32_t ctr
)
{
  //  KRML_CHECK_SIZE((uint8_t )0, (uint32_t )64);
  uint8_t block[64] = { 0 };
  Hacl_Impl_Chacha20_chacha20_block((void *)(uint8_t )0, block, st, ctr);
  uint8_t *mask = block;
  for (uint32_t i = (uint32_t )0; i < len; i = i + (uint32_t )1)
  {
    uint8_t _0_35 = plain[i];
    uint8_t _0_34 = block[i];
    uint8_t _0_36 = _0_35 ^ _0_34;
    output[i] = _0_36;
  }
}

inline static void
Hacl_Impl_Chacha20_update(
  uint8_t *output,
  uint8_t *plain,
  void *log,
  uint32_t *st,
  uint32_t ctr
)
{
  //  KRML_CHECK_SIZE((uint8_t )0, (uint32_t )64);
  // uint8_t block[64] = { 0 };
  uint32_t block[16] = { 0 };
  Hacl_Impl_Chacha20_chacha20_core((void *)(uint8_t )0, (uint32_t*) block, st, ctr);
  for (uint32_t i = (uint32_t )0; i < (uint32_t )16; i = i + (uint32_t )1)
  {
    uint32_t _0_35 = load32_le(plain + (4*i));
    uint32_t _0_34 = block[i];
    uint32_t _0_36 = _0_35 ^ _0_34;
    store32_le(output + (4*i),_0_36);
  }
}

static void
Hacl_Impl_Chacha20_chacha20_counter_mode_(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  void *log,
  uint32_t *st,
  uint32_t ctr
)
{
  if (len == (uint32_t )0)
    return;
  else
  {
    Hacl_Impl_Chacha20_update_last(output, plain, len, (void *)(uint8_t )0, st, ctr);
    return;
  }
}

inline static void
Hacl_Impl_Chacha20_chacha20_counter_mode(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  void *log,
  uint32_t *st,
  uint32_t ctr
)
{
  uint32_t blocks = len >> 6;
  uint8_t *b = plain;
  uint8_t *o = output;
  uint32_t c = ctr;

  for (int i = 0; i < blocks; i++)
  {
    Hacl_Impl_Chacha20_update(o, b, (void *)(uint8_t )0, st, c);
    b = b + 64;
    o = o + 64;
    c = c + 1;
  }
  len = len & 0x3f;
  Hacl_Impl_Chacha20_chacha20_counter_mode_(o, b, len, (void *)(uint8_t )0, st, c);
}

static void
Hacl_Impl_Chacha20_chacha20(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint8_t *k,
  uint8_t *n,
  uint32_t ctr
)
{
  //  KRML_CHECK_SIZE((uint32_t )0, (uint32_t )16);
  uint32_t buf[16] = { 0 };
  uint32_t *st = buf;
  Hacl_Impl_Chacha20_init(st, k, n);
  Hacl_Impl_Chacha20_chacha20_counter_mode(output, plain, len, (void *)(uint8_t )0, st, ctr);
}

void Chacha20_chacha20_key_block(uint8_t *block, uint8_t *k, uint8_t *n, uint32_t ctr)
{
  //  KRML_CHECK_SIZE((uint32_t )0, (uint32_t )16);
  uint32_t buf[16] = { 0 };
  uint32_t *st = buf;
  Hacl_Impl_Chacha20_init(st, k, n);
  Hacl_Impl_Chacha20_chacha20_block((void *)(uint8_t )0, block, st, ctr);
}

void Chacha20_double_round(uint32_t *st)
{
  Hacl_Impl_Chacha20_double_round(st);
  return;
}

void *Chacha20_value_at(uint8_t *m, FStar_HyperStack_mem h)
{
  return (void *)(uint8_t )0;
}

void
Chacha20_chacha20(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint8_t *k,
  uint8_t *n,
  uint32_t ctr
)
{
  Hacl_Impl_Chacha20_chacha20(output, plain, len, k, n, ctr);
  return;
}

