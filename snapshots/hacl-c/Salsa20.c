#include "Salsa20.h"

inline static void
Hacl_Impl_Salsa20_uint32s_from_le_bytes(uint32_t *output, uint8_t *input, uint32_t len)
{
  if (len == (uint32_t )0)
    return;
  else
  {
    uint8_t *x0 = input;
    uint32_t _0_41 = load32_le(x0);
    output[0] = _0_41;
    uint32_t *output_ = output + (uint32_t )1;
    uint8_t *input_ = input + (uint32_t )4;
    Hacl_Impl_Salsa20_uint32s_from_le_bytes(output_, input_, len - (uint32_t )1);
    return;
  }
}

inline static void
Hacl_Impl_Salsa20_uint32s_to_le_bytes(uint8_t *output, uint32_t *input, uint32_t len)
{
  if (len == (uint32_t )0)
    return;
  else
  {
    uint32_t hd = input[0];
    uint8_t *x0 = output;
    store32_le(x0, hd);
    uint8_t *output_ = output + (uint32_t )4;
    uint32_t *input_ = input + (uint32_t )1;
    Hacl_Impl_Salsa20_uint32s_to_le_bytes(output_, input_, len - (uint32_t )1);
    return;
  }
}

inline static void Hacl_Impl_Salsa20_setup(uint32_t *st, uint8_t *k, uint8_t *n, uint64_t c)
{
  KRML_CHECK_SIZE((uint32_t )0, (uint32_t )10);
  uint32_t tmp[10] = { 0 };
  uint32_t *k_ = tmp;
  uint32_t *n_ = tmp + (uint32_t )8;
  Hacl_Impl_Salsa20_uint32s_from_le_bytes(k_, k, (uint32_t )8);
  Hacl_Impl_Salsa20_uint32s_from_le_bytes(n_, n, (uint32_t )2);
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
  uint32_t n1 = n_[1];
  st[0] = (uint32_t )0x61707865;
  st[1] = k0;
  st[2] = k1;
  st[3] = k2;
  st[4] = k3;
  st[5] = (uint32_t )0x3320646e;
  st[6] = n0;
  st[7] = n1;
  st[8] = c0;
  st[9] = c1;
  st[10] = (uint32_t )0x79622d32;
  st[11] = k4;
  st[12] = k5;
  st[13] = k6;
  st[14] = k7;
  st[15] = (uint32_t )0x6b206574;
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
  return;
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
  return;
}

inline static void Hacl_Impl_Salsa20_rounds(uint32_t *st)
{
  // KB: manually inlined for auto-vec
  //  for (uint32_t i = (uint32_t )0; i < (uint32_t )10; i = i + (uint32_t )1)
    Hacl_Impl_Salsa20_double_round(st);
    Hacl_Impl_Salsa20_double_round(st);
    Hacl_Impl_Salsa20_double_round(st);
    Hacl_Impl_Salsa20_double_round(st);
    Hacl_Impl_Salsa20_double_round(st);
    Hacl_Impl_Salsa20_double_round(st);
    Hacl_Impl_Salsa20_double_round(st);
    Hacl_Impl_Salsa20_double_round(st);
    Hacl_Impl_Salsa20_double_round(st);
    Hacl_Impl_Salsa20_double_round(st);
}

inline static void Hacl_Impl_Salsa20_sum_states(uint32_t *st, uint32_t *st_)
{
  for (uint32_t i = (uint32_t )0; i < (uint32_t )16; i = i + (uint32_t )1)
  {
    uint32_t _0_39 = st[i];
    uint32_t _0_38 = st_[i];
    uint32_t _0_40 = _0_39 + _0_38;
    st[i] = _0_40;
  }
}

inline static void Hacl_Impl_Salsa20_copy_state(uint32_t *st, uint32_t *st_)
{
  memcpy(st, st_, (uint32_t )16 * sizeof st_[0]);
}

inline static void
Hacl_Impl_Salsa20_salsa20_core(void *log, uint32_t *k, uint32_t *st, uint64_t ctr)
{
  uint32_t c0 = (uint32_t )ctr;
  uint32_t c1 = (uint32_t )(ctr >> (uint32_t )32);
  st[8] = c0;
  st[9] = c1;
  Hacl_Impl_Salsa20_copy_state(k, st);
  Hacl_Impl_Salsa20_rounds(k);
  Hacl_Impl_Salsa20_sum_states(k, st);
  return;
}

inline static void
Hacl_Impl_Salsa20_salsa20_block(void *log, uint8_t *stream_block, uint32_t *st, uint64_t ctr)
{
  KRML_CHECK_SIZE((uint32_t )0, (uint32_t )16);
  uint32_t st_[16] = { 0 };
  Hacl_Impl_Salsa20_salsa20_core((void *)(uint8_t )0, st_, st, ctr);
  Hacl_Impl_Salsa20_uint32s_to_le_bytes(stream_block, st_, (uint32_t )16);
}

inline static void Hacl_Impl_Salsa20_init(uint32_t *st, uint8_t *k, uint8_t *n)
{
  Hacl_Impl_Salsa20_setup(st, k, n, (uint64_t )0);
  return;
}

static void
Hacl_Impl_Salsa20_update_last(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  void *log,
  uint32_t *st,
  uint64_t ctr
)
{
  KRML_CHECK_SIZE((uint8_t )0, (uint32_t )64);
  uint8_t block[64] = { 0 };
  Hacl_Impl_Salsa20_salsa20_block((void *)(uint8_t )0, block, st, ctr);
  uint8_t *mask = block;
  for (uint32_t i = (uint32_t )0; i < len; i = i + (uint32_t )1)
  {
    uint8_t _0_35 = plain[i];
    uint8_t _0_34 = mask[i];
    uint8_t _0_36 = _0_35 ^ _0_34;
    output[i] = _0_36;
  }
}

static void
Hacl_Impl_Salsa20_update(
  uint8_t *output,
  uint8_t *plain,
  void *log,
  uint32_t *st,
  uint64_t ctr
)
{
  KRML_CHECK_SIZE((uint32_t )0, (uint32_t )16);
  uint32_t k[16] = { 0 };
  Hacl_Impl_Salsa20_salsa20_core((void *)(uint8_t )0, k, st, ctr);
  KRML_CHECK_SIZE((uint32_t )0, (uint32_t )16);
  uint32_t ib[16] = { 0 };
  KRML_CHECK_SIZE((uint32_t )0, (uint32_t )16);
  uint32_t ob[16] = { 0 };
  Hacl_Impl_Salsa20_uint32s_from_le_bytes(ib, plain, (uint32_t )16);
  for (uint32_t i = (uint32_t )0; i < (uint32_t )16; i = i + (uint32_t )1)
  {
    uint32_t _0_35 = ib[i];
    uint32_t _0_34 = k[i];
    uint32_t _0_36 = _0_35 ^ _0_34;
    ob[i] = _0_36;
  }
  Hacl_Impl_Salsa20_uint32s_to_le_bytes(output, ob, (uint32_t )16);
}

static void
Hacl_Impl_Salsa20_salsa20_counter_mode_(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  void *log,
  uint32_t *st,
  uint64_t ctr
)
{
  if (len == (uint32_t )0)
    return;
  else
  {
    Hacl_Impl_Salsa20_update_last(output, plain, len, (void *)(uint8_t )0, st, ctr);
    return;
  }
}

static void
Hacl_Impl_Salsa20_salsa20_counter_mode(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  void *log,
  uint32_t *st,
  uint64_t ctr
)
{
  if (len <= (uint32_t )64)
  {
    Hacl_Impl_Salsa20_salsa20_counter_mode_(output, plain, len, (void *)(uint8_t )0, st, ctr);
    return;
  }
  else
  {
    uint8_t *b = plain;
    uint8_t *b_ = plain + (uint32_t )64;
    uint8_t *o = output;
    uint8_t *o_ = output + (uint32_t )64;
    Hacl_Impl_Salsa20_update(o, b, (void *)(uint8_t )0, st, ctr);
    Hacl_Impl_Salsa20_salsa20_counter_mode(o_,
      b_,
      len - (uint32_t )64,
      (void *)(uint8_t )0,
      st,
      ctr + (uint64_t )1);
    return;
  }
}

static void
Hacl_Impl_Salsa20_salsa20(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint8_t *k,
  uint8_t *n,
  uint64_t ctr
)
{
  KRML_CHECK_SIZE((uint32_t )0, (uint32_t )16);
  uint32_t buf[16] = { 0 };
  uint32_t *st = buf;
  Hacl_Impl_Salsa20_init(st, k, n);
  Hacl_Impl_Salsa20_salsa20_counter_mode(output, plain, len, (void *)(uint8_t )0, st, ctr);
}

void *Salsa20_value_at(uint8_t *m, FStar_HyperStack_mem h)
{
  return (void *)(uint8_t )0;
}

void
Salsa20_salsa20(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint8_t *k,
  uint8_t *n,
  uint64_t ctr
)
{
  Hacl_Impl_Salsa20_salsa20(output, plain, len, k, n, ctr);
  return;
}

