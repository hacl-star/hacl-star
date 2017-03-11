#include "Chacha20_vec.h"

inline static void Hacl_Impl_Chacha20_state2_state_incr(vec *k)
{
  vec k12 = k[12];
  vec step = vec_load_32(vec_size);
  k[12] = vec_add(k12, step);
}

inline static void Hacl_Impl_Chacha20_state2_state_to_key(vec *k)
{
  if (vec_size == (uint32_t )8)
  {
    vec k0 = k[0];
    vec k1 = k[1];
    vec k2 = k[2];
    vec k3 = k[3];
    vec k4 = k[4];
    vec k5 = k[5];
    vec k6 = k[6];
    vec k7 = k[7];
    vec k8 = k[8];
    vec k9 = k[9];
    vec k10 = k[10];
    vec k11 = k[11];
    vec k12 = k[12];
    vec k13 = k[13];
    vec k14 = k[14];
    vec k15 = k[15];
    vec k01l = vec_interleave32_low(k0, k1);
    vec k23l = vec_interleave32_low(k2, k3);
    vec k45l = vec_interleave32_low(k4, k5);
    vec k67l = vec_interleave32_low(k6, k7);
    vec k89l = vec_interleave32_low(k8, k9);
    vec k1011l = vec_interleave32_low(k10, k11);
    vec k1213l = vec_interleave32_low(k12, k13);
    vec k1415l = vec_interleave32_low(k14, k15);
    vec k03_1 = vec_interleave64_low(k01l, k23l);
    vec k47_1 = vec_interleave64_low(k45l, k67l);
    vec k07_0 = vec_choose_128(k03_1, k47_1, (uint32_t )0, (uint32_t )2);
    vec k07_4 = vec_choose_128(k03_1, k47_1, (uint32_t )1, (uint32_t )3);
    vec k03_2 = vec_interleave64_high(k01l, k23l);
    vec k47_2 = vec_interleave64_high(k45l, k67l);
    vec k07_1 = vec_choose_128(k03_2, k47_2, (uint32_t )0, (uint32_t )2);
    vec k07_5 = vec_choose_128(k03_2, k47_2, (uint32_t )1, (uint32_t )3);
    vec k811_1 = vec_interleave64_low(k89l, k1011l);
    vec k1215_1 = vec_interleave64_low(k1213l, k1415l);
    vec k815_0 = vec_choose_128(k811_1, k1215_1, (uint32_t )0, (uint32_t )2);
    vec k815_4 = vec_choose_128(k811_1, k1215_1, (uint32_t )1, (uint32_t )3);
    vec k811_2 = vec_interleave64_high(k89l, k1011l);
    vec k1215_2 = vec_interleave64_high(k1213l, k1415l);
    vec k815_1 = vec_choose_128(k811_2, k1215_2, (uint32_t )0, (uint32_t )2);
    vec k815_5 = vec_choose_128(k811_2, k1215_2, (uint32_t )1, (uint32_t )3);
    vec k01h = vec_interleave32_high(k0, k1);
    vec k23h = vec_interleave32_high(k2, k3);
    vec k45h = vec_interleave32_high(k4, k5);
    vec k67h = vec_interleave32_high(k6, k7);
    vec k89h = vec_interleave32_high(k8, k9);
    vec k1011h = vec_interleave32_high(k10, k11);
    vec k1213h = vec_interleave32_high(k12, k13);
    vec k1415h = vec_interleave32_high(k14, k15);
    vec k03_3 = vec_interleave64_low(k01h, k23h);
    vec k47_3 = vec_interleave64_low(k45h, k67h);
    vec k07_2 = vec_choose_128(k03_3, k47_3, (uint32_t )0, (uint32_t )2);
    vec k07_6 = vec_choose_128(k03_3, k47_3, (uint32_t )1, (uint32_t )3);
    vec k03_4 = vec_interleave64_high(k01h, k23h);
    vec k47_4 = vec_interleave64_high(k45h, k67h);
    vec k07_3 = vec_choose_128(k03_4, k47_4, (uint32_t )0, (uint32_t )2);
    vec k07_7 = vec_choose_128(k03_4, k47_4, (uint32_t )1, (uint32_t )3);
    vec k811_3 = vec_interleave64_low(k89h, k1011h);
    vec k1215_3 = vec_interleave64_low(k1213h, k1415h);
    vec k815_2 = vec_choose_128(k811_3, k1215_3, (uint32_t )0, (uint32_t )2);
    vec k815_6 = vec_choose_128(k811_3, k1215_3, (uint32_t )1, (uint32_t )3);
    vec k811_4 = vec_interleave64_high(k89h, k1011h);
    vec k1215_4 = vec_interleave64_high(k1213h, k1415h);
    vec k815_3 = vec_choose_128(k811_4, k1215_4, (uint32_t )0, (uint32_t )2);
    vec k815_7 = vec_choose_128(k811_4, k1215_4, (uint32_t )1, (uint32_t )3);
    k[0] = k07_0;
    k[1] = k815_0;
    k[2] = k07_1;
    k[3] = k815_1;
    k[4] = k07_2;
    k[5] = k815_2;
    k[6] = k07_3;
    k[7] = k815_3;
    k[8] = k07_4;
    k[9] = k815_4;
    k[10] = k07_5;
    k[11] = k815_5;
    k[12] = k07_6;
    k[13] = k815_6;
    k[14] = k07_7;
    k[15] = k815_7;
  }
  else if (vec_size == (uint32_t )4)
  {
    vec k0 = k[0];
    vec k1 = k[1];
    vec k2 = k[2];
    vec k3 = k[3];
    vec k4 = k[4];
    vec k5 = k[5];
    vec k6 = k[6];
    vec k7 = k[7];
    vec k8 = k[8];
    vec k9 = k[9];
    vec k10 = k[10];
    vec k11 = k[11];
    vec k12 = k[12];
    vec k13 = k[13];
    vec k14 = k[14];
    vec k15 = k[15];
    vec k01l = vec_interleave32_low(k0, k1);
    vec k23l = vec_interleave32_low(k2, k3);
    vec k45l = vec_interleave32_low(k4, k5);
    vec k67l = vec_interleave32_low(k6, k7);
    vec k89l = vec_interleave32_low(k8, k9);
    vec k1011l = vec_interleave32_low(k10, k11);
    vec k1213l = vec_interleave32_low(k12, k13);
    vec k1415l = vec_interleave32_low(k14, k15);
    vec k03_0 = vec_interleave64_low(k01l, k23l);
    vec k47_0 = vec_interleave64_low(k45l, k67l);
    vec k03_1 = vec_interleave64_high(k01l, k23l);
    vec k47_1 = vec_interleave64_high(k45l, k67l);
    vec k811_0 = vec_interleave64_low(k89l, k1011l);
    vec k1215_0 = vec_interleave64_low(k1213l, k1415l);
    vec k811_1 = vec_interleave64_high(k89l, k1011l);
    vec k1215_1 = vec_interleave64_high(k1213l, k1415l);
    vec k01h = vec_interleave32_high(k0, k1);
    vec k23h = vec_interleave32_high(k2, k3);
    vec k45h = vec_interleave32_high(k4, k5);
    vec k67h = vec_interleave32_high(k6, k7);
    vec k89h = vec_interleave32_high(k8, k9);
    vec k1011h = vec_interleave32_high(k10, k11);
    vec k1213h = vec_interleave32_high(k12, k13);
    vec k1415h = vec_interleave32_high(k14, k15);
    vec k03_2 = vec_interleave64_low(k01h, k23h);
    vec k47_2 = vec_interleave64_low(k45h, k67h);
    vec k03_3 = vec_interleave64_high(k01h, k23h);
    vec k47_3 = vec_interleave64_high(k45h, k67h);
    vec k811_2 = vec_interleave64_low(k89h, k1011h);
    vec k1215_2 = vec_interleave64_low(k1213h, k1415h);
    vec k811_3 = vec_interleave64_high(k89h, k1011h);
    vec k1215_3 = vec_interleave64_high(k1213h, k1415h);
    k[0] = k03_0;
    k[1] = k47_0;
    k[2] = k811_0;
    k[3] = k1215_0;
    k[4] = k03_1;
    k[5] = k47_1;
    k[6] = k811_1;
    k[7] = k1215_1;
    k[8] = k03_2;
    k[9] = k47_2;
    k[10] = k811_2;
    k[11] = k1215_2;
    k[12] = k03_3;
    k[13] = k47_3;
    k[14] = k811_3;
    k[15] = k1215_3;
  }
  else
    return;
}

inline static void Hacl_Impl_Chacha20_state2_state_to_key_block(uint8_t *stream_block, vec *k)
{
  Hacl_Impl_Chacha20_state2_state_to_key(k);
  vec_store16(stream_block, k, vec_size * (uint32_t )4);
  return;
}

inline static void
Hacl_Impl_Chacha20_state2_state_setup(vec *st, uint8_t *k, uint8_t *n, uint32_t c)
{
  st[0] = vec_load_32((uint32_t )0x61707865);
  st[1] = vec_load_32((uint32_t )0x3320646e);
  st[2] = vec_load_32((uint32_t )0x79622d32);
  st[3] = vec_load_32((uint32_t )0x6b206574);
  uint8_t *x00 = k;
  vec _0_41 = vec_load_32(load32_le(x00));
  st[4] = _0_41;
  uint8_t *x01 = k + (uint32_t )4;
  vec _0_42 = vec_load_32(load32_le(x01));
  st[5] = _0_42;
  uint8_t *x02 = k + (uint32_t )8;
  vec _0_43 = vec_load_32(load32_le(x02));
  st[6] = _0_43;
  uint8_t *x03 = k + (uint32_t )12;
  vec _0_44 = vec_load_32(load32_le(x03));
  st[7] = _0_44;
  uint8_t *x04 = k + (uint32_t )16;
  vec _0_45 = vec_load_32(load32_le(x04));
  st[8] = _0_45;
  uint8_t *x05 = k + (uint32_t )20;
  vec _0_46 = vec_load_32(load32_le(x05));
  st[9] = _0_46;
  uint8_t *x06 = k + (uint32_t )24;
  vec _0_47 = vec_load_32(load32_le(x06));
  st[10] = _0_47;
  uint8_t *x07 = k + (uint32_t )28;
  vec _0_48 = vec_load_32(load32_le(x07));
  st[11] = _0_48;
  uint32_t ctr = c;
  if (vec_size == (uint32_t )8)
    st[12] =
      vec_load_32x8(ctr,
        ctr + (uint32_t )1,
        ctr + (uint32_t )2,
        ctr + (uint32_t )3,
        ctr + (uint32_t )4,
        ctr + (uint32_t )5,
        ctr + (uint32_t )6,
        ctr + (uint32_t )7);
  else if (vec_size == (uint32_t )4)
    st[12] = vec_load_32x4(ctr, ctr + (uint32_t )1, ctr + (uint32_t )2, ctr + (uint32_t )3);
  else
    st[12] = vec_load_32(ctr);
  uint8_t *x08 = n;
  uint32_t n0 = load32_le(x08);
  uint8_t *x09 = n + (uint32_t )4;
  uint32_t n1 = load32_le(x09);
  uint8_t *x0 = n + (uint32_t )8;
  uint32_t n2 = load32_le(x0);
  st[13] = vec_load_32(n0);
  st[14] = vec_load_32(n1);
  st[15] = vec_load_32(n2);
}

inline static void
Hacl_Impl_Chacha20_vec2_line(vec *st, uint32_t a, uint32_t b, uint32_t d, uint32_t s)
{
  vec sa0 = st[a];
  vec sb = st[b];
  vec sd0 = st[d];
  vec sa = vec_add(sa0, sb);
  vec sd = vec_rotate_left(vec_xor(sd0, sa), s);
  st[a] = sa;
  st[d] = sd;
}

inline static void Hacl_Impl_Chacha20_vec2_column_round(vec *st)
{
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )0, (uint32_t )4, (uint32_t )12, (uint32_t )16);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )1, (uint32_t )5, (uint32_t )13, (uint32_t )16);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )2, (uint32_t )6, (uint32_t )14, (uint32_t )16);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )3, (uint32_t )7, (uint32_t )15, (uint32_t )16);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )8, (uint32_t )12, (uint32_t )4, (uint32_t )12);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )9, (uint32_t )13, (uint32_t )5, (uint32_t )12);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )10, (uint32_t )14, (uint32_t )6, (uint32_t )12);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )11, (uint32_t )15, (uint32_t )7, (uint32_t )12);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )0, (uint32_t )4, (uint32_t )12, (uint32_t )8);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )1, (uint32_t )5, (uint32_t )13, (uint32_t )8);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )2, (uint32_t )6, (uint32_t )14, (uint32_t )8);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )3, (uint32_t )7, (uint32_t )15, (uint32_t )8);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )8, (uint32_t )12, (uint32_t )4, (uint32_t )7);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )9, (uint32_t )13, (uint32_t )5, (uint32_t )7);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )10, (uint32_t )14, (uint32_t )6, (uint32_t )7);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )11, (uint32_t )15, (uint32_t )7, (uint32_t )7);
  return;
}

inline static void Hacl_Impl_Chacha20_vec2_double_round(vec *st)
{
  Hacl_Impl_Chacha20_vec2_column_round(st);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )0, (uint32_t )5, (uint32_t )15, (uint32_t )16);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )1, (uint32_t )6, (uint32_t )12, (uint32_t )16);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )2, (uint32_t )7, (uint32_t )13, (uint32_t )16);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )3, (uint32_t )4, (uint32_t )14, (uint32_t )16);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )10, (uint32_t )15, (uint32_t )5, (uint32_t )12);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )11, (uint32_t )12, (uint32_t )6, (uint32_t )12);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )8, (uint32_t )13, (uint32_t )7, (uint32_t )12);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )9, (uint32_t )14, (uint32_t )4, (uint32_t )12);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )0, (uint32_t )5, (uint32_t )15, (uint32_t )8);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )1, (uint32_t )6, (uint32_t )12, (uint32_t )8);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )2, (uint32_t )7, (uint32_t )13, (uint32_t )8);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )3, (uint32_t )4, (uint32_t )14, (uint32_t )8);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )10, (uint32_t )15, (uint32_t )5, (uint32_t )7);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )11, (uint32_t )12, (uint32_t )6, (uint32_t )7);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )8, (uint32_t )13, (uint32_t )7, (uint32_t )7);
  Hacl_Impl_Chacha20_vec2_line(st, (uint32_t )9, (uint32_t )14, (uint32_t )4, (uint32_t )7);
  return;
}

inline static void Hacl_Impl_Chacha20_vec2_sum_states(vec *st_, vec *st)
{
  sum_states16(st_, st);
  return;
}

inline static void Hacl_Impl_Chacha20_vec2_copy_state(vec *st_, vec *st)
{
  copy_state16(st_, st);
  return;
}

inline static void Hacl_Impl_Chacha20_vec2_chacha20_core(vec *k, vec *st)
{
  Hacl_Impl_Chacha20_vec2_copy_state(k, st);
  rounds16(k);
  Hacl_Impl_Chacha20_vec2_sum_states(k, st);
  return;
}

inline static void Hacl_Impl_Chacha20_vec2_chacha20_block(uint8_t *stream_block, vec *st)
{
  KRML_CHECK_SIZE(zero, (uint32_t )16);
  vec buf[16];
  for (uintmax_t _i = 0; _i < (uint32_t )16; ++_i)
    buf[_i] = zero;
  vec *k = buf;
  Hacl_Impl_Chacha20_vec2_chacha20_core(k, st);
  Hacl_Impl_Chacha20_state2_state_to_key_block(stream_block, k);
}

static void
Hacl_Impl_Chacha20_vec2_update_last(uint8_t *output, uint8_t *plain, uint32_t len, vec *st)
{
  KRML_CHECK_SIZE((uint8_t )0, (uint32_t )16 * vec_size * (uint32_t )4);
  uint8_t block[(uint32_t )16 * vec_size * (uint32_t )4];
  memset(block, 0, (uint32_t )16 * vec_size * (uint32_t )4 * sizeof block[0]);
  Hacl_Impl_Chacha20_vec2_chacha20_block(block, st);
  uint8_t *mask = block;
  xor_bytes(output, plain, mask, len);
}

static void Hacl_Impl_Chacha20_vec2_xor_block(uint8_t *output, uint8_t *plain, vec *st)
{
  Hacl_Impl_Chacha20_state2_state_to_key(st);
  vec_xor16(output, plain, st, vec_size * (uint32_t )4);
  return;
}

static void Hacl_Impl_Chacha20_vec2_update(uint8_t *output, uint8_t *plain, vec *st)
{
  KRML_CHECK_SIZE(zero, (uint32_t )16);
  vec buf[16];
  for (uintmax_t _i = 0; _i < (uint32_t )16; ++_i)
    buf[_i] = zero;
  vec *k = buf;
  Hacl_Impl_Chacha20_vec2_chacha20_core(k, st);
  Hacl_Impl_Chacha20_vec2_xor_block(output, plain, k);
  Hacl_Impl_Chacha20_state2_state_incr(st);
}

static void
Hacl_Impl_Chacha20_vec2_chacha20_counter_mode_(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  vec *st
)
{
  if (len == (uint32_t )0)
    return;
  else
  {
    Hacl_Impl_Chacha20_vec2_update_last(output, plain, len, st);
    return;
  }
}

static void
Hacl_Impl_Chacha20_vec2_chacha20_counter_mode(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  vec *st,
  uint32_t ctr
)
{
  uint32_t bs = (uint32_t )16 * vec_size * (uint32_t )4;
  if (len < bs)
  {
    Hacl_Impl_Chacha20_vec2_chacha20_counter_mode_(output, plain, len, st);
    return;
  }
  else
  {
    uint8_t *b = plain;
    uint8_t *b_ = plain + bs;
    uint8_t *o = output;
    uint8_t *o_ = output + bs;
    Hacl_Impl_Chacha20_vec2_update(o, b, st);
    Hacl_Impl_Chacha20_vec2_chacha20_counter_mode(o_, b_, len - bs, st, ctr + vec_size);
    return;
  }
}

static void
Hacl_Impl_Chacha20_vec2_chacha20(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint8_t *k,
  uint8_t *n,
  uint32_t ctr
)
{
  KRML_CHECK_SIZE(zero, (uint32_t )16);
  vec buf[16];
  for (uintmax_t _i = 0; _i < (uint32_t )16; ++_i)
    buf[_i] = zero;
  vec *st = buf;
  Hacl_Impl_Chacha20_state2_state_setup(st, k, n, ctr);
  Hacl_Impl_Chacha20_vec2_chacha20_counter_mode(output, plain, len, st, ctr);
}

void Chacha20_vec2_chacha20_key_block(uint8_t *block, uint8_t *k, uint8_t *n, uint32_t ctr)
{
  KRML_CHECK_SIZE(zero, (uint32_t )16);
  vec buf[16];
  for (uintmax_t _i = 0; _i < (uint32_t )16; ++_i)
    buf[_i] = zero;
  vec *st = buf;
  Hacl_Impl_Chacha20_state2_state_setup(st, k, n, ctr);
  Hacl_Impl_Chacha20_vec2_chacha20_block(block, st);
}

void Chacha20_vec2_double_round(vec *st)
{
  Hacl_Impl_Chacha20_vec2_double_round(st);
  return;
}

void *Chacha20_vec2_value_at(uint8_t *m, FStar_HyperStack_mem h)
{
  return (void *)(uint8_t )0;
}

void
Chacha20_vec2_chacha20(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint8_t *k,
  uint8_t *n,
  uint32_t ctr
)
{
  Hacl_Impl_Chacha20_vec2_chacha20(output, plain, len, k, n, ctr);
  return;
}

void
Chacha20_vec_crypto_stream_xor_ic(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint8_t *n,
  uint8_t *k,
  uint32_t ctr
)
{
  Chacha20_vec2_chacha20(output, plain, len, k, n, ctr);
  return;
}

