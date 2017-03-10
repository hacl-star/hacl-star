#include "Chacha20_vec.h"

inline static void Hacl_Impl_Chacha20_state_state_incr(vec *k)
{
  vec k3 = k[3];
  if (vec_size / (uint32_t )4 == (uint32_t )2)
    k[3] = vec_add(k3, two_le);
  else
    k[3] = vec_add(k3, one_le);
}

inline static void Hacl_Impl_Chacha20_state_state_to_key(vec *k)
{
  if (vec_size / (uint32_t )4 == (uint32_t )2)
  {
    vec k0 = k[0];
    vec k1 = k[1];
    vec k2 = k[2];
    vec k3 = k[3];
    k[0] = vec_choose_128(k0, k1, (uint32_t )0, (uint32_t )2);
    k[1] = vec_choose_128(k2, k3, (uint32_t )0, (uint32_t )2);
    k[2] = vec_choose_128(k0, k1, (uint32_t )1, (uint32_t )3);
    k[3] = vec_choose_128(k2, k3, (uint32_t )1, (uint32_t )3);
  }
  else
    return;
}

inline static void Hacl_Impl_Chacha20_state_state_to_key_block(uint8_t *stream_block, vec *k)
{
  Hacl_Impl_Chacha20_state_state_to_key(k);
  uint32_t bb = vec_size / (uint32_t )4 * (uint32_t )16;
  uint32_t bb2 = bb * (uint32_t )2;
  uint32_t bb3 = bb * (uint32_t )3;
  vec k0 = k[0];
  vec k1 = k[1];
  vec k2 = k[2];
  vec k3 = k[3];
  vec _0_41 = k[0];
  vec_store_le(stream_block, _0_41);
  vec _0_42 = k[1];
  vec_store_le(stream_block + bb, _0_42);
  vec _0_43 = k[2];
  vec_store_le(stream_block + bb2, _0_43);
  vec _0_44 = k[3];
  vec_store_le(stream_block + bb3, _0_44);
  return;
}

inline static void
Hacl_Impl_Chacha20_state_state_setup(vec *st, uint8_t *k, uint8_t *n, uint32_t c)
{
  st[0] =
    vec_load_32x4((uint32_t )0x61707865,
      (uint32_t )0x3320646e,
      (uint32_t )0x79622d32,
      (uint32_t )0x6b206574);
  vec k0 = vec_load128_le(k);
  vec k1 = vec_load128_le(k + (uint32_t )16);
  st[1] = k0;
  st[2] = k1;
  uint8_t *x00 = n;
  uint32_t n0 = load32_le(x00);
  uint8_t *x01 = n + (uint32_t )4;
  uint32_t n1 = load32_le(x01);
  uint8_t *x0 = n + (uint32_t )8;
  uint32_t n2 = load32_le(x0);
  vec v = vec_load_32x8(c, n0, n1, n2, c + (uint32_t )1, n0, n1, n2);
  st[3] = v;
}

inline static void
Hacl_Impl_Chacha20_vec_line(vec *st, uint32_t a, uint32_t b, uint32_t d, uint32_t s)
{
  vec sa0 = st[a];
  vec sb = st[b];
  vec sd0 = st[d];
  vec sa = vec_add(sa0, sb);
  vec sd = vec_rotate_left(vec_xor(sd0, sa), s);
  st[a] = sa;
  st[d] = sd;
}

inline static void Hacl_Impl_Chacha20_vec_round(vec *st)
{
  Hacl_Impl_Chacha20_vec_line(st, (uint32_t )0, (uint32_t )1, (uint32_t )3, (uint32_t )16);
  Hacl_Impl_Chacha20_vec_line(st, (uint32_t )2, (uint32_t )3, (uint32_t )1, (uint32_t )12);
  Hacl_Impl_Chacha20_vec_line(st, (uint32_t )0, (uint32_t )1, (uint32_t )3, (uint32_t )8);
  Hacl_Impl_Chacha20_vec_line(st, (uint32_t )2, (uint32_t )3, (uint32_t )1, (uint32_t )7);
  return;
}

inline static void Hacl_Impl_Chacha20_vec_double_round(vec *st)
{
  Hacl_Impl_Chacha20_vec_round(st);
  vec r1 = st[1];
  vec r20 = st[2];
  vec r30 = st[3];
  st[1] = vec_shuffle_right(r1, (uint32_t )1);
  st[2] = vec_shuffle_right(r20, (uint32_t )2);
  st[3] = vec_shuffle_right(r30, (uint32_t )3);
  Hacl_Impl_Chacha20_vec_round(st);
  vec r10 = st[1];
  vec r2 = st[2];
  vec r3 = st[3];
  st[1] = vec_shuffle_right(r10, (uint32_t )3);
  st[2] = vec_shuffle_right(r2, (uint32_t )2);
  st[3] = vec_shuffle_right(r3, (uint32_t )1);
}

inline static void Hacl_Impl_Chacha20_vec_sum_states(vec *st_, vec *st)
{
  vec s0 = st[0];
  vec s1 = st[1];
  vec s2 = st[2];
  vec s3 = st[3];
  vec s0_ = st_[0];
  vec s1_ = st_[1];
  vec s2_ = st_[2];
  vec s3_ = st_[3];
  st_[0] = vec_add(s0_, s0);
  st_[1] = vec_add(s1_, s1);
  st_[2] = vec_add(s2_, s2);
  st_[3] = vec_add(s3_, s3);
}

inline static void Hacl_Impl_Chacha20_vec_copy_state(vec *st_, vec *st)
{
  vec _0_45 = st[0];
  st_[0] = _0_45;
  vec _0_46 = st[1];
  st_[1] = _0_46;
  vec _0_47 = st[2];
  st_[2] = _0_47;
  vec _0_48 = st[3];
  st_[3] = _0_48;
}

inline static void Hacl_Impl_Chacha20_vec_chacha20_core(vec *k, vec *st)
{
  Hacl_Impl_Chacha20_vec_copy_state(k, st);
  rounds(k);
  Hacl_Impl_Chacha20_vec_sum_states(k, st);
  return;
}

inline static void Hacl_Impl_Chacha20_vec_chacha20_core2(vec *k0, vec *k1, vec *st)
{
  Hacl_Impl_Chacha20_vec_copy_state(k0, st);
  Hacl_Impl_Chacha20_vec_copy_state(k1, st);
  Hacl_Impl_Chacha20_state_state_incr(k1);
  rounds2(k0, k1);
  Hacl_Impl_Chacha20_vec_sum_states(k0, st);
  Hacl_Impl_Chacha20_state_state_incr(st);
  Hacl_Impl_Chacha20_vec_sum_states(k1, st);
  return;
}

inline static void Hacl_Impl_Chacha20_vec_chacha20_core3(vec *k0, vec *k1, vec *k2, vec *st)
{
  Hacl_Impl_Chacha20_vec_copy_state(k0, st);
  Hacl_Impl_Chacha20_vec_copy_state(k1, st);
  Hacl_Impl_Chacha20_state_state_incr(k1);
  Hacl_Impl_Chacha20_vec_copy_state(k2, k1);
  Hacl_Impl_Chacha20_state_state_incr(k2);
  rounds3(k0, k1, k2);
  Hacl_Impl_Chacha20_vec_sum_states(k0, st);
  Hacl_Impl_Chacha20_state_state_incr(st);
  Hacl_Impl_Chacha20_vec_sum_states(k1, st);
  Hacl_Impl_Chacha20_state_state_incr(st);
  Hacl_Impl_Chacha20_vec_sum_states(k2, st);
  return;
}

inline static void Hacl_Impl_Chacha20_vec_chacha20_block(uint8_t *stream_block, vec *st)
{
  KRML_CHECK_SIZE(zero, (uint32_t )4);
  vec k[4];
  for (uintmax_t _i = 0; _i < (uint32_t )4; ++_i)
    k[_i] = zero;
  Hacl_Impl_Chacha20_vec_chacha20_core(k, st);
  Hacl_Impl_Chacha20_state_state_to_key_block(stream_block, k);
}

static void
Hacl_Impl_Chacha20_vec_update_last(uint8_t *output, uint8_t *plain, uint32_t len, vec *st)
{
  KRML_CHECK_SIZE((uint8_t )0, vec_size * (uint32_t )4 * (uint32_t )4);
  uint8_t block[vec_size * (uint32_t )4 * (uint32_t )4];
  memset(block, 0, vec_size * (uint32_t )4 * (uint32_t )4 * sizeof block[0]);
  Hacl_Impl_Chacha20_vec_chacha20_block(block, st);
  uint8_t *mask = block;
  xor_bytes(output, plain, mask, len);
}

static void Hacl_Impl_Chacha20_vec_xor_block(uint8_t *output, uint8_t *plain, vec *st)
{
  Hacl_Impl_Chacha20_state_state_to_key(st);
  vec p0 = vec_load_le(plain);
  vec p1 = vec_load_le(plain + vec_size * (uint32_t )4);
  vec p2 = vec_load_le(plain + vec_size * (uint32_t )4 * (uint32_t )2);
  vec p3 = vec_load_le(plain + vec_size * (uint32_t )4 * (uint32_t )3);
  vec k0 = st[0];
  vec k1 = st[1];
  vec k2 = st[2];
  vec k3 = st[3];
  vec o0 = vec_xor(p0, k0);
  vec o1 = vec_xor(p1, k1);
  vec o2 = vec_xor(p2, k2);
  vec o3 = vec_xor(p3, k3);
  vec_store_le(output, o0);
  vec_store_le(output + vec_size * (uint32_t )4, o1);
  vec_store_le(output + vec_size * (uint32_t )4 * (uint32_t )2, o2);
  vec_store_le(output + vec_size * (uint32_t )4 * (uint32_t )3, o3);
  return;
}

static void Hacl_Impl_Chacha20_vec_update(uint8_t *output, uint8_t *plain, vec *st)
{
  KRML_CHECK_SIZE(zero, (uint32_t )4);
  vec k[4];
  for (uintmax_t _i = 0; _i < (uint32_t )4; ++_i)
    k[_i] = zero;
  Hacl_Impl_Chacha20_vec_chacha20_core(k, st);
  Hacl_Impl_Chacha20_vec_xor_block(output, plain, k);
  Hacl_Impl_Chacha20_state_state_incr(st);
}

static void Hacl_Impl_Chacha20_vec_update2(uint8_t *output, uint8_t *plain, vec *st)
{
  KRML_CHECK_SIZE(zero, (uint32_t )4);
  vec k[4];
  for (uintmax_t _i = 0; _i < (uint32_t )4; ++_i)
    k[_i] = zero;
  KRML_CHECK_SIZE(zero, (uint32_t )4);
  vec k_[4];
  for (uintmax_t _i = 0; _i < (uint32_t )4; ++_i)
    k_[_i] = zero;
  Hacl_Impl_Chacha20_vec_chacha20_core2(k, k_, st);
  Hacl_Impl_Chacha20_vec_xor_block(output, plain, k);
  Hacl_Impl_Chacha20_vec_xor_block(output + vec_size * (uint32_t )4 * (uint32_t )4,
    plain + vec_size * (uint32_t )4 * (uint32_t )4,
    k_);
  Hacl_Impl_Chacha20_state_state_incr(st);
}

static void Hacl_Impl_Chacha20_vec_update3(uint8_t *output, uint8_t *plain, vec *st)
{
  KRML_CHECK_SIZE(zero, (uint32_t )4);
  vec k0[4];
  for (uintmax_t _i = 0; _i < (uint32_t )4; ++_i)
    k0[_i] = zero;
  KRML_CHECK_SIZE(zero, (uint32_t )4);
  vec k1[4];
  for (uintmax_t _i = 0; _i < (uint32_t )4; ++_i)
    k1[_i] = zero;
  KRML_CHECK_SIZE(zero, (uint32_t )4);
  vec k2[4];
  for (uintmax_t _i = 0; _i < (uint32_t )4; ++_i)
    k2[_i] = zero;
  Hacl_Impl_Chacha20_vec_chacha20_core3(k0, k1, k2, st);
  Hacl_Impl_Chacha20_vec_xor_block(output, plain, k0);
  Hacl_Impl_Chacha20_vec_xor_block(output + vec_size * (uint32_t )4 * (uint32_t )4,
    plain + vec_size * (uint32_t )4 * (uint32_t )4,
    k1);
  Hacl_Impl_Chacha20_vec_xor_block(output + vec_size * (uint32_t )4 * (uint32_t )8,
    plain + vec_size * (uint32_t )4 * (uint32_t )8,
    k2);
  Hacl_Impl_Chacha20_state_state_incr(st);
}

static void
Hacl_Impl_Chacha20_vec_chacha20_counter_mode_(
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
    Hacl_Impl_Chacha20_vec_update_last(output, plain, len, st);
    return;
  }
}

static void
Hacl_Impl_Chacha20_vec_chacha20_counter_mode(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  vec *st,
  uint32_t ctr
)
{
  uint32_t bs = vec_size * (uint32_t )4 * (uint32_t )4;
  uint32_t bs2 = bs * (uint32_t )2;
  uint32_t bs3 = bs * (uint32_t )3;
  if (len < bs)
  {
    Hacl_Impl_Chacha20_vec_chacha20_counter_mode_(output, plain, len, st);
    return;
  }
  else if (len < bs2)
  {
    uint8_t *b = plain;
    uint8_t *b_ = plain + bs;
    uint8_t *o = output;
    uint8_t *o_ = output + bs;
    Hacl_Impl_Chacha20_vec_update(o, b, st);
    Hacl_Impl_Chacha20_vec_chacha20_counter_mode(o_,
      b_,
      len - bs,
      st,
      ctr + vec_size / (uint32_t )4);
    return;
  }
  else if (len < bs3)
  {
    uint8_t *b = plain;
    uint8_t *b_ = plain + bs2;
    uint8_t *o = output;
    uint8_t *o_ = output + bs2;
    Hacl_Impl_Chacha20_vec_update2(o, b, st);
    Hacl_Impl_Chacha20_vec_chacha20_counter_mode(o_,
      b_,
      len - bs2,
      st,
      ctr + (uint32_t )2 * vec_size / (uint32_t )4);
    return;
  }
  else
  {
    uint8_t *b = plain;
    uint8_t *b_ = plain + bs3;
    uint8_t *o = output;
    uint8_t *o_ = output + bs3;
    Hacl_Impl_Chacha20_vec_update3(o, b, st);
    Hacl_Impl_Chacha20_vec_chacha20_counter_mode(o_,
      b_,
      len - bs3,
      st,
      ctr + (uint32_t )3 * vec_size / (uint32_t )4);
    return;
  }
}

static void
Hacl_Impl_Chacha20_vec_chacha20(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint8_t *k,
  uint8_t *n,
  uint32_t ctr
)
{
  KRML_CHECK_SIZE(zero, (uint32_t )4);
  vec buf[4];
  for (uintmax_t _i = 0; _i < (uint32_t )4; ++_i)
    buf[_i] = zero;
  vec *st = buf;
  Hacl_Impl_Chacha20_state_state_setup(st, k, n, ctr);
  Hacl_Impl_Chacha20_vec_chacha20_counter_mode(output, plain, len, st, ctr);
}

void Chacha20_vec_chacha20_key_block(uint8_t *block, uint8_t *k, uint8_t *n, uint32_t ctr)
{
  KRML_CHECK_SIZE(zero, (uint32_t )4);
  vec buf[4];
  for (uintmax_t _i = 0; _i < (uint32_t )4; ++_i)
    buf[_i] = zero;
  vec *st = buf;
  Hacl_Impl_Chacha20_state_state_setup(st, k, n, ctr);
  Hacl_Impl_Chacha20_vec_chacha20_block(block, st);
}

void Chacha20_vec_double_round(vec *st)
{
  Hacl_Impl_Chacha20_vec_double_round(st);
  return;
}

void *Chacha20_vec_value_at(uint8_t *m, FStar_HyperStack_mem h)
{
  return (void *)(uint8_t )0;
}

void
Chacha20_vec_chacha20(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint8_t *k,
  uint8_t *n,
  uint32_t ctr
)
{
  Hacl_Impl_Chacha20_vec_chacha20(output, plain, len, k, n, ctr);
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
  Chacha20_vec_chacha20(output, plain, len, k, n, ctr);
  return;
}

