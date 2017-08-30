#include "Chacha20_Vec128.h"

inline static void Hacl_Impl_Chacha20_Vec128_State_state_incr(vec *k)
{
  vec k3 = k[3];
  k[3] = vec_add(k3, one_le);
}

inline static void
Hacl_Impl_Chacha20_Vec128_State_state_to_key_block(uint8_t *stream_block, vec *k)
{
  vec k0 = k[0];
  vec k1 = k[1];
  vec k2 = k[2];
  vec k3 = k[3];
  uint8_t *a = stream_block;
  uint8_t *b = stream_block + (uint32_t )16;
  uint8_t *c = stream_block + (uint32_t )32;
  uint8_t *d = stream_block + (uint32_t )48;
  vec_store_le(a, k0);
  vec_store_le(b, k1);
  vec_store_le(c, k2);
  vec_store_le(d, k3);
}

inline static void
Hacl_Impl_Chacha20_Vec128_State_state_setup(vec *st, uint8_t *k, uint8_t *n1, uint32_t c)
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
  uint32_t n0 = load32_le(n1);
  uint8_t *x00 = n1 + (uint32_t )4;
  uint32_t n10 = load32_le(x00);
  uint8_t *x0 = n1 + (uint32_t )8;
  uint32_t n2 = load32_le(x0);
  vec v1 = vec_load_32x4(c, n0, n10, n2);
  st[3] = v1;
}

inline static void
Hacl_Impl_Chacha20_Vec128_line(vec *st, uint32_t a, uint32_t b, uint32_t d, uint32_t s)
{
  vec sa = st[a];
  vec sb = st[b];
  vec sd = st[d];
  vec sa1 = vec_add(sa, sb);
  vec sd1 = vec_rotate_left(vec_xor(sd, sa1), s);
  st[a] = sa1;
  st[d] = sd1;
}

inline static void Hacl_Impl_Chacha20_Vec128_round(vec *st)
{
  Hacl_Impl_Chacha20_Vec128_line(st, (uint32_t )0, (uint32_t )1, (uint32_t )3, (uint32_t )16);
  Hacl_Impl_Chacha20_Vec128_line(st, (uint32_t )2, (uint32_t )3, (uint32_t )1, (uint32_t )12);
  Hacl_Impl_Chacha20_Vec128_line(st, (uint32_t )0, (uint32_t )1, (uint32_t )3, (uint32_t )8);
  Hacl_Impl_Chacha20_Vec128_line(st, (uint32_t )2, (uint32_t )3, (uint32_t )1, (uint32_t )7);
}

inline static void Hacl_Impl_Chacha20_Vec128_double_round(vec *st)
{
  Hacl_Impl_Chacha20_Vec128_round(st);
  vec r1 = st[1];
  vec r20 = st[2];
  vec r30 = st[3];
  st[1] = vec_shuffle_right(r1, (uint32_t )1);
  st[2] = vec_shuffle_right(r20, (uint32_t )2);
  st[3] = vec_shuffle_right(r30, (uint32_t )3);
  Hacl_Impl_Chacha20_Vec128_round(st);
  vec r10 = st[1];
  vec r2 = st[2];
  vec r3 = st[3];
  st[1] = vec_shuffle_right(r10, (uint32_t )3);
  st[2] = vec_shuffle_right(r2, (uint32_t )2);
  st[3] = vec_shuffle_right(r3, (uint32_t )1);
}

inline static void Hacl_Impl_Chacha20_Vec128_double_round3(vec *st, vec *st_, vec *st__)
{
  Hacl_Impl_Chacha20_Vec128_double_round(st);
  Hacl_Impl_Chacha20_Vec128_double_round(st_);
  Hacl_Impl_Chacha20_Vec128_double_round(st__);
}

inline static void Hacl_Impl_Chacha20_Vec128_sum_states(vec *st_, vec *st)
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

inline static void Hacl_Impl_Chacha20_Vec128_copy_state(vec *st_, vec *st)
{
  vec uu____3478 = st[0];
  st_[0] = uu____3478;
  vec uu____3520 = st[1];
  st_[1] = uu____3520;
  vec uu____3562 = st[2];
  st_[2] = uu____3562;
  vec uu____3604 = st[3];
  st_[3] = uu____3604;
}

inline static void Hacl_Impl_Chacha20_Vec128_chacha20_core(vec *k, vec *st)
{
  Hacl_Impl_Chacha20_Vec128_copy_state(k, st);
  for (uint32_t i = (uint32_t )0; i < (uint32_t )10; i = i + (uint32_t )1)
    Hacl_Impl_Chacha20_Vec128_double_round(k);
  Hacl_Impl_Chacha20_Vec128_sum_states(k, st);
}

static void Hacl_Impl_Chacha20_Vec128_state_incr(vec *st)
{
  Hacl_Impl_Chacha20_Vec128_State_state_incr(st);
}

inline static void Hacl_Impl_Chacha20_Vec128_chacha20_incr3(vec *k0, vec *k1, vec *k2, vec *st)
{
  Hacl_Impl_Chacha20_Vec128_copy_state(k0, st);
  Hacl_Impl_Chacha20_Vec128_copy_state(k1, st);
  Hacl_Impl_Chacha20_Vec128_state_incr(k1);
  Hacl_Impl_Chacha20_Vec128_copy_state(k2, k1);
  Hacl_Impl_Chacha20_Vec128_state_incr(k2);
}

inline static void Hacl_Impl_Chacha20_Vec128_chacha20_sum3(vec *k0, vec *k1, vec *k2, vec *st)
{
  Hacl_Impl_Chacha20_Vec128_sum_states(k0, st);
  Hacl_Impl_Chacha20_Vec128_state_incr(st);
  Hacl_Impl_Chacha20_Vec128_sum_states(k1, st);
  Hacl_Impl_Chacha20_Vec128_state_incr(st);
  Hacl_Impl_Chacha20_Vec128_sum_states(k2, st);
}

inline static void Hacl_Impl_Chacha20_Vec128_chacha20_core3(vec *k0, vec *k1, vec *k2, vec *st)
{
  Hacl_Impl_Chacha20_Vec128_chacha20_incr3(k0, k1, k2, st);
  for (uint32_t i = (uint32_t )0; i < (uint32_t )10; i = i + (uint32_t )1)
    Hacl_Impl_Chacha20_Vec128_double_round3(k0, k1, k2);
  Hacl_Impl_Chacha20_Vec128_chacha20_sum3(k0, k1, k2, st);
}

inline static void Hacl_Impl_Chacha20_Vec128_chacha20_block(uint8_t *stream_block, vec *st)
{
  KRML_CHECK_SIZE(zero, (uint32_t )4);
  vec k[4];
  for (uintmax_t _i = 0; _i < (uint32_t )4; ++_i)
    k[_i] = zero;
  Hacl_Impl_Chacha20_Vec128_chacha20_core(k, st);
  Hacl_Impl_Chacha20_Vec128_State_state_to_key_block(stream_block, k);
}

inline static void
Hacl_Impl_Chacha20_Vec128_init(vec *st, uint8_t *k, uint8_t *n1, uint32_t ctr)
{
  Hacl_Impl_Chacha20_Vec128_State_state_setup(st, k, n1, ctr);
}

static void
Hacl_Impl_Chacha20_Vec128_update_last(uint8_t *output, uint8_t *plain, uint32_t len, vec *st)
{
  uint8_t block[64] = { 0 };
  Hacl_Impl_Chacha20_Vec128_chacha20_block(block, st);
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
Hacl_Impl_Chacha20_Vec128_store_4_vec(uint8_t *output, vec v0, vec v1, vec v2, vec v3)
{
  uint8_t *o0 = output;
  uint8_t *o1 = output + (uint32_t )16;
  uint8_t *o2 = output + (uint32_t )32;
  uint8_t *o3 = output + (uint32_t )48;
  vec_store_le(o0, v0);
  vec_store_le(o1, v1);
  vec_store_le(o2, v2);
  vec_store_le(o3, v3);
}

static void Hacl_Impl_Chacha20_Vec128_xor_block(uint8_t *output, uint8_t *plain, vec *st)
{
  vec p0 = vec_load_le(plain);
  vec p1 = vec_load_le(plain + (uint32_t )16);
  vec p2 = vec_load_le(plain + (uint32_t )32);
  vec p3 = vec_load_le(plain + (uint32_t )48);
  vec k0 = st[0];
  vec k1 = st[1];
  vec k2 = st[2];
  vec k3 = st[3];
  vec o0 = vec_xor(p0, k0);
  vec o1 = vec_xor(p1, k1);
  vec o2 = vec_xor(p2, k2);
  vec o3 = vec_xor(p3, k3);
  Hacl_Impl_Chacha20_Vec128_store_4_vec(output, o0, o1, o2, o3);
}

static void Hacl_Impl_Chacha20_Vec128_update(uint8_t *output, uint8_t *plain, vec *st)
{
  KRML_CHECK_SIZE(zero, (uint32_t )4);
  vec k[4];
  for (uintmax_t _i = 0; _i < (uint32_t )4; ++_i)
    k[_i] = zero;
  Hacl_Impl_Chacha20_Vec128_chacha20_core(k, st);
  Hacl_Impl_Chacha20_Vec128_xor_block(output, plain, k);
}

static void Hacl_Impl_Chacha20_Vec128_update3(uint8_t *output, uint8_t *plain, vec *st)
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
  Hacl_Impl_Chacha20_Vec128_chacha20_core3(k0, k1, k2, st);
  uint8_t *p0 = plain;
  uint8_t *p1 = plain + (uint32_t )64;
  uint8_t *p2 = plain + (uint32_t )128;
  uint8_t *o0 = output;
  uint8_t *o1 = output + (uint32_t )64;
  uint8_t *o2 = output + (uint32_t )128;
  Hacl_Impl_Chacha20_Vec128_xor_block(o0, p0, k0);
  Hacl_Impl_Chacha20_Vec128_xor_block(o1, p1, k1);
  Hacl_Impl_Chacha20_Vec128_xor_block(o2, p2, k2);
}

static void
Hacl_Impl_Chacha20_Vec128_update3_(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  vec *st,
  uint32_t i
)
{
  uint8_t *out_block = output + (uint32_t )192 * i;
  uint8_t *plain_block = plain + (uint32_t )192 * i;
  Hacl_Impl_Chacha20_Vec128_update3(out_block, plain_block, st);
  Hacl_Impl_Chacha20_Vec128_state_incr(st);
}

static void
Hacl_Impl_Chacha20_Vec128_chacha20_counter_mode_blocks3(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  vec *st
)
{
  for (uint32_t i = (uint32_t )0; i < len; i = i + (uint32_t )1)
    Hacl_Impl_Chacha20_Vec128_update3_(output, plain, len, st, i);
}

static void
Hacl_Impl_Chacha20_Vec128_chacha20_counter_mode_blocks(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  vec *st
)
{
  uint32_t len3 = len / (uint32_t )3;
  uint32_t rest3 = len % (uint32_t )3;
  uint8_t *plain_ = plain;
  uint8_t *blocks1 = plain + (uint32_t )192 * len3;
  uint8_t *output_ = output;
  uint8_t *outs = output + (uint32_t )192 * len3;
  Hacl_Impl_Chacha20_Vec128_chacha20_counter_mode_blocks3(output_, plain_, len3, st);
  if (rest3 == (uint32_t )2)
  {
    uint8_t *block0 = blocks1;
    uint8_t *block1 = blocks1 + (uint32_t )64;
    uint8_t *out0 = outs;
    uint8_t *out1 = outs + (uint32_t )64;
    Hacl_Impl_Chacha20_Vec128_update(out0, block0, st);
    Hacl_Impl_Chacha20_Vec128_state_incr(st);
    Hacl_Impl_Chacha20_Vec128_update(out1, block1, st);
    Hacl_Impl_Chacha20_Vec128_state_incr(st);
  }
  else if (rest3 == (uint32_t )1)
  {
    Hacl_Impl_Chacha20_Vec128_update(outs, blocks1, st);
    Hacl_Impl_Chacha20_Vec128_state_incr(st);
  }
}

static void
Hacl_Impl_Chacha20_Vec128_chacha20_counter_mode(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  vec *st
)
{
  uint32_t blocks_len = len >> (uint32_t )6;
  uint32_t part_len = len & (uint32_t )0x3f;
  uint8_t *output_ = output;
  uint8_t *plain_ = plain;
  uint8_t *output__ = output + (uint32_t )64 * blocks_len;
  uint8_t *plain__ = plain + (uint32_t )64 * blocks_len;
  Hacl_Impl_Chacha20_Vec128_chacha20_counter_mode_blocks(output_, plain_, blocks_len, st);
  if (part_len > (uint32_t )0)
    Hacl_Impl_Chacha20_Vec128_update_last(output__, plain__, part_len, st);
}

static void
Hacl_Impl_Chacha20_Vec128_chacha20(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint8_t *k,
  uint8_t *n1,
  uint32_t ctr
)
{
  KRML_CHECK_SIZE(zero, (uint32_t )4);
  vec buf[4];
  for (uintmax_t _i = 0; _i < (uint32_t )4; ++_i)
    buf[_i] = zero;
  vec *st = buf;
  Hacl_Impl_Chacha20_Vec128_init(st, k, n1, ctr);
  Hacl_Impl_Chacha20_Vec128_chacha20_counter_mode(output, plain, len, st);
}

void *Chacha20_Vec128_op_String_Access(FStar_Monotonic_HyperStack_mem h, uint8_t *b)
{
  return (void *)(uint8_t )0;
}

void
Chacha20_Vec128_chacha20(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint8_t *k,
  uint8_t *n1,
  uint32_t ctr
)
{
  Hacl_Impl_Chacha20_Vec128_chacha20(output, plain, len, k, n1, ctr);
}

