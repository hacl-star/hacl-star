#include "Poly1305_64.h"

inline static void Hacl_Bignum_Fsum_fsum_(uint64_t *a, uint64_t *b, uint32_t i)
{
  if (i == (uint32_t )0)
    return;
  else
  {
    uint32_t i0 = i - (uint32_t )1;
    uint64_t ai = a[i0];
    uint64_t bi = b[i0];
    a[i0] = ai + bi;
    Hacl_Bignum_Fsum_fsum_(a, b, i0);
    return;
  }
}

inline static void Hacl_Bignum_Modulo_reduce(uint64_t *b)
{
  uint64_t b0 = b[0];
  b[0] = (b0 << (uint32_t )4) + (b0 << (uint32_t )2);
}

inline static void Hacl_Bignum_Modulo_carry_top(uint64_t *b)
{
  uint64_t b2 = b[2];
  uint64_t b0 = b[0];
  uint64_t b2_42 = b2 >> (uint32_t )42;
  b[2] = b2 & (uint64_t )0x3ffffffffff;
  b[0] = (b2_42 << (uint32_t )2) + b2_42 + b0;
}

inline static void Hacl_Bignum_Modulo_carry_top_wide(FStar_UInt128_t *b)
{
  FStar_UInt128_t b2 = b[2];
  FStar_UInt128_t b0 = b[0];
  FStar_UInt128_t
  b2_ = FStar_UInt128_logand(b2, FStar_Int_Cast_uint64_to_uint128((uint64_t )0x3ffffffffff));
  uint64_t
  b2_42 = FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_shift_right(b2, (uint32_t )42));
  FStar_UInt128_t
  b0_ = FStar_UInt128_add(b0, FStar_Int_Cast_uint64_to_uint128((b2_42 << (uint32_t )2) + b2_42));
  b[2] = b2_;
  b[0] = b0_;
}

inline static void
Hacl_Bignum_Fproduct_copy_from_wide_(uint64_t *output, FStar_UInt128_t *input, uint32_t ctr)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    FStar_UInt128_t inputi = input[i];
    output[i] = FStar_Int_Cast_uint128_to_uint64(inputi);
    Hacl_Bignum_Fproduct_copy_from_wide_(output, input, i);
    return;
  }
}

inline static void Hacl_Bignum_Fproduct_shift_(uint64_t *output, uint32_t ctr)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint64_t z = output[ctr - (uint32_t )1];
    output[ctr] = z;
    Hacl_Bignum_Fproduct_shift_(output, ctr - (uint32_t )1);
    return;
  }
}

inline static void Hacl_Bignum_Fproduct_shift(uint64_t *output)
{
  uint64_t tmp = output[2];
  Hacl_Bignum_Fproduct_shift_(output, (uint32_t )2);
  output[0] = tmp;
}

inline static void
Hacl_Bignum_Fproduct_sum_scalar_multiplication_(
  FStar_UInt128_t *output,
  uint64_t *input,
  uint64_t s,
  uint32_t ctr
)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    FStar_UInt128_t oi = output[i];
    uint64_t ii = input[i];
    output[i] = FStar_UInt128_add(oi, FStar_UInt128_mul_wide(ii, s));
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, s, i);
    return;
  }
}

inline static void Hacl_Bignum_Fproduct_carry_wide_(FStar_UInt128_t *tmp, uint32_t ctr)
{
  if (ctr == (uint32_t )2)
    return;
  else
  {
    FStar_UInt128_t tctr = tmp[ctr];
    FStar_UInt128_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint64_t
    r0 = FStar_Int_Cast_uint128_to_uint64(tctr) & ((uint64_t )1 << (uint32_t )44) - (uint64_t )1;
    FStar_UInt128_t c = FStar_UInt128_shift_right(tctr, (uint32_t )44);
    tmp[ctr] = FStar_Int_Cast_uint64_to_uint128(r0);
    tmp[ctr + (uint32_t )1] = FStar_UInt128_add(tctrp1, c);
    Hacl_Bignum_Fproduct_carry_wide_(tmp, ctr + (uint32_t )1);
    return;
  }
}

inline static void Hacl_Bignum_Fproduct_carry_limb_(uint64_t *tmp, uint32_t ctr)
{
  if (ctr == (uint32_t )2)
    return;
  else
  {
    uint64_t tctr = tmp[ctr];
    uint64_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint64_t r0 = tctr & ((uint64_t )1 << (uint32_t )44) - (uint64_t )1;
    uint64_t c = tctr >> (uint32_t )44;
    tmp[ctr] = r0;
    tmp[ctr + (uint32_t )1] = tctrp1 + c;
    Hacl_Bignum_Fproduct_carry_limb_(tmp, ctr + (uint32_t )1);
    return;
  }
}

inline static void Hacl_Bignum_Fproduct_carry_0_to_1(uint64_t *output)
{
  uint64_t i0 = output[0];
  uint64_t i1 = output[1];
  uint64_t i0_ = i0 & ((uint64_t )1 << (uint32_t )44) - (uint64_t )1;
  uint64_t i1_ = i1 + (i0 >> (uint32_t )44);
  output[0] = i0_;
  output[1] = i1_;
}

inline static void Hacl_Bignum_Fmul_shift_reduce(uint64_t *output)
{
  Hacl_Bignum_Fproduct_shift(output);
  Hacl_Bignum_Modulo_reduce(output);
  return;
}

inline static void
Hacl_Bignum_Fmul_mul_shift_reduce_(
  FStar_UInt128_t *output,
  void *init_input,
  uint64_t *input,
  uint64_t *input2,
  uint32_t ctr
)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    uint32_t j = (uint32_t )2 - i;
    uint64_t input2i = input2[j];
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2i, (uint32_t )3);
    if (ctr > (uint32_t )1)
      Hacl_Bignum_Fmul_shift_reduce(input);
    Hacl_Bignum_Fmul_mul_shift_reduce_(output, (void *)(uint8_t )0, input, input2, i);
    return;
  }
}

inline static void Hacl_Bignum_Fmul_fmul_(uint64_t *output, uint64_t *input, uint64_t *input2)
{
  FStar_UInt128_t t[3];
  for (uintmax_t i = 0; i < (uint32_t )3; ++i)
    t[i] = FStar_Int_Cast_uint64_to_uint128((uint64_t )0);
  void
  *input_init =
    (void *)/* start inlining Hacl.Bignum.Fmul.get_seq */
      (void *)(uint8_t )0
    /* end inlining Hacl.Bignum.Fmul.get_seq */;
  Hacl_Bignum_Fmul_mul_shift_reduce_(t, (void *)(uint8_t )0, input, input2, (uint32_t )3);
  Hacl_Bignum_Fproduct_carry_wide_(t, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top_wide(t);
  Hacl_Bignum_Fproduct_copy_from_wide_(output, t, (uint32_t )3);
  Hacl_Bignum_Fproduct_carry_0_to_1(output);
}

inline static void Hacl_Bignum_Fmul_fmul(uint64_t *output, uint64_t *input, uint64_t *input2)
{
  uint64_t tmp[3] = { 0 };
  memcpy(tmp, input, (uint32_t )3 * sizeof input[0]);
  Hacl_Bignum_Fmul_fmul_(output, tmp, input2);
}

inline static void
Hacl_Bignum_AddAndMultiply_add_and_multiply(uint64_t *acc, uint64_t *block, uint64_t *r)
{
  Hacl_Bignum_Fsum_fsum_(acc, block, (uint32_t )3);
  Hacl_Bignum_Fmul_fmul(acc, acc, r);
  return;
}

static uint64_t
*Hacl_Impl_Poly1305_64___proj__MkState__item__r(Hacl_Impl_Poly1305_64_poly1305_state projectee)
{
  Hacl_Impl_Poly1305_64_poly1305_state scrut = projectee;
  uint64_t *r = scrut.x00;
  uint64_t *h = scrut.x01;
  return r;
}

static uint64_t
*Hacl_Impl_Poly1305_64___proj__MkState__item__h(Hacl_Impl_Poly1305_64_poly1305_state projectee)
{
  Hacl_Impl_Poly1305_64_poly1305_state scrut = projectee;
  uint64_t *r = scrut.x00;
  uint64_t *h = scrut.x01;
  return h;
}

inline static void
Hacl_Impl_Poly1305_64_upd_3(uint64_t *b, uint64_t b0, uint64_t b1, uint64_t b2)
{
  b[0] = b0;
  b[1] = b1;
  b[2] = b2;
}

inline static void Hacl_Impl_Poly1305_64_poly1305_encode_r(uint64_t *r, uint8_t *key)
{
  FStar_UInt128_t
  k =
    /* start inlining Hacl.Endianness.hload128_le */
      /* start inlining Hacl.Endianness.load128_le */
        load128_le(key)
      /* end inlining Hacl.Endianness.load128_le */
    /* end inlining Hacl.Endianness.hload128_le */;
  FStar_UInt128_t
  k_clamped =
    FStar_UInt128_logand(k,
      FStar_UInt128_logor(FStar_UInt128_shift_left(FStar_Int_Cast_uint64_to_uint128((uint64_t )0x0ffffffc0ffffffc),
          (uint32_t )64),
        FStar_Int_Cast_uint64_to_uint128((uint64_t )0x0ffffffc0fffffff)));
  uint64_t r0 = FStar_Int_Cast_uint128_to_uint64(k_clamped) & (uint64_t )0xfffffffffff;
  uint64_t
  r1 =
    FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_shift_right(k_clamped, (uint32_t )44))
    & (uint64_t )0xfffffffffff;
  uint64_t
  r2 = FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_shift_right(k_clamped, (uint32_t )88));
  Hacl_Impl_Poly1305_64_upd_3(r, r0, r1, r2);
  return;
}

inline static void Hacl_Impl_Poly1305_64_toField(uint64_t *b, uint8_t *block)
{
  FStar_UInt128_t
  m =
    /* start inlining Hacl.Endianness.hload128_le */
      /* start inlining Hacl.Endianness.load128_le */
        load128_le(block)
      /* end inlining Hacl.Endianness.load128_le */
    /* end inlining Hacl.Endianness.hload128_le */;
  uint64_t r0 = FStar_Int_Cast_uint128_to_uint64(m) & (uint64_t )0xfffffffffff;
  uint64_t
  r1 =
    FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_shift_right(m, (uint32_t )44))
    & (uint64_t )0xfffffffffff;
  uint64_t r2 = FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_shift_right(m, (uint32_t )88));
  Hacl_Impl_Poly1305_64_upd_3(b, r0, r1, r2);
  return;
}

inline static void Hacl_Impl_Poly1305_64_toField_plus_2_128(uint64_t *b, uint8_t *m)
{
  Hacl_Impl_Poly1305_64_toField(b, m);
  uint64_t b2 = b[2];
  uint64_t b2_ = (uint64_t )0x10000000000 | b2;
  b[2] = b2_;
}

static void Hacl_Impl_Poly1305_64_poly1305_start(uint64_t *a)
{
  Hacl_Impl_Poly1305_64_upd_3(a, (uint64_t )0, (uint64_t )0, (uint64_t )0);
  return;
}

void
Hacl_Impl_Poly1305_64_poly1305_init_(Hacl_Impl_Poly1305_64_poly1305_state st, uint8_t *key)
{
  Hacl_Impl_Poly1305_64_poly1305_encode_r(Hacl_Impl_Poly1305_64___proj__MkState__item__r(st),
    key);
  Hacl_Impl_Poly1305_64_poly1305_start(Hacl_Impl_Poly1305_64___proj__MkState__item__h(st));
  return;
}

void
Hacl_Impl_Poly1305_64_poly1305_update(
  void *log,
  Hacl_Impl_Poly1305_64_poly1305_state st,
  uint8_t *m
)
{
  uint64_t *acc = Hacl_Impl_Poly1305_64___proj__MkState__item__h(st);
  uint64_t *r = Hacl_Impl_Poly1305_64___proj__MkState__item__r(st);
  uint64_t tmp[3] = { 0 };
  Hacl_Impl_Poly1305_64_toField_plus_2_128(tmp, m);
  Hacl_Bignum_AddAndMultiply_add_and_multiply(acc, tmp, r);
  return;
}

inline static void Hacl_Impl_Poly1305_64_poly1305_concat(uint8_t *b, uint8_t *m, uint64_t len)
{
  uint32_t i = (uint32_t )len;
  memcpy(b, m, i * sizeof m[0]);
}

inline static void
Hacl_Impl_Poly1305_64_poly1305_process_last_block_(
  void *log,
  uint8_t *block,
  Hacl_Impl_Poly1305_64_poly1305_state st,
  uint8_t *m,
  uint64_t rem_
)
{
  uint64_t tmp[3] = { 0 };
  Hacl_Impl_Poly1305_64_toField(tmp, block);
  Hacl_Bignum_AddAndMultiply_add_and_multiply(Hacl_Impl_Poly1305_64___proj__MkState__item__h(st),
    tmp,
    Hacl_Impl_Poly1305_64___proj__MkState__item__r(st));
  return;
}

static void
Hacl_Impl_Poly1305_64_poly1305_process_last_block(
  void *log,
  Hacl_Impl_Poly1305_64_poly1305_state st,
  uint8_t *m,
  uint64_t rem_
)
{
  uint8_t zero = (uint8_t )0;
  uint8_t block[16];
  for (uintmax_t i = 0; i < (uint32_t )16; ++i)
    block[i] = zero;
  uint32_t i = (uint32_t )rem_;
  Hacl_Impl_Poly1305_64_poly1305_concat(block, m, rem_);
  block[i] = (uint8_t )1;
  void
  *log_ =
    (Hacl_Impl_Poly1305_64_poly1305_process_last_block_((void *)(uint8_t )0,
      block,
      st,
      m,
      rem_)
    , (void *)0);
}

static void Hacl_Impl_Poly1305_64_poly1305_last_pass_(uint64_t *acc)
{
  uint64_t a0 = acc[0];
  uint64_t a1 = acc[1];
  uint64_t a2 = acc[2];
  uint64_t mask0 = FStar_UInt64_gte_mask(a0, (uint64_t )0xffffffffffb);
  uint64_t mask1 = FStar_UInt64_eq_mask(a1, (uint64_t )0xfffffffffff);
  uint64_t mask2 = FStar_UInt64_eq_mask(a2, (uint64_t )0x3ffffffffff);
  uint64_t mask = mask0 & mask1 & mask2;
  uint64_t a0_ = a0 - ((uint64_t )0xffffffffffb & mask);
  uint64_t a1_ = a1 - ((uint64_t )0xfffffffffff & mask);
  uint64_t a2_ = a2 - ((uint64_t )0x3ffffffffff & mask);
  Hacl_Impl_Poly1305_64_upd_3(acc, a0_, a1_, a2_);
  return;
}

inline static void Hacl_Impl_Poly1305_64_carry_limb_unrolled(uint64_t *acc)
{
  uint64_t a0 = acc[0];
  uint64_t a1 = acc[1];
  uint64_t a2 = acc[2];
  uint64_t a0_ = a0 & (uint64_t )0xfffffffffff;
  uint64_t r0 = a0 >> (uint32_t )44;
  uint64_t a1_ = a1 + r0 & (uint64_t )0xfffffffffff;
  uint64_t r1 = a1 + r0 >> (uint32_t )44;
  uint64_t a2_ = a2 + r1;
  Hacl_Impl_Poly1305_64_upd_3(acc, a0_, a1_, a2_);
  return;
}

static void Hacl_Impl_Poly1305_64_carry_last_unrolled(uint64_t *acc)
{
  Hacl_Bignum_Modulo_carry_top(acc);
  Hacl_Bignum_Fproduct_carry_0_to_1(acc);
  return;
}

static void Hacl_Impl_Poly1305_64_poly1305_last_pass(uint64_t *acc)
{
  Hacl_Bignum_Fproduct_carry_limb_(acc, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top(acc);
  Hacl_Impl_Poly1305_64_carry_limb_unrolled(acc);
  Hacl_Impl_Poly1305_64_carry_last_unrolled(acc);
  Hacl_Impl_Poly1305_64_poly1305_last_pass_(acc);
  return;
}

static FStar_UInt128_t Hacl_Impl_Poly1305_64_bignum_to_128(uint64_t *acc)
{
  uint64_t h0 = acc[0];
  uint64_t h1 = acc[1];
  uint64_t h2 = acc[2];
  return
    FStar_UInt128_logor(FStar_UInt128_shift_left(FStar_Int_Cast_uint64_to_uint128(h2
          << (uint32_t )24
          | h1 >> (uint32_t )20),
        (uint32_t )64),
      FStar_Int_Cast_uint64_to_uint128(h1 << (uint32_t )44 | h0));
}

void
Hacl_Impl_Poly1305_64_poly1305_finish__(
  void *log,
  Hacl_Impl_Poly1305_64_poly1305_state st,
  uint8_t *mac,
  uint8_t *m,
  uint64_t len,
  uint8_t *key_s
)
{
  void *ite;
  if (len == (uint64_t )0)
    ite = (void *)(uint8_t )0;
  else
    ite =
      (void *)(Hacl_Impl_Poly1305_64_poly1305_process_last_block((void *)(uint8_t )0,
        st,
        m,
        len)
      , (void *)0);
  return;
}

void
Hacl_Impl_Poly1305_64_poly1305_finish_(
  void *log,
  Hacl_Impl_Poly1305_64_poly1305_state st,
  uint8_t *mac,
  uint8_t *m,
  uint64_t len,
  uint8_t *key_s
)
{
  uint64_t *acc = Hacl_Impl_Poly1305_64___proj__MkState__item__h(st);
  void
  *log_ =
    (Hacl_Impl_Poly1305_64_poly1305_finish__((void *)(uint8_t )0,
      st,
      mac,
      m,
      len,
      key_s)
    , (void *)0);
  Hacl_Impl_Poly1305_64_poly1305_last_pass(acc);
  FStar_UInt128_t
  k_ =
    /* start inlining Hacl.Endianness.hload128_le */
      /* start inlining Hacl.Endianness.load128_le */
        load128_le(key_s)
      /* end inlining Hacl.Endianness.load128_le */
    /* end inlining Hacl.Endianness.hload128_le */;
  FStar_UInt128_t acc_ = Hacl_Impl_Poly1305_64_bignum_to_128(acc);
  FStar_UInt128_t mac_ = FStar_UInt128_add_mod(acc_, k_);
  /* start inlining Hacl.Endianness.hstore128_le */
  /* start inlining Hacl.Endianness.store128_le */
  store128_le(mac, mac_);
  return;
  /* end inlining Hacl.Endianness.store128_le */
  /* end inlining Hacl.Endianness.hstore128_le */
}

static void
Hacl_Impl_Poly1305_64_poly1305_blocks(
  void *log,
  Hacl_Impl_Poly1305_64_poly1305_state st,
  uint8_t *m,
  uint64_t len
)
{
  void *ite;
  if (len == (uint64_t )0)
    ite = (void *)(uint8_t )0;
  else
  {
    void
    *new_log = (Hacl_Impl_Poly1305_64_poly1305_update((void *)(uint8_t )0, st, m) , (void *)0);
    uint64_t len0 = len - (uint64_t )1;
    uint8_t *m0 = m + (uint32_t )16;
    ite =
      (void *)(Hacl_Impl_Poly1305_64_poly1305_blocks((void *)(uint8_t )0, st, m0, len0) , (void *)0);
  }
  return;
}

void
Hacl_Impl_Poly1305_64_crypto_onetimeauth(
  uint8_t *output,
  uint8_t *input,
  uint64_t len,
  uint8_t *k
)
{
  uint64_t len16 = len >> (uint32_t )4;
  uint64_t rem16 = len & (uint64_t )0xf;
  uint8_t *partial_input = input;
  uint8_t *last_block = input + (uint32_t )16 * (uint32_t )len16;
  uint64_t buf[6] = { 0 };
  uint64_t *r = buf;
  uint64_t *h = buf + (uint32_t )3;
  Hacl_Impl_Poly1305_64_poly1305_state st = { .x00 = r, .x01 = h };
  uint8_t *key_r = k;
  uint8_t *key_s = k + (uint32_t )16;
  void *init_log = (Hacl_Impl_Poly1305_64_poly1305_init_(st, key_r) , (void *)0);
  void
  *partial_log =
    (Hacl_Impl_Poly1305_64_poly1305_blocks((void *)(uint8_t )0,
      st,
      partial_input,
      len16)
    , (void *)0);
  Hacl_Impl_Poly1305_64_poly1305_finish_((void *)(uint8_t )0,
    st,
    output,
    last_block,
    rem16,
    key_s);
}

void Poly1305_64_crypto_onetimeauth(uint8_t *output, uint8_t *input, uint64_t len, uint8_t *k)
{
  Hacl_Impl_Poly1305_64_crypto_onetimeauth(output, input, len, k);
  return;
}

