#include "Poly1305_64.h"

static inline void Hacl_Bignum_Fsum_fsum_(uint64_t *a, uint64_t *b, uint32_t i)
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

static const FStar_UInt128_t
Hacl_Bignum_Modulo_mask_2_42 = FStar_Int_Cast_uint64_to_uint128((uint64_t )0x3ffffffffff);

static const uint64_t Hacl_Bignum_Modulo_mask_2_42_ = (uint64_t )0x3ffffffffff;

static inline void Hacl_Bignum_Modulo_reduce(uint64_t *b)
{
  uint64_t b0 = b[(uint32_t )0];
  b[(uint32_t )0] = (b0 << (uint32_t )4) + (b0 << (uint32_t )2);
}

static inline void Hacl_Bignum_Modulo_carry_top(uint64_t *b)
{
  uint64_t b2 = b[(uint32_t )2];
  uint64_t b0 = b[(uint32_t )0];
  uint64_t b2_42 = b2 >> (uint32_t )42;
  b[(uint32_t )2] = b2 & (uint64_t )0x3ffffffffff;
  b[(uint32_t )0] = (b2_42 << (uint32_t )2) + b2_42 + b0;
}

static inline void Hacl_Bignum_Modulo_carry_top_wide(FStar_UInt128_t *b)
{
  FStar_UInt128_t b2 = b[(uint32_t )2];
  FStar_UInt128_t b0 = b[(uint32_t )0];
  FStar_UInt128_t
  b2_ = FStar_UInt128_logand(b2, FStar_Int_Cast_uint64_to_uint128((uint64_t )0x3ffffffffff));
  uint64_t
  b2_42 = FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_shift_right(b2, (uint32_t )42));
  FStar_UInt128_t
  b0_ = FStar_UInt128_add(b0, FStar_Int_Cast_uint64_to_uint128((b2_42 << (uint32_t )2) + b2_42));
  b[(uint32_t )2] = b2_;
  b[(uint32_t )0] = b0_;
}

static inline void
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

static inline void Hacl_Bignum_Fproduct_shift_(uint64_t *output, uint32_t ctr)
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

static inline void Hacl_Bignum_Fproduct_shift(uint64_t *output)
{
  uint64_t tmp = output[(uint32_t )2];
  Hacl_Bignum_Fproduct_shift_(output, (uint32_t )2);
  output[(uint32_t )0] = tmp;
}

static inline void
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

static inline void Hacl_Bignum_Fproduct_carry_wide_(FStar_UInt128_t *tmp, uint32_t ctr)
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

static inline void Hacl_Bignum_Fproduct_carry_limb_(uint64_t *tmp, uint32_t ctr)
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

static inline void Hacl_Bignum_Fproduct_carry_0_to_1(uint64_t *output)
{
  uint64_t i0 = output[(uint32_t )0];
  uint64_t i1 = output[(uint32_t )1];
  uint64_t i0_ = i0 & ((uint64_t )1 << (uint32_t )44) - (uint64_t )1;
  uint64_t i1_ = i1 + (i0 >> (uint32_t )44);
  output[(uint32_t )0] = i0_;
  output[(uint32_t )1] = i1_;
}

static inline void Hacl_Bignum_Fmul_shift_reduce(uint64_t *output)
{
  Hacl_Bignum_Fproduct_shift(output);
  Hacl_Bignum_Modulo_reduce(output);
  return;
}

static inline void
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
    Hacl_Bignum_Fmul_mul_shift_reduce_(output, (void *)(void *)(uint8_t )0, input, input2, i);
    return;
  }
}

static inline void Hacl_Bignum_Fmul_fmul_(uint64_t *output, uint64_t *input, uint64_t *input2)
{
  FStar_UInt128_t t[3];
  for (uintmax_t i = 0; i < (uint32_t )3; ++i)
    t[i] = FStar_Int_Cast_uint64_to_uint128((uint64_t )0);
  void *input_init = (void *)(uint8_t )0;
  Hacl_Bignum_Fmul_mul_shift_reduce_(t,
    (void *)(void *)(uint8_t )0,
    input,
    input2,
    (uint32_t )3);
  Hacl_Bignum_Fproduct_carry_wide_(t, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top_wide(t);
  Hacl_Bignum_Fproduct_copy_from_wide_(output, t, (uint32_t )3);
  Hacl_Bignum_Fproduct_carry_0_to_1(output);
}

static inline void Hacl_Bignum_Fmul_fmul(uint64_t *output, uint64_t *input, uint64_t *input2)
{
  uint64_t tmp[3] = { 0 };
  memcpy(tmp, input, (uint32_t )3 * sizeof input[0]);
  Hacl_Bignum_Fmul_fmul_(output, tmp, input2);
}

static inline void Hacl_Bignum_AddAndMultiply_add_and_multiply(uint64_t *acc, uint64_t *block, uint64_t *r)
{
  Hacl_Bignum_Fsum_fsum_(acc, block, (uint32_t )3);
  Hacl_Bignum_Fmul_fmul(acc, acc, r);
  return;
}


static inline bool Hacl_MAC_Poly1305_64_uu___is_MkState(Hacl_MAC_Poly1305_64_poly1305_state projectee)
{
  return true;
}

static inline uint64_t
*Hacl_MAC_Poly1305_64___proj__MkState__item__r(Hacl_MAC_Poly1305_64_poly1305_state projectee)
{
  Hacl_MAC_Poly1305_64_poly1305_state scrut = projectee;
  uint64_t *r = scrut.x00;
  uint64_t *h = scrut.x01;
  return r;
}

static inline uint64_t
*Hacl_MAC_Poly1305_64___proj__MkState__item__h(Hacl_MAC_Poly1305_64_poly1305_state projectee)
{
  Hacl_MAC_Poly1305_64_poly1305_state scrut = projectee;
  uint64_t *r = scrut.x00;
  uint64_t *h = scrut.x01;
  return h;
}

static inline uint64_t Hacl_MAC_Poly1305_64_load64_le(uint8_t *b)
{
  return le64toh(load64(b));
}

static inline void Hacl_MAC_Poly1305_64_store64_le(uint8_t *b, uint64_t z)
{
  store64(b,htole64(z));
}

static inline Prims_nat Hacl_MAC_Poly1305_64_sel_int(FStar_HyperStack_mem h, uint64_t *b)
{
  return (Prims_nat )(uint8_t )0;
}

static inline void Hacl_MAC_Poly1305_64_upd_3(uint64_t *b, uint64_t b0, uint64_t b1, uint64_t b2)
{
  b[(uint32_t )0] = b0;
  b[(uint32_t )1] = b1;
  b[(uint32_t )2] = b2;
}

static void Hacl_MAC_Poly1305_64_poly1305_encode_r(uint64_t *r, uint8_t *key)
{
  uint64_t t0 = Hacl_MAC_Poly1305_64_load64_le(key + (uint32_t )0);
  uint64_t t1 = Hacl_MAC_Poly1305_64_load64_le(key + (uint32_t )8);
  uint64_t r0 = t0 & (uint64_t )0xffc0fffffff;
  uint64_t r1 = (t0 >> (uint32_t )44 | t1 << (uint32_t )20) & (uint64_t )0xfffffc0ffff;
  uint64_t r2 = t1 >> (uint32_t )24 & (uint64_t )0x00ffffffc0f;
  Hacl_MAC_Poly1305_64_upd_3(r, r0, r1, r2);
  return;
}

static const uint64_t Hacl_MAC_Poly1305_64_mask_42 = (uint64_t )0x3ffffffffff;

static const uint64_t Hacl_MAC_Poly1305_64_mask_44 = (uint64_t )0xfffffffffff;

static void Hacl_MAC_Poly1305_64_toField(uint64_t *b, uint8_t *m)
{
  uint64_t t0 = Hacl_MAC_Poly1305_64_load64_le(m + (uint32_t )0);
  uint64_t t1 = Hacl_MAC_Poly1305_64_load64_le(m + (uint32_t )8);
  uint64_t t_0 = t0 & (uint64_t )0xfffffffffff;
  uint64_t t_1 = (t0 >> (uint32_t )44 | t1 << (uint32_t )20) & (uint64_t )0xfffffffffff;
  uint64_t t_2 = t1 >> (uint32_t )24;
  Hacl_MAC_Poly1305_64_upd_3(b, t_0, t_1, t_2);
  return;
}

static void Hacl_MAC_Poly1305_64_toField_plus_2_128(uint64_t *b, uint8_t *m)
{
  Hacl_MAC_Poly1305_64_toField(b, m);
  uint64_t b2 = b[(uint32_t )2];
  uint64_t b2_ = (uint64_t )0x10000000000 | b2;
  b[(uint32_t )2] = b2_;
}

static void Hacl_MAC_Poly1305_64_poly1305_start(uint64_t *a)
{
  Hacl_MAC_Poly1305_64_upd_3(a, (uint64_t )0, (uint64_t )0, (uint64_t )0);
  return;
}

static void Hacl_MAC_Poly1305_64_poly1305_init_(Hacl_MAC_Poly1305_64_poly1305_state st, uint8_t *key)
{
  Hacl_MAC_Poly1305_64_poly1305_encode_r(Hacl_MAC_Poly1305_64___proj__MkState__item__r(st),
    key + (uint32_t )0);
  Hacl_MAC_Poly1305_64_poly1305_start(Hacl_MAC_Poly1305_64___proj__MkState__item__h(st));
  return;
}

static void
Hacl_MAC_Poly1305_64_poly1305_update(
  void *log,
  Hacl_MAC_Poly1305_64_poly1305_state st,
  uint8_t *m
)
{
  uint64_t tmp[3] = { 0 };
  uint64_t *acc = Hacl_MAC_Poly1305_64___proj__MkState__item__h(st);
  uint64_t *r = Hacl_MAC_Poly1305_64___proj__MkState__item__r(st);
  Hacl_MAC_Poly1305_64_toField_plus_2_128(tmp, m + (uint32_t )0);
  Hacl_Bignum_AddAndMultiply_add_and_multiply(acc, tmp, r);
}

static void
Hacl_MAC_Poly1305_64_poly1305_blocks(
  void *log,
  Hacl_MAC_Poly1305_64_poly1305_state st,
  uint8_t *m,
  uint64_t len
)
{
  if (len < (uint64_t )16)
    return;
  else
  {
    void *new_log = (Hacl_MAC_Poly1305_64_poly1305_update((void *)0, st, m) , (void *)0);
    uint64_t len0 = len - (uint64_t )16;
    uint8_t *m0 = m + (uint32_t )16;
    Hacl_MAC_Poly1305_64_poly1305_blocks((void *)0, st, m0, len0);
    return;
  }
}

static void Hacl_MAC_Poly1305_64_poly1305_concat(uint8_t *b, uint8_t *m, uint64_t len)
{
  uint32_t i = (uint32_t )len;
  memcpy(b, m, i * sizeof m[0]);
}

static void
Hacl_MAC_Poly1305_64_poly1305_process_last_block_(
  uint8_t *block,
  Hacl_MAC_Poly1305_64_poly1305_state st,
  uint8_t *m,
  uint64_t rem_
)
{
  uint64_t tmp[3] = { 0 };
  Hacl_MAC_Poly1305_64_toField(tmp, block);
  Hacl_Bignum_AddAndMultiply_add_and_multiply(Hacl_MAC_Poly1305_64___proj__MkState__item__h(st),
    tmp,
    Hacl_MAC_Poly1305_64___proj__MkState__item__r(st));
}

static void
Hacl_MAC_Poly1305_64_poly1305_process_last_block(
  Hacl_MAC_Poly1305_64_poly1305_state st,
  uint8_t *m,
  uint64_t rem_
)
{
  uint8_t zero = (uint8_t )0;
  uint8_t block[16];
  for (uintmax_t i = 0; i < (uint32_t )16; ++i)
    block[i] = zero;
  uint32_t i = (uint32_t )rem_;
  Hacl_MAC_Poly1305_64_poly1305_concat(block, m, rem_);
  block[i] = (uint8_t )1;
  Hacl_MAC_Poly1305_64_poly1305_process_last_block_(block, st, m, rem_);
}

static void Hacl_MAC_Poly1305_64_poly1305_last_pass(uint64_t *acc)
{
  Hacl_Bignum_Fproduct_carry_limb_(acc, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top(acc);
  Hacl_Bignum_Fproduct_carry_0_to_1(acc);
  return;
}

static void Hacl_MAC_Poly1305_64_store128_le(uint8_t *mac, FStar_UInt128_t mac_)
{
  uint64_t macl = FStar_Int_Cast_uint128_to_uint64(mac_);
  uint64_t
  mach = FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_shift_right(mac_, (uint32_t )64));
  Hacl_MAC_Poly1305_64_store64_le(mac + (uint32_t )0, macl);
  Hacl_MAC_Poly1305_64_store64_le(mac + (uint32_t )8, mach);
  return;
}

static void
Hacl_MAC_Poly1305_64_poly1305_finish__(
  void *log,
  Hacl_MAC_Poly1305_64_poly1305_state st,
  uint8_t *mac,
  uint8_t *m,
  uint64_t len,
  uint8_t *key_s
)
{
  uint64_t rem_ = len & (uint64_t )0xf;
  if (rem_ == (uint64_t )0)
    return;
  else
  {
    uint32_t start = (uint32_t )(len - rem_);
    uint8_t *last_block = m + start;
    Hacl_MAC_Poly1305_64_poly1305_process_last_block(st, m + start, rem_);
    return;
  }
}

static void
Hacl_MAC_Poly1305_64_poly1305_finish_(
  void *log,
  Hacl_MAC_Poly1305_64_poly1305_state st,
  uint8_t *mac,
  uint8_t *m,
  uint64_t len,
  uint8_t *key_s
)
{
  Hacl_MAC_Poly1305_64_poly1305_finish__((uint8_t *)0, st, mac, m, len, key_s);
  Hacl_MAC_Poly1305_64_poly1305_last_pass(Hacl_MAC_Poly1305_64___proj__MkState__item__h(st));
  uint64_t kl = Hacl_MAC_Poly1305_64_load64_le(key_s + (uint32_t )0);
  uint64_t kh = Hacl_MAC_Poly1305_64_load64_le(key_s + (uint32_t )8);
  uint64_t h0 = Hacl_MAC_Poly1305_64___proj__MkState__item__h(st)[(uint32_t )0];
  uint64_t h1 = Hacl_MAC_Poly1305_64___proj__MkState__item__h(st)[(uint32_t )1];
  uint64_t h2 = Hacl_MAC_Poly1305_64___proj__MkState__item__h(st)[(uint32_t )2];
  uint64_t accl = h0 | h1 << (uint32_t )44;
  uint64_t acch = h1 >> (uint32_t )20 | h2 << (uint32_t )24;
  FStar_UInt128_t
  acc_ =
    FStar_UInt128_logor(FStar_Int_Cast_uint64_to_uint128(accl),
      FStar_UInt128_shift_left(FStar_Int_Cast_uint64_to_uint128(acch), (uint32_t )64));
  FStar_UInt128_t
  k_ =
    FStar_UInt128_logor(FStar_Int_Cast_uint64_to_uint128(kl),
      FStar_UInt128_shift_left(FStar_Int_Cast_uint64_to_uint128(kh), (uint32_t )64));
  FStar_UInt128_t mac_ = FStar_UInt128_add_mod(acc_, k_);
  Hacl_MAC_Poly1305_64_store128_le(mac, mac_);
  return;
}

void
Hacl_MAC_Poly1305_64_crypto_onetimeauth(
  uint8_t *output,
  uint8_t *input,
  uint64_t len,
  uint8_t *k
)
{
  uint64_t zero = (uint64_t )0;
  uint64_t buf[6];
  for (uintmax_t i = 0; i < (uint32_t )6; ++i)
    buf[i] = zero;
  uint64_t *r = buf + (uint32_t )0;
  uint64_t *h = buf + (uint32_t )3;
  Hacl_MAC_Poly1305_64_poly1305_state st = { .x00 = r, .x01 = h };
  uint8_t *key_r = k + (uint32_t )0;
  uint8_t *key_s = k + (uint32_t )16;
  void *init_log = (Hacl_MAC_Poly1305_64_poly1305_init_(st, k) , (void *)0);
  void
  *partial_log = (Hacl_MAC_Poly1305_64_poly1305_blocks((uint8_t *)0, st, input, len) , (void *)0);
  void
  *final_log =
    (Hacl_MAC_Poly1305_64_poly1305_finish_((uint8_t *)0, st, output, input, len, key_s) , (void *)0);
}

