#include "Poly1305_32.h"

inline static void Hacl_Bignum_Fsum_fsum_(uint32_t *a, uint32_t *b, uint32_t i)
{
  if (i == (uint32_t )0)
    return;
  else
  {
    uint32_t i0 = i - (uint32_t )1;
    uint32_t ai = a[i0];
    uint32_t bi = b[i0];
    a[i0] = ai + bi;
    Hacl_Bignum_Fsum_fsum_(a, b, i0);
    return;
  }
}

static void Hacl_Bignum_Modulo_reduce(uint32_t *b)
{
  uint32_t b0 = b[0];
  b[0] = (b0 << (uint32_t )2) + b0;
}

static void Hacl_Bignum_Modulo_carry_top(uint32_t *b)
{
  uint32_t b4 = b[4];
  uint32_t b0 = b[0];
  uint32_t b4_26 = b4 >> (uint32_t )26;
  b[4] = b4 & (uint32_t )0x3ffffff;
  b[0] = (b4_26 << (uint32_t )2) + b4_26 + b0;
}

static void Hacl_Bignum_Modulo_carry_top_wide(uint64_t *b)
{
  uint64_t b4 = b[4];
  uint64_t b0 = b[0];
  uint64_t b4_ = b4 & (uint64_t )(uint32_t )0x3ffffff;
  uint32_t b4_26 = (uint32_t )(b4 >> (uint32_t )26);
  uint64_t b0_ = b0 + (uint64_t )((b4_26 << (uint32_t )2) + b4_26);
  b[4] = b4_;
  b[0] = b0_;
}

inline static void
Hacl_Bignum_Fproduct_copy_from_wide_(uint32_t *output, uint64_t *input, uint32_t ctr)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    uint64_t inputi = input[i];
    output[i] = (uint32_t )inputi;
    Hacl_Bignum_Fproduct_copy_from_wide_(output, input, i);
    return;
  }
}

inline static void Hacl_Bignum_Fproduct_shift_(uint32_t *output, uint32_t ctr)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t z = output[ctr - (uint32_t )1];
    output[ctr] = z;
    Hacl_Bignum_Fproduct_shift_(output, ctr - (uint32_t )1);
    return;
  }
}

inline static void Hacl_Bignum_Fproduct_shift(uint32_t *output)
{
  uint32_t tmp = output[4];
  Hacl_Bignum_Fproduct_shift_(output, (uint32_t )4);
  output[0] = tmp;
}

inline static void
Hacl_Bignum_Fproduct_sum_scalar_multiplication_(
  uint64_t *output,
  uint32_t *input,
  uint32_t s,
  uint32_t ctr
)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    uint64_t oi = output[i];
    uint32_t ii = input[i];
    output[i] = oi + (uint64_t )ii * (uint64_t )s;
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, s, i);
    return;
  }
}

inline static void Hacl_Bignum_Fproduct_carry_wide_(uint64_t *tmp, uint32_t ctr)
{
  if (ctr == (uint32_t )4)
    return;
  else
  {
    uint64_t tctr = tmp[ctr];
    uint64_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint32_t r0 = (uint32_t )tctr & ((uint32_t )1 << (uint32_t )26) - (uint32_t )1;
    uint64_t c = tctr >> (uint32_t )26;
    tmp[ctr] = (uint64_t )r0;
    tmp[ctr + (uint32_t )1] = tctrp1 + c;
    Hacl_Bignum_Fproduct_carry_wide_(tmp, ctr + (uint32_t )1);
    return;
  }
}

inline static void Hacl_Bignum_Fproduct_carry_limb_(uint32_t *tmp, uint32_t ctr)
{
  if (ctr == (uint32_t )4)
    return;
  else
  {
    uint32_t tctr = tmp[ctr];
    uint32_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint32_t r0 = tctr & ((uint32_t )1 << (uint32_t )26) - (uint32_t )1;
    uint32_t c = tctr >> (uint32_t )26;
    tmp[ctr] = r0;
    tmp[ctr + (uint32_t )1] = tctrp1 + c;
    Hacl_Bignum_Fproduct_carry_limb_(tmp, ctr + (uint32_t )1);
    return;
  }
}

inline static void Hacl_Bignum_Fproduct_carry_0_to_1(uint32_t *output)
{
  uint32_t i0 = output[0];
  uint32_t i1 = output[1];
  uint32_t i0_ = i0 & ((uint32_t )1 << (uint32_t )26) - (uint32_t )1;
  uint32_t i1_ = i1 + (i0 >> (uint32_t )26);
  output[0] = i0_;
  output[1] = i1_;
}

inline static void Hacl_Bignum_Fmul_shift_reduce(uint32_t *output)
{
  Hacl_Bignum_Fproduct_shift(output);
  Hacl_Bignum_Modulo_reduce(output);
  return;
}

inline static void
Hacl_Bignum_Fmul_mul_shift_reduce_(
  uint64_t *output,
  void *init_input,
  uint32_t *input,
  uint32_t *input2,
  uint32_t ctr
)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    uint32_t j = (uint32_t )4 - i;
    uint32_t input2i = input2[j];
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2i, (uint32_t )5);
    if (ctr > (uint32_t )1)
      Hacl_Bignum_Fmul_shift_reduce(input);
    Hacl_Bignum_Fmul_mul_shift_reduce_(output, (void *)(uint8_t )0, input, input2, i);
    return;
  }
}

inline static void Hacl_Bignum_Fmul_fmul_(uint32_t *output, uint32_t *input, uint32_t *input2)
{
  uint64_t t[5] = { 0 };
  void
  *input_init =
    (void *)/* start inlining Hacl.Bignum.Fmul.get_seq */
      (void *)(uint8_t )0
    /* end inlining Hacl.Bignum.Fmul.get_seq */;
  Hacl_Bignum_Fmul_mul_shift_reduce_(t, (void *)(uint8_t )0, input, input2, (uint32_t )5);
  Hacl_Bignum_Fproduct_carry_wide_(t, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top_wide(t);
  Hacl_Bignum_Fproduct_copy_from_wide_(output, t, (uint32_t )5);
  Hacl_Bignum_Fproduct_carry_0_to_1(output);
}

inline static void Hacl_Bignum_Fmul_fmul(uint32_t *output, uint32_t *input, uint32_t *input2)
{
  uint32_t tmp[5] = { 0 };
  memcpy(tmp, input, (uint32_t )5 * sizeof input[0]);
  Hacl_Bignum_Fmul_fmul_(output, tmp, input2);
}

static void
Hacl_Bignum_AddAndMultiply_add_and_multiply(uint32_t *acc, uint32_t *block, uint32_t *r)
{
  Hacl_Bignum_Fsum_fsum_(acc, block, (uint32_t )5);
  Hacl_Bignum_Fmul_fmul(acc, acc, r);
  return;
}

static uint32_t
*Hacl_MAC_Poly1305_32___proj__MkState__item__r(Hacl_MAC_Poly1305_32_poly1305_state projectee)
{
  Hacl_MAC_Poly1305_32_poly1305_state scrut = projectee;
  uint32_t *r = scrut.x00;
  uint32_t *h = scrut.x01;
  return r;
}

static uint32_t
*Hacl_MAC_Poly1305_32___proj__MkState__item__h(Hacl_MAC_Poly1305_32_poly1305_state projectee)
{
  Hacl_MAC_Poly1305_32_poly1305_state scrut = projectee;
  uint32_t *r = scrut.x00;
  uint32_t *h = scrut.x01;
  return h;
}

static uint32_t Hacl_MAC_Poly1305_32_load32_le(uint8_t *b)
{
  uint8_t b0 = b[0];
  uint8_t b1 = b[1];
  uint8_t b2 = b[2];
  uint8_t b3 = b[3];
  return
    (uint32_t )b0
    | (uint32_t )b1 << (uint32_t )8
    | (uint32_t )b2 << (uint32_t )16
    | (uint32_t )b3 << (uint32_t )24;
}

static void Hacl_MAC_Poly1305_32_store32_le(uint8_t *b, uint32_t z)
{
  uint8_t b0 = (uint8_t )z;
  uint8_t b1 = (uint8_t )(z >> (uint32_t )8);
  uint8_t b2 = (uint8_t )(z >> (uint32_t )16);
  uint8_t b3 = (uint8_t )(z >> (uint32_t )24);
  b[0] = b0;
  b[1] = b1;
  b[2] = b2;
  b[3] = b3;
}

static void
Hacl_MAC_Poly1305_32_upd_5(
  uint32_t *b,
  uint32_t b0,
  uint32_t b1,
  uint32_t b2,
  uint32_t b3,
  uint32_t b4
)
{
  b[0] = b0;
  b[1] = b1;
  b[2] = b2;
  b[3] = b3;
  b[4] = b4;
}

static void Hacl_MAC_Poly1305_32_poly1305_encode_r(uint32_t *r, uint8_t *key)
{
  uint32_t t00 = Hacl_MAC_Poly1305_32_load32_le(key);
  uint32_t t10 = Hacl_MAC_Poly1305_32_load32_le(key + (uint32_t )4);
  uint32_t t20 = Hacl_MAC_Poly1305_32_load32_le(key + (uint32_t )8);
  uint32_t t30 = Hacl_MAC_Poly1305_32_load32_le(key + (uint32_t )12);
  uint32_t t0 = t00 & (uint32_t )0x0fffffff;
  uint32_t t1 = t10 & (uint32_t )0x0ffffffc;
  uint32_t t2 = t20 & (uint32_t )0x0ffffffc;
  uint32_t t3 = t30 & (uint32_t )0x0ffffffc;
  uint32_t r0 = t0 & (uint32_t )0x3ffffff;
  uint32_t r1 = (t0 >> (uint32_t )26 | t1 << (uint32_t )6) & (uint32_t )0x3ffffff;
  uint32_t r2 = (t1 >> (uint32_t )20 | t2 << (uint32_t )12) & (uint32_t )0x3ffffff;
  uint32_t r3 = (t2 >> (uint32_t )14 | t3 << (uint32_t )18) & (uint32_t )0x3ffffff;
  uint32_t r4 = t3 >> (uint32_t )8 & (uint32_t )0x3ffffff;
  Hacl_MAC_Poly1305_32_upd_5(r, r0, r1, r2, r3, r4);
  return;
}

static void Hacl_MAC_Poly1305_32_toField(uint32_t *b, uint8_t *m)
{
  uint32_t t0 = Hacl_MAC_Poly1305_32_load32_le(m);
  uint32_t t1 = Hacl_MAC_Poly1305_32_load32_le(m + (uint32_t )4);
  uint32_t t2 = Hacl_MAC_Poly1305_32_load32_le(m + (uint32_t )8);
  uint32_t t3 = Hacl_MAC_Poly1305_32_load32_le(m + (uint32_t )12);
  uint32_t r0 = t0 & (uint32_t )0x3ffffff;
  uint32_t r1 = (t0 >> (uint32_t )26 | t1 << (uint32_t )6) & (uint32_t )0x3ffffff;
  uint32_t r2 = (t1 >> (uint32_t )20 | t2 << (uint32_t )12) & (uint32_t )0x3ffffff;
  uint32_t r3 = (t2 >> (uint32_t )14 | t3 << (uint32_t )18) & (uint32_t )0x3ffffff;
  uint32_t r4 = t3 >> (uint32_t )8 & (uint32_t )0x3ffffff;
  Hacl_MAC_Poly1305_32_upd_5(b, r0, r1, r2, r3, r4);
  return;
}

static void Hacl_MAC_Poly1305_32_toField_plus_2_128(uint32_t *b, uint8_t *m)
{
  Hacl_MAC_Poly1305_32_toField(b, m);
  uint32_t b4 = b[4];
  uint32_t b4_ = (uint32_t )0x1000000 | b4;
  b[4] = b4_;
}

static void Hacl_MAC_Poly1305_32_poly1305_start(uint32_t *a)
{
  Hacl_MAC_Poly1305_32_upd_5(a,
    (uint32_t )0,
    (uint32_t )0,
    (uint32_t )0,
    (uint32_t )0,
    (uint32_t )0);
  return;
}

static void
Hacl_MAC_Poly1305_32_poly1305_init_(Hacl_MAC_Poly1305_32_poly1305_state st, uint8_t *key)
{
  Hacl_MAC_Poly1305_32_poly1305_encode_r(Hacl_MAC_Poly1305_32___proj__MkState__item__r(st), key);
  Hacl_MAC_Poly1305_32_poly1305_start(Hacl_MAC_Poly1305_32___proj__MkState__item__h(st));
  return;
}

static void
Hacl_MAC_Poly1305_32_poly1305_update(
  void *log,
  Hacl_MAC_Poly1305_32_poly1305_state st,
  uint8_t *m
)
{
  uint32_t tmp[5] = { 0 };
  uint32_t *acc = Hacl_MAC_Poly1305_32___proj__MkState__item__h(st);
  uint32_t *r = Hacl_MAC_Poly1305_32___proj__MkState__item__r(st);
  Hacl_MAC_Poly1305_32_toField_plus_2_128(tmp, m);
  Hacl_Bignum_AddAndMultiply_add_and_multiply(acc, tmp, r);
}

static void
Hacl_MAC_Poly1305_32_poly1305_blocks(
  void *log,
  Hacl_MAC_Poly1305_32_poly1305_state st,
  uint8_t *m,
  uint64_t len
)
{
  if (len < (uint64_t )16)
    return;
  else
  {
    void *new_log = (Hacl_MAC_Poly1305_32_poly1305_update((void *)(uint8_t )0, st, m) , (void *)0);
    uint64_t len0 = len - (uint64_t )16;
    uint8_t *m0 = m + (uint32_t )16;
    Hacl_MAC_Poly1305_32_poly1305_blocks((void *)(uint8_t )0, st, m0, len0);
    return;
  }
}

static void Hacl_MAC_Poly1305_32_poly1305_concat(uint8_t *b, uint8_t *m, uint64_t len)
{
  uint32_t i = (uint32_t )len;
  memcpy(b, m, i * sizeof m[0]);
}

static void
Hacl_MAC_Poly1305_32_poly1305_process_last_block_(
  uint8_t *block,
  Hacl_MAC_Poly1305_32_poly1305_state st,
  uint8_t *m,
  uint64_t rem_
)
{
  uint32_t tmp[5] = { 0 };
  Hacl_MAC_Poly1305_32_toField(tmp, block);
  Hacl_Bignum_AddAndMultiply_add_and_multiply(Hacl_MAC_Poly1305_32___proj__MkState__item__h(st),
    tmp,
    Hacl_MAC_Poly1305_32___proj__MkState__item__r(st));
}

static void
Hacl_MAC_Poly1305_32_poly1305_process_last_block(
  Hacl_MAC_Poly1305_32_poly1305_state st,
  uint8_t *m,
  uint64_t rem_
)
{
  uint8_t zero = (uint8_t )0;
  uint8_t block[16];
  for (uintmax_t i = 0; i < (uint32_t )16; ++i)
    block[i] = zero;
  uint32_t i = (uint32_t )rem_;
  Hacl_MAC_Poly1305_32_poly1305_concat(block, m, rem_);
  block[i] = (uint8_t )1;
  Hacl_MAC_Poly1305_32_poly1305_process_last_block_(block, st, m, rem_);
}

static void Hacl_MAC_Poly1305_32_poly1305_last_pass(uint32_t *acc)
{
  Hacl_Bignum_Fproduct_carry_limb_(acc, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top(acc);
  Hacl_Bignum_Fproduct_carry_limb_(acc, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top(acc);
  Hacl_Bignum_Fproduct_carry_0_to_1(acc);
  uint32_t p26m1 = (uint32_t )0x3ffffff;
  uint32_t p26m5 = (uint32_t )0x3fffffb;
  uint32_t a0 = acc[0];
  uint32_t a1 = acc[1];
  uint32_t a2 = acc[2];
  uint32_t a3 = acc[3];
  uint32_t a4 = acc[4];
  uint32_t mask0 = FStar_UInt32_gte_mask(a0, p26m5);
  uint32_t mask1 = FStar_UInt32_eq_mask(a1, p26m1);
  uint32_t mask2 = FStar_UInt32_eq_mask(a2, p26m1);
  uint32_t mask3 = FStar_UInt32_eq_mask(a3, p26m1);
  uint32_t mask4 = FStar_UInt32_eq_mask(a4, p26m1);
  uint32_t mask = mask0 & mask1 & mask2 & mask3 & mask4;
  uint32_t a0_ = a0 - (p26m5 & mask);
  uint32_t a1_ = a1 - (p26m1 & mask);
  uint32_t a2_ = a2 - (p26m1 & mask);
  uint32_t a3_ = a3 - (p26m1 & mask);
  uint32_t a4_ = a4 - (p26m1 & mask);
  Hacl_MAC_Poly1305_32_upd_5(acc, a0_, a1_, a2_, a3_, a4_);
  return;
}

static void
Hacl_MAC_Poly1305_32_poly1305_finish__(
  void *log,
  Hacl_MAC_Poly1305_32_poly1305_state st,
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
    Hacl_MAC_Poly1305_32_poly1305_process_last_block(st, m + start, rem_);
    return;
  }
}

static void
Hacl_MAC_Poly1305_32_poly1305_finish_(
  void *log,
  Hacl_MAC_Poly1305_32_poly1305_state st,
  uint8_t *mac,
  uint8_t *m,
  uint64_t len,
  uint8_t *key_s
)
{
  uint32_t tmp[5] = { 0 };
  Hacl_MAC_Poly1305_32_toField(tmp, key_s);
  Hacl_MAC_Poly1305_32_poly1305_finish__((void *)(uint8_t )0, st, mac, m, len, key_s);
  Hacl_MAC_Poly1305_32_poly1305_last_pass(Hacl_MAC_Poly1305_32___proj__MkState__item__h(st));
  Hacl_Bignum_Fsum_fsum_(Hacl_MAC_Poly1305_32___proj__MkState__item__h(st), tmp, (uint32_t )5);
  Hacl_Bignum_Fproduct_carry_limb_(Hacl_MAC_Poly1305_32___proj__MkState__item__h(st),
    (uint32_t )0);
  uint32_t k0 = Hacl_MAC_Poly1305_32_load32_le(key_s);
  uint32_t k1 = Hacl_MAC_Poly1305_32_load32_le(key_s + (uint32_t )4);
  uint32_t k2 = Hacl_MAC_Poly1305_32_load32_le(key_s + (uint32_t )8);
  uint32_t k3 = Hacl_MAC_Poly1305_32_load32_le(key_s + (uint32_t )12);
  uint32_t h0 = Hacl_MAC_Poly1305_32___proj__MkState__item__h(st)[0];
  uint32_t h1 = Hacl_MAC_Poly1305_32___proj__MkState__item__h(st)[1];
  uint32_t h2 = Hacl_MAC_Poly1305_32___proj__MkState__item__h(st)[2];
  uint32_t h3 = Hacl_MAC_Poly1305_32___proj__MkState__item__h(st)[3];
  uint32_t h4 = Hacl_MAC_Poly1305_32___proj__MkState__item__h(st)[4];
  uint32_t acc0 = h0 | h1 << (uint32_t )26;
  uint32_t acc1 = h1 >> (uint32_t )6 | h2 << (uint32_t )20;
  uint32_t acc2 = h2 >> (uint32_t )12 | h3 << (uint32_t )14;
  uint32_t acc3 = h3 >> (uint32_t )18 | h4 << (uint32_t )8;
  Hacl_MAC_Poly1305_32_store32_le(mac, acc0);
  Hacl_MAC_Poly1305_32_store32_le(mac + (uint32_t )4, acc1);
  Hacl_MAC_Poly1305_32_store32_le(mac + (uint32_t )8, acc2);
  Hacl_MAC_Poly1305_32_store32_le(mac + (uint32_t )12, acc3);
}

static void
Hacl_MAC_Poly1305_32_crypto_onetimeauth(
  uint8_t *output,
  uint8_t *input,
  uint64_t len,
  uint8_t *k
)
{
  uint32_t buf[10] = { 0 };
  uint32_t *r = buf;
  uint32_t *h = buf + (uint32_t )5;
  Hacl_MAC_Poly1305_32_poly1305_state st = { .x00 = r, .x01 = h };
  uint8_t *key_r = k;
  uint8_t *key_s = k + (uint32_t )16;
  void *init_log = (Hacl_MAC_Poly1305_32_poly1305_init_(st, k) , (void *)0);
  void
  *partial_log =
    (Hacl_MAC_Poly1305_32_poly1305_blocks((void *)(uint8_t )0, st, input, len) , (void *)0);
  void
  *final_log =
    (Hacl_MAC_Poly1305_32_poly1305_finish_((void *)(uint8_t )0,
      st,
      output,
      input,
      len,
      key_s)
    , (void *)0);
}

void Poly1305_32_crypto_onetimeauth(uint8_t *output, uint8_t *input, uint64_t len, uint8_t *k)
{
  Hacl_MAC_Poly1305_32_crypto_onetimeauth(output, input, len, k);
  return;
}

