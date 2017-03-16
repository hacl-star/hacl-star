#include "Poly1305_vec.h"
#include "immintrin.h"

#undef inline
#define inline 
inline static void Hacl_Bignum_Fsum_fsum_(vec *a, vec *b, uint32_t i)
{
  if (i == (uint32_t )0)
    return;
  else
  {
    uint32_t i0 = i - (uint32_t )1;
    vec ai = a[i0];
    vec bi = b[i0];
    a[i0] = ai + bi;
    Hacl_Bignum_Fsum_fsum_(a, b, i0);
    return;
  }
}

static void Hacl_Bignum_Modulo_reduce(vec *b)
{
  vec b0 = b[0];
  b[0] = (b0 << (uint32_t )2) + b0;
}

static void Hacl_Bignum_Modulo_carry_top(vec *b)
{
  vec b4 = b[4];
  vec b0 = b[0];
  vec b4_26 = b4 >> (uint32_t )26;
  b[4] = b4 & (uint64_t )0x3ffffff;
  b[0] = (b4_26 << (uint32_t )2) + b4_26 + b0;
}

static void Hacl_Bignum_Modulo_carry_top_wide(vec *b)
{
  vec b4 = b[4];
  vec b0 = b[0];
  vec b4_ = b4 & (uint64_t )(uint64_t )0x3ffffff;
  vec b4_26 = (vec )(b4 >> (uint32_t )26);
  vec b0_ = b0 + (vec )((b4_26 << (uint32_t )2) + b4_26);
  b[4] = b4_;
  b[0] = b0_;
}

inline static void
Hacl_Bignum_Fproduct_copy_from_wide_(vec *output, vec *input, uint32_t ctr)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    vec inputi = input[i];
    output[i] = inputi ;
    Hacl_Bignum_Fproduct_copy_from_wide_(output, input, i);
    return;
  }
}

inline static void Hacl_Bignum_Fproduct_shift_(vec *output, uint32_t ctr)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    vec z = output[ctr - (uint32_t )1];
    output[ctr] = z;
    Hacl_Bignum_Fproduct_shift_(output, ctr - (uint32_t )1);
    return;
  }
}

inline static void Hacl_Bignum_Fproduct_shift(vec *output)
{
  vec tmp = output[4];
  Hacl_Bignum_Fproduct_shift_(output, (uint32_t )4);
  output[0] = tmp;
}

inline static void
Hacl_Bignum_Fproduct_sum_scalar_multiplication_(
  vec *output,
  vec *input,
  vec s,
  uint32_t ctr
)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    vec oi = output[i];
    vec ii = input[i];
    output[i] = oi + (vec )ii * (vec )s;
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, s, i);
    return;
  }
}

inline static void Hacl_Bignum_Fproduct_carry_wide_(vec *tmp, uint32_t ctr)
{
  if (ctr == (uint32_t )4)
    return;
  else
  {
    vec tctr = tmp[ctr];
    vec tctrp1 = tmp[ctr + (uint32_t )1];
    vec r0 = (vec )tctr & ((uint64_t )1 << (uint32_t )26) - (uint64_t )1;
    vec c = tctr >> (uint32_t )26;
    tmp[ctr] = (vec )r0;
    tmp[ctr + (uint32_t )1] = tctrp1 + c;
    Hacl_Bignum_Fproduct_carry_wide_(tmp, ctr + (uint32_t )1);
    return;
  }
}

inline static void Hacl_Bignum_Fproduct_carry_limb_(vec *tmp, uint32_t ctr)
{
  if (ctr == (uint32_t )4)
    return;
  else
  {
    vec tctr = tmp[ctr];
    vec tctrp1 = tmp[ctr + (uint32_t )1];
    vec r0 = tctr & ((uint64_t )1 << (uint32_t )26) - (uint64_t )1;
    vec c = tctr >> (uint32_t )26;
    tmp[ctr] = r0;
    tmp[ctr + (uint32_t )1] = tctrp1 + c;
    Hacl_Bignum_Fproduct_carry_limb_(tmp, ctr + (uint32_t )1);
    return;
  }
}

inline static void Hacl_Bignum_Fproduct_carry_0_to_1(vec *output)
{
  vec i0 = output[0];
  vec i1 = output[1];
  vec i0_ = i0 & ((uint64_t )1 << (uint32_t )26) - (uint64_t )1;
  vec i1_ = i1 + (i0 >> (uint32_t )26);
  output[0] = i0_;
  output[1] = i1_;
}

inline static void Hacl_Bignum_Fmul_shift_reduce(vec *output)
{
  Hacl_Bignum_Fproduct_shift(output);
  Hacl_Bignum_Modulo_reduce(output);
  return;
}

inline static void
Hacl_Bignum_Fmul_mul_shift_reduce_(
  vec *output,
  void *init_input,
  vec *input,
  vec *input2,
  uint32_t ctr
)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    uint32_t j = (uint32_t )4 - i;
    vec input2i = input2[j];
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2i, (uint64_t )5);
    if (ctr > (uint32_t )1)
      Hacl_Bignum_Fmul_shift_reduce(input);
    Hacl_Bignum_Fmul_mul_shift_reduce_(output, (void *)(uint8_t )0, input, input2, i);
    return;
  }
}

inline static void Hacl_Bignum_Fmul_fmul_(vec *output, vec *input, vec *input2)
{
  vec t[5] = { 0 };
  void
  *input_init =
    (void *)/* start inlining Hacl.Bignum.Fmul.get_seq */
      (void *)(uint8_t )0
    /* end inlining Hacl.Bignum.Fmul.get_seq */;
  Hacl_Bignum_Fmul_mul_shift_reduce_(t, (void *)(uint8_t )0, input, input2, (uint64_t )5);
  Hacl_Bignum_Fproduct_carry_wide_(t, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top_wide(t);
  Hacl_Bignum_Fproduct_copy_from_wide_(output, t, (uint32_t )5);
  Hacl_Bignum_Fproduct_carry_0_to_1(output);
}

inline static void Hacl_Bignum_Fmul_fmul(vec *output, vec *input, vec *input2)
{
  vec tmp[5] = { 0 };
  memcpy(tmp, input, (uint32_t )5 * sizeof input[0]);
  Hacl_Bignum_Fmul_fmul_(output, tmp, input2);
}

static void
Hacl_Bignum_AddAndMultiply_add_and_multiply(vec *acc, vec *block, vec *r)
{
  Hacl_Bignum_Fsum_fsum_(acc, block, (uint32_t )5);
  Hacl_Bignum_Fmul_fmul(acc, acc, r);
  return;
}

static vec
*Hacl_MAC_Poly1305_32___proj__MkState__item__r(Hacl_MAC_Poly1305_32_poly1305_state projectee)
{
  Hacl_MAC_Poly1305_32_poly1305_state scrut = projectee;
  vec *r = scrut.x00;
  vec *h = scrut.x01;
  return r;
}

static vec
*Hacl_MAC_Poly1305_32___proj__MkState__item__h(Hacl_MAC_Poly1305_32_poly1305_state projectee)
{
  Hacl_MAC_Poly1305_32_poly1305_state scrut = projectee;
  vec *r = scrut.x00;
  vec *h = scrut.x01;
  return h;
}

static void
Hacl_MAC_Poly1305_32_upd_5(
  vec *b,
  vec b0,
  vec b1,
  vec b2,
  vec b3,
  vec b4
)
{
  b[0] = b0;
  b[1] = b1;
  b[2] = b2;
  b[3] = b3;
  b[4] = b4;
}

static void Hacl_MAC_Poly1305_32_poly1305_encode_r(vec *r, vec* rp4, uint8_t *key)
{
  uint64_t t00 = load32_le(key);
  uint64_t t10 = load32_le(key + (uint32_t )4);
  uint64_t t20 = load32_le(key + (uint32_t )8);
  uint64_t t30 = load32_le(key + (uint32_t )12);
  vec v0 = (vec){t00,t00,t00,t00};
  vec v1 = (vec){t10,t10,t10,t10};
  vec v2 = (vec){t20,t20,t20,t20};
  vec v3 = (vec){t30,t30,t30,t30};
  vec t0 = v0 & (uint64_t )0x0fffffff;
  vec t1 = v1 & (uint64_t )0x0ffffffc;
  vec t2 = v2 & (uint64_t )0x0ffffffc;
  vec t3 = v3 & (uint64_t )0x0ffffffc;
  vec r0 = t0 & (uint64_t )0x3ffffff;
  vec r1 = (t0 >> (uint32_t )26 | t1 << (uint32_t )6) & (uint64_t )0x3ffffff;
  vec r2 = (t1 >> (uint32_t )20 | t2 << (uint32_t )12) & (uint64_t )0x3ffffff;
  vec r3 = (t2 >> (uint32_t )14 | t3 << (uint32_t )18) & (uint64_t )0x3ffffff;
  vec r4 = t3 >> (uint32_t )8 & (uint64_t )0x3ffffff;
  Hacl_MAC_Poly1305_32_upd_5(r, r0, r1, r2, r3, r4);
  vec rp2[5];
  Hacl_Bignum_Fmul_fmul(rp2, r, r);
  Hacl_Bignum_Fmul_fmul(rp4, rp2, rp2);
  return;
}

inline static void Hacl_MAC_Poly1305_32_toField(vec *b, uint8_t *m, uint32_t k)
{
  uint64_t t00, t01, t02, t03,
    t10, t11, t12, t13,
    t20, t21, t22, t23,
    t30, t31, t32, t33;
  t00 = load32_le(m);
  t01 = load32_le(m + (uint32_t )4);
  t02 = load32_le(m + (uint32_t )8);
  t03 = load32_le(m + (uint32_t )12);
  if (k > 1) {
    t10 = load32_le(m+16);
    t11 = load32_le(m + (uint32_t )20);
    t12 = load32_le(m + (uint32_t )24);
    t13 = load32_le(m + (uint32_t )28);
  } else {
    t10 = t11 = t12 = t13 = 0;
  }
  if (k > 2) {
    t20 = load32_le(m+32);
    t21 = load32_le(m + (uint32_t )36);
    t22 = load32_le(m + (uint32_t )40);
    t23 = load32_le(m + (uint32_t )44);
  } else {
    t20 = t21 = t22 = t23 = 0;
  }
  if (k > 3) {
    t30 = load32_le(m+48);
    t31 = load32_le(m + (uint32_t )52);
    t32 = load32_le(m + (uint32_t )56);
    t33 = load32_le(m + (uint32_t )60);
  } else {
    t30 = t31 = t32 = t33 = 0;
  }
  vec v0 = (vec){t00,t10,t20,t30};
  vec v1 = (vec){t01,t11,t21,t31};
  vec v2 = (vec){t02,t12,t22,t32};
  vec v3 = (vec){t03,t13,t23,t33};
  vec r0 = v0 & (uint64_t )0x3ffffff;
  vec r1 = (v0 >> (uint32_t )26 | v1 << (uint32_t )6) & (uint64_t )0x3ffffff;
  vec r2 = (v1 >> (uint32_t )20 | v2 << (uint32_t )12) & (uint64_t )0x3ffffff;
  vec r3 = (v2 >> (uint32_t )14 | v3 << (uint32_t )18) & (uint64_t )0x3ffffff;
  vec r4 = v3 >> (uint32_t )8 & (uint64_t )0x3ffffff;
  Hacl_MAC_Poly1305_32_upd_5(b, r0, r1, r2, r3, r4);
  return;
}

inline static void Hacl_MAC_Poly1305_32_toField4(vec *b, uint8_t *m)
{
  uint64_t t00, t01, t02, t03,
    t10, t11, t12, t13,
    t20, t21, t22, t23,
    t30, t31, t32, t33;

  t00 = load32_le(m);
  t01 = load32_le(m + (uint32_t )4);
  t02 = load32_le(m + (uint32_t )8);
  t03 = load32_le(m + (uint32_t )12);
  t10 = load32_le(m+16);
  t11 = load32_le(m + (uint32_t )20);
  t12 = load32_le(m + (uint32_t )24);
  t13 = load32_le(m + (uint32_t )28);
  t20 = load32_le(m+32);
  t21 = load32_le(m + (uint32_t )36);
  t22 = load32_le(m + (uint32_t )40);
  t23 = load32_le(m + (uint32_t )44);
  t30 = load32_le(m+48);
  t31 = load32_le(m + (uint32_t )52);
  t32 = load32_le(m + (uint32_t )56);
  t33 = load32_le(m + (uint32_t )60);
  vec v0 = (vec){t00,t10,t20,t30};
  vec v1 = (vec){t01,t11,t21,t31};
  vec v2 = (vec){t02,t12,t22,t32};
  vec v3 = (vec){t03,t13,t23,t33};
  vec r0 = v0 & (uint64_t )0x3ffffff;
  vec r1 = (v0 >> (uint32_t )26 | v1 << (uint32_t )6) & (uint64_t )0x3ffffff;
  vec r2 = (v1 >> (uint32_t )20 | v2 << (uint32_t )12) & (uint64_t )0x3ffffff;
  vec r3 = (v2 >> (uint32_t )14 | v3 << (uint32_t )18) & (uint64_t )0x3ffffff;
  vec r4 = v3 >> (uint32_t )8 & (uint64_t )0x3ffffff;
  Hacl_MAC_Poly1305_32_upd_5(b, r0, r1, r2, r3, r4);
  Hacl_MAC_Poly1305_32_upd_5(b, v0, v1, v2, v3, v0);
  return;
}


inline static void Hacl_MAC_Poly1305_32_toField_plus_2_128(vec *b, uint8_t *m, uint32_t l)
{
  Hacl_MAC_Poly1305_32_toField(b, m, l);
  vec b4 = b[4];
  vec b4_ = (uint64_t )0x1000000 | b4;
  b[4] = b4_;
}

inline static void Hacl_MAC_Poly1305_32_toField_plus_2_128_4(vec *b, uint8_t *m)
{
  Hacl_MAC_Poly1305_32_toField4(b, m);
  vec b4 = b[4];
  vec b4_ = (uint64_t )0x1000000 | b4;
  b[4] = b4_;
}

static void Hacl_MAC_Poly1305_32_poly1305_start(vec *a)
{
  vec zero = (vec){0,0,0,0};
  Hacl_MAC_Poly1305_32_upd_5(a,zero,zero,zero,zero,zero);
  return;
}

static void
Hacl_MAC_Poly1305_32_poly1305_init_(Hacl_MAC_Poly1305_32_poly1305_state st, uint8_t *key)
{
  Hacl_MAC_Poly1305_32_poly1305_encode_r(Hacl_MAC_Poly1305_32___proj__MkState__item__r(st), st.x02, key);
  Hacl_MAC_Poly1305_32_poly1305_start(Hacl_MAC_Poly1305_32___proj__MkState__item__h(st));
  return;
}


inline static void
Hacl_MAC_Poly1305_32_poly1305_update(
  void *log,
  Hacl_MAC_Poly1305_32_poly1305_state st,
  uint8_t *m,
  uint32_t b
)
{
  vec tmp[5] = { 0 };
  vec *acc = Hacl_MAC_Poly1305_32___proj__MkState__item__h(st);
  vec *r = Hacl_MAC_Poly1305_32___proj__MkState__item__r(st);
  vec *rp4 = st.x02;
  Hacl_MAC_Poly1305_32_toField_plus_2_128(tmp, m, b);
  Hacl_Bignum_AddAndMultiply_add_and_multiply(acc, tmp, rp4);
}


inline static void
Hacl_MAC_Poly1305_32_poly1305_update4(
  void *log,
  Hacl_MAC_Poly1305_32_poly1305_state st,
  uint8_t *m
)
{
  vec tmp[5] = { 0 };
  vec *acc = Hacl_MAC_Poly1305_32___proj__MkState__item__h(st);
  vec *r = Hacl_MAC_Poly1305_32___proj__MkState__item__r(st);
  vec *rp4 = st.x02;
  Hacl_MAC_Poly1305_32_toField_plus_2_128_4(tmp, m);
  Hacl_Bignum_AddAndMultiply_add_and_multiply(acc, tmp, rp4);
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
    if (len < (uint64_t )64) {
      uint64_t l = len / 16 ;
      void *new_log = (Hacl_MAC_Poly1305_32_poly1305_update((void *)(uint8_t )0, st, m, l) , (void *)0);
      return;}
  else
  {
    void *new_log = (Hacl_MAC_Poly1305_32_poly1305_update4((void *)(uint8_t )0, st, m) , (void *)0);
    uint64_t len0 = len - (uint64_t )64;
    uint8_t *m0 = m + (uint32_t )64;
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
  vec* r = Hacl_MAC_Poly1305_32___proj__MkState__item__r(st);
  vec* acc = Hacl_MAC_Poly1305_32___proj__MkState__item__h(st);
  vec rp2[5];
  Hacl_Bignum_Fmul_fmul(rp2, r, r);
  vec rp3[5];
  Hacl_Bignum_Fmul_fmul(rp3, rp2, r);
  vec* rp4 = st.x02;
  vec accr4[5];
  vec accr3[5];
  vec accr2[5];
  vec accr1[5];
  Hacl_Bignum_Fmul_fmul(accr4, acc, rp4);
  Hacl_Bignum_Fmul_fmul(accr2, acc, rp3);
  Hacl_Bignum_Fmul_fmul(accr3, acc, rp2);
  Hacl_Bignum_Fmul_fmul(accr1, acc, r);
  acc[0][0] += acc[0][1] + acc[0][2] + acc[0][3];
  acc[1][0] += acc[1][1] + acc[1][2] + acc[1][3];
  acc[2][0] += acc[2][1] + acc[2][2] + acc[2][3];
  acc[3][0] += acc[3][1] + acc[3][2] + acc[3][3];
  acc[0] &= (vec){0xffffffffffffffff,0,0,0};
  acc[1] &= (vec){0xffffffffffffffff,0,0,0};
  acc[2] &= (vec){0xffffffffffffffff,0,0,0};
  acc[3] &= (vec){0xffffffffffffffff,0,0,0};
  vec tmp[5] = { 0 };
  Hacl_MAC_Poly1305_32_toField(tmp, block,1);
  Hacl_Bignum_AddAndMultiply_add_and_multiply(acc,tmp, r);
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
  uint64_t i = (uint64_t )rem_;
  Hacl_MAC_Poly1305_32_poly1305_concat(block, m, rem_);
  block[i] = (uint8_t )1;
  Hacl_MAC_Poly1305_32_poly1305_process_last_block_(block, st, m, rem_);
}

static void Hacl_MAC_Poly1305_32_poly1305_last_pass(vec *acc)
{
  Hacl_Bignum_Fproduct_carry_limb_(acc, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top(acc);
  Hacl_Bignum_Fproduct_carry_limb_(acc, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top(acc);
  Hacl_Bignum_Fproduct_carry_0_to_1(acc);
  uint64_t p26m1 = (uint64_t )0x3ffffff;
  uint64_t p26m5 = (uint64_t )0x3fffffb;
  vec a0 = acc[0];
  vec a1 = acc[1];
  vec a2 = acc[2];
  vec a3 = acc[3];
  vec a4 = acc[4];
  vec mask0 = vec_gte_mask(a0, p26m5);
  vec mask1 = vec_eq_mask(a1, p26m1);
  vec mask2 = vec_eq_mask(a2, p26m1);
  vec mask3 = vec_eq_mask(a3, p26m1);
  vec mask4 = vec_eq_mask(a4, p26m1);
  vec mask = mask0 & mask1 & mask2 & mask3 & mask4;
  vec a0_ = a0 - (p26m5 & mask);
  vec a1_ = a1 - (p26m1 & mask);
  vec a2_ = a2 - (p26m1 & mask);
  vec a3_ = a3 - (p26m1 & mask);
  vec a4_ = a4 - (p26m1 & mask);
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
    uint64_t start = (uint64_t )(len - rem_);
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
  vec tmp[5] = { 0 };
  Hacl_MAC_Poly1305_32_toField(tmp, key_s, 1);
  Hacl_MAC_Poly1305_32_poly1305_finish__((void *)(uint8_t )0, st, mac, m, len, key_s);
  Hacl_MAC_Poly1305_32_poly1305_last_pass(Hacl_MAC_Poly1305_32___proj__MkState__item__h(st));
  Hacl_Bignum_Fsum_fsum_(Hacl_MAC_Poly1305_32___proj__MkState__item__h(st), tmp, (uint32_t )5);
  Hacl_Bignum_Fproduct_carry_limb_(Hacl_MAC_Poly1305_32___proj__MkState__item__h(st),
    (uint32_t )0);
  vec h0 = Hacl_MAC_Poly1305_32___proj__MkState__item__h(st)[0];
  vec h1 = Hacl_MAC_Poly1305_32___proj__MkState__item__h(st)[1];
  vec h2 = Hacl_MAC_Poly1305_32___proj__MkState__item__h(st)[2];
  vec h3 = Hacl_MAC_Poly1305_32___proj__MkState__item__h(st)[3];
  vec h4 = Hacl_MAC_Poly1305_32___proj__MkState__item__h(st)[4];
  vec acc0 = h0 | h1 << (uint32_t )26;
  vec acc1 = h1 >> (uint32_t )6 | h2 << (uint32_t )20;
  vec acc2 = h2 >> (uint32_t )12 | h3 << (uint32_t )14;
  vec acc3 = h3 >> (uint32_t )18 | h4 << (uint32_t )8;
  store32_le(mac, acc0[0]);
  store32_le(mac + (uint32_t )4, acc1[0]);
  store32_le(mac + (uint32_t )8, acc2[0]);
  store32_le(mac + (uint32_t )12, acc3[0]);
}

static void
Hacl_MAC_Poly1305_32_crypto_onetimeauth(
  uint8_t *output,
  uint8_t *input,
  uint64_t len,
  uint8_t *k
)
{
  vec buf[15] = { 0 };
  vec *r = buf;
  vec *h = buf + (uint32_t )5;
  vec *rp4 = buf + (uint32_t )10;
  Hacl_MAC_Poly1305_32_poly1305_state st = { .x00 = r, .x01 = h, .x02 = rp4 };
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

