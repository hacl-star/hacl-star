#include "Poly1305_64.h"
//#define inline __attribute((noinline))
//#define static



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
  b[0] = (b2_42 * 5) + b0;

    //(b2_42 << (uint32_t )2) + b2_42 + b0;
}

inline static void Hacl_Bignum_Modulo_carry_top_wide(uint128_t *b)
{
  uint128_t b2h;
  uint128_split(b2h,b[2],b[2],42);
  uint64_t b2_42 = FStar_Int_Cast_uint128_to_uint64(b2h);
  uint128_add64(b[0], b[0], b2_42 * 5);

		//(b2_42 << (uint32_t )2) + b2_42);
}

inline static void
Hacl_Bignum_Fproduct_copy_from_wide_(uint64_t *output, uint128_t *input, uint32_t ctr)
{
    output[0] = FStar_Int_Cast_uint128_to_uint64(input[0]);
    output[1] = FStar_Int_Cast_uint128_to_uint64(input[1]);
    output[2] = FStar_Int_Cast_uint128_to_uint64(input[2]);
}

inline static void Hacl_Bignum_Fproduct_shift_(uint64_t *output, uint32_t ctr)
{
    output[2] = output[1];
    output[1] = output[0];
}

inline static void Hacl_Bignum_Fproduct_shift(uint64_t *output)
{
  uint64_t tmp = output[2];
  Hacl_Bignum_Fproduct_shift_(output, (uint32_t )2);
  output[0] = tmp;
}

inline static void
Hacl_Bignum_Fproduct_sum_scalar_multiplication_(
  uint128_t *output,
  uint64_t *input,
  uint64_t s,
  uint32_t ctr
)
{
  uint128_t o0, o1, o2 ;
  uint128_mul_wide(o0,input[0],s);
  uint128_add(output[0], o0, output[0]);
  uint128_mul_wide(o1,input[1],s);
  uint128_add(output[1], o1, output[1]);
  uint128_mul_wide(o2,input[2],s);
  uint128_add(output[2], o2, output[2]);
}

inline static void Hacl_Bignum_Fproduct_carry_wide_(uint128_t *tmp, uint32_t ctr)
{
    uint128_t th,tp1;
    uint128_split(th,tmp[ctr],tmp[ctr],44);
    uint128_add(tp1,tmp[ctr+1], th);
    uint128_split(th,tmp[ctr+1],tp1,44);
    uint128_add(tmp[ctr+2],tmp[ctr+2], th);
}

inline static void Hacl_Bignum_Fproduct_carry_limb_(uint64_t *tmp, uint32_t ctr)
{
  {
    ctr = 0;
    uint64_t tctr = tmp[ctr];
    uint64_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint64_t r0 = tctr & ((uint64_t )1 << (uint32_t )44) - (uint64_t )1;
    uint64_t c = tctr >> (uint32_t )44;
    tmp[ctr] = r0;
    tmp[ctr + (uint32_t )1] = tctrp1 + c;
  }
  {
    ctr = 1;
    uint64_t tctr = tmp[ctr];
    uint64_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint64_t r0 = tctr & ((uint64_t )1 << (uint32_t )44) - (uint64_t )1;
    uint64_t c = tctr >> (uint32_t )44;
    tmp[ctr] = r0;
    tmp[ctr + (uint32_t )1] = tctrp1 + c;
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
  uint128_t *output,
  void *init_input,
  uint64_t *input,
  uint64_t *input2,
  uint32_t ctr
)
{
  { ctr = 3;
    uint32_t i = ctr - (uint32_t )1;
    uint32_t j = (uint32_t )2 - i;
    uint64_t input2i = input2[j];
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2i, (uint32_t )3);
    Hacl_Bignum_Fmul_shift_reduce(input);
  }
  { ctr = 2;
    uint32_t i = ctr - (uint32_t )1;
    uint32_t j = (uint32_t )2 - i;
    uint64_t input2i = input2[j];
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2i, (uint32_t )3);
    Hacl_Bignum_Fmul_shift_reduce(input);
  }
  { ctr = 1;
    uint32_t i = ctr - (uint32_t )1;
    uint32_t j = (uint32_t )2 - i;
    uint64_t input2i = input2[j];
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2i, (uint32_t )3);
  }
}

inline static void Hacl_Bignum_Fmul_fmul_(uint64_t *output, uint64_t *input, uint64_t *input2)
{
  uint64_t t[6] = {0};
  //  for (uintmax_t _i = 0; _i < (uint32_t )3; ++_i)
  //  FStar_Int_Cast_uint64_to_uint128(t[_i],(uint64_t )0);
  void *input_init = (void *)(uint8_t )0;
  Hacl_Bignum_Fmul_mul_shift_reduce_(t, (void *)(uint8_t )0, input, input2, (uint32_t )3);
  Hacl_Bignum_Fproduct_carry_wide_(t, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top_wide(t);
  Hacl_Bignum_Fproduct_copy_from_wide_(output, t, (uint32_t )3);
  Hacl_Bignum_Fproduct_carry_0_to_1(output);
}

inline static void Hacl_Bignum_Fmul_fmul(uint64_t *output, uint64_t *input, uint64_t *input2)
{
  uint64_t tmp[3];
  for (int i = 0; i < 3; i++)
    tmp[i] = input[i];
  Hacl_Bignum_Fmul_fmul_(output, tmp, input2);
}

inline static void Hacl_Bignum_Fsum_fsum_(uint64_t *a, uint64_t *b, uint32_t i)
{
  a[0] = a[0] + b[0];
  a[1] = a[1] + b[1];
  a[2] = a[2] + b[2];
}

inline static void
Hacl_Bignum_AddAndMultiply_add_and_multiply(uint64_t *acc, uint64_t *block, uint64_t *r)
{
  Hacl_Bignum_Fsum_fsum_(acc, block, (uint32_t )3);
  Hacl_Bignum_Fmul_fmul(acc, acc, r);
  return;
}

inline static uint64_t
*Hacl_Impl_Poly1305_64___proj__MkState__item__r(Hacl_Impl_Poly1305_64_poly1305_state projectee)
{
  uint64_t *r = projectee;
  return r;
}

inline static uint64_t
*Hacl_Impl_Poly1305_64___proj__MkState__item__h(Hacl_Impl_Poly1305_64_poly1305_state projectee)
{
  uint64_t *h = projectee + 3;
  return h;
}

inline static void
Hacl_Impl_Poly1305_64_poly1305_update(
  void *log,
  Hacl_Impl_Poly1305_64_poly1305_state st,
  uint8_t *m
)
{
  uint64_t *acc = Hacl_Impl_Poly1305_64___proj__MkState__item__h(st);
  uint64_t *r = Hacl_Impl_Poly1305_64___proj__MkState__item__r(st);
  //  KRML_CHECK_SIZE((uint64_t )0, (uint32_t )3);
  uint64_t tmp[3] = { 0 };
  uint128_t m0_,m0, m1_, m1, m2;
  load128_le(m0_,m);
  uint128_split(m1_,m0,m0_,44);
  uint128_split(m2,m1,m1_,44);
  tmp[0] = FStar_Int_Cast_uint128_to_uint64(m0);
  tmp[1] = FStar_Int_Cast_uint128_to_uint64(m1);
  tmp[2] = FStar_Int_Cast_uint128_to_uint64(m2);
  uint64_t b2 = tmp[2];
  uint64_t b2_ = (uint64_t )0x10000000000 | b2;
  tmp[2] = b2_;
  Hacl_Bignum_AddAndMultiply_add_and_multiply(acc, tmp, r);
  return;
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
  //  KRML_CHECK_SIZE((uint64_t )0, (uint32_t )3);
  uint64_t tmp[3] = { 0 };
  uint128_t m0_,m0, m1_, m1, m2;
  load128_le(m0_,block);
  uint128_split(m1_,m0,m0_,44);
  uint128_split(m2,m1,m1_,44);
  tmp[0] = FStar_Int_Cast_uint128_to_uint64(m0);
  tmp[1] = FStar_Int_Cast_uint128_to_uint64(m1);
  tmp[2] = FStar_Int_Cast_uint128_to_uint64(m2);
  Hacl_Bignum_AddAndMultiply_add_and_multiply(Hacl_Impl_Poly1305_64___proj__MkState__item__h(st),
    tmp,
    Hacl_Impl_Poly1305_64___proj__MkState__item__r(st));
  return;
}

inline static void
Hacl_Impl_Poly1305_64_poly1305_process_last_block(
  void *log,
  Hacl_Impl_Poly1305_64_poly1305_state st,
  uint8_t *m,
  uint64_t rem_
)
{
  uint8_t zero = (uint8_t )0;
  //  KRML_CHECK_SIZE(zero, (uint32_t )16);
  uint8_t block[16] = {0};
  //  for (uintmax_t _i = 0; _i < (uint32_t )16; ++_i)
  //  block[_i] = zero;
  uint32_t i0 = (uint32_t )rem_;
  uint32_t i = (uint32_t )rem_;
  memcpy(block, m, i * sizeof m[0]);
  block[i0] = (uint8_t )1;
  Hacl_Impl_Poly1305_64_poly1305_process_last_block_((void *)(uint8_t )0, block, st, m, rem_);
}

inline static void Hacl_Impl_Poly1305_64_poly1305_last_pass(uint64_t *acc)
{
  Hacl_Bignum_Fproduct_carry_limb_(acc, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top(acc);
  uint64_t a0 = acc[0];
  uint64_t a10 = acc[1];
  uint64_t a20 = acc[2];
  uint64_t a0_ = a0 & (uint64_t )0xfffffffffff;
  uint64_t r0 = a0 >> (uint32_t )44;
  uint64_t a1_ = a10 + r0 & (uint64_t )0xfffffffffff;
  uint64_t r1 = a10 + r0 >> (uint32_t )44;
  uint64_t a2_ = a20 + r1;
  acc[0] = a0_;
  acc[1] = a1_;
  acc[2] = a2_;
  Hacl_Bignum_Modulo_carry_top(acc);
  Hacl_Bignum_Fproduct_carry_0_to_1(acc);
  uint64_t a00 = acc[0];
  uint64_t a1 = acc[1];
  uint64_t a2 = acc[2];
  uint64_t mask0 = FStar_UInt64_gte_mask(a00, (uint64_t )0xffffffffffb);
  uint64_t mask1 = FStar_UInt64_eq_mask(a1, (uint64_t )0xfffffffffff);
  uint64_t mask2 = FStar_UInt64_eq_mask(a2, (uint64_t )0x3ffffffffff);
  uint64_t mask = mask0 & mask1 & mask2;
  uint64_t a0_0 = a00 - ((uint64_t )0xffffffffffb & mask);
  uint64_t a1_0 = a1 - ((uint64_t )0xfffffffffff & mask);
  uint64_t a2_0 = a2 - ((uint64_t )0x3ffffffffff & mask);
  acc[0] = a0_0;
  acc[1] = a1_0;
  acc[2] = a2_0;
}

inline static void
Hacl_Standalone_Poly1305_64_poly1305_blocks(
  void *log,
  Hacl_Impl_Poly1305_64_poly1305_state st,
  uint8_t *m,
  uint64_t len
)
{
  for (int i = 0; i < len; i++) {
    uint8_t *block = m;
    uint8_t *tail = m + (uint32_t )16;
    Hacl_Impl_Poly1305_64_poly1305_update((void *)(uint8_t )0, st, block);
    m = tail;
  }
}

inline static void
Hacl_Standalone_Poly1305_64_poly1305_partial(
  Hacl_Impl_Poly1305_64_poly1305_state st,
  uint8_t *input,
  uint64_t len,
  uint8_t *kr
)
{
  uint64_t *x0 = Hacl_Impl_Poly1305_64___proj__MkState__item__r(st);
  uint8_t *x1 = kr;
  uint128_t m0_,m0, m1_, m1, m2;
  load128_le(m0_,x1);
  uint128_t msk;
  load128_64(msk, 0x0ffffffc0fffffff, 0x0ffffffc0ffffffc);
  uint128_logand(m0_,m0_,msk);
  uint128_split(m1_,m0,m0_,44);
  uint128_split(m2,m1,m1_,44);
  x0[0] = FStar_Int_Cast_uint128_to_uint64(m0);
  x0[1] = FStar_Int_Cast_uint128_to_uint64(m1);
  x0[2] = FStar_Int_Cast_uint128_to_uint64(m2);
  uint64_t *x00 = Hacl_Impl_Poly1305_64___proj__MkState__item__h(st);
  x00[0] = (uint64_t )0;
  x00[1] = (uint64_t )0;
  x00[2] = (uint64_t )0;
  Hacl_Standalone_Poly1305_64_poly1305_blocks((void *)(uint8_t )0, st, input, len);
  return;
}

inline static void
Hacl_Standalone_Poly1305_64_poly1305_complete(
  Hacl_Impl_Poly1305_64_poly1305_state st,
  uint8_t *m,
  uint64_t len,
  uint8_t *k
)
{
  uint8_t *kr = k;
  uint64_t len16 = len >> (uint32_t )4;
  uint64_t rem16 = len & (uint64_t )0xf;
  uint8_t *part_input = m;
  uint8_t *last_block = m + (uint32_t )((uint64_t )16 * len16);
  Hacl_Standalone_Poly1305_64_poly1305_partial(st, part_input, len16, kr);
  void *ite;
  if (rem16 == (uint64_t )0)
    ite = (void *)(uint8_t )0;
  else
    ite =
      (void *)(Hacl_Impl_Poly1305_64_poly1305_process_last_block((void *)(uint8_t )0,
        st,
        last_block,
        rem16)
      , (void *)0);
  uint64_t *acc = Hacl_Impl_Poly1305_64___proj__MkState__item__h(st);
  Hacl_Impl_Poly1305_64_poly1305_last_pass(acc);
  return;
}

inline static void
Hacl_Standalone_Poly1305_64_crypto_onetimeauth_(
  uint8_t *output,
  uint8_t *input,
  uint64_t len,
  uint8_t *k
)
{
  //  KRML_CHECK_SIZE((uint64_t )0, (uint32_t )6);
  uint64_t buf[6] = { 0 };
  uint64_t *r = buf;
  uint64_t *h = buf + (uint32_t )3;
  Hacl_Impl_Poly1305_64_poly1305_state st = buf;
  uint8_t *key_r = k;
  uint8_t *key_s = k + (uint32_t )16;
  Hacl_Standalone_Poly1305_64_poly1305_complete(st, input, len, k);
  uint64_t *acc = Hacl_Impl_Poly1305_64___proj__MkState__item__h(st);

  uint64_t h0 = acc[0];
  uint64_t h1 = acc[1];
  uint64_t h2 = acc[2];
  uint64_t accl = (h1 << 44) ^ h0;
  uint64_t acch = (h2 << 24) ^ (h1 >> 20);
  uint128_t acc_;
  load128_64(acc_,accl,acch);
  uint128_t k_, mac_;
  load128_le(k_,key_s);
  uint128_add_mod(mac_,acc_, k_);
  store128_le(output, mac_);
}

inline static void
Hacl_Standalone_Poly1305_64_crypto_onetimeauth(
  uint8_t *output,
  uint8_t *input,
  uint64_t len,
  uint8_t *k
)
{
  Hacl_Standalone_Poly1305_64_crypto_onetimeauth_(output, input, len, k);
  return;
}

void Poly1305_64_init(Hacl_Impl_Poly1305_64_poly1305_state st, uint8_t *k)
{
  uint8_t *x10 = k;
  uint64_t *x0 = Hacl_Impl_Poly1305_64___proj__MkState__item__r(st);
  uint8_t *x1 = x10;
  uint128_t m0__, m0_, m0, m1_,m1, m2;
  load128_le(m0__,x1);
  uint128_t msk;
  load128_64(msk, 0x0ffffffc0fffffff, 0x0ffffffc0ffffffc);
  uint128_logand(m0_,m0__,msk);
  uint128_split(m1_,m0,m0_,44);
  uint128_split(m2,m1,m1_,44);
  x0[0] = FStar_Int_Cast_uint128_to_uint64(m0);
  x0[1] = FStar_Int_Cast_uint128_to_uint64(m1);
  x0[2] = FStar_Int_Cast_uint128_to_uint64(m2);
  uint64_t *x00 = Hacl_Impl_Poly1305_64___proj__MkState__item__h(st);
  x00[0] = (uint64_t )0;
  x00[1] = (uint64_t )0;
  x00[2] = (uint64_t )0;
  return;
}

void *Poly1305_64_empty_log = (void *)(uint8_t )0;

void Poly1305_64_update_block(Hacl_Impl_Poly1305_64_poly1305_state st, uint8_t *m)
{
  Hacl_Impl_Poly1305_64_poly1305_update((void *)(uint8_t )0, st, m);
  return;
}

void Poly1305_64_update(Hacl_Impl_Poly1305_64_poly1305_state st, uint8_t *m, uint32_t len)
{
  if (len == (uint32_t )0)
    return;
  else
  {
    uint8_t *block = m;
    uint8_t *m_ = m + (uint32_t )16;
    uint32_t len0 = len - (uint32_t )1;
    Poly1305_64_update_block(st, block);
    Poly1305_64_update(st, m_, len0);
    return;
  }
}

void Poly1305_64_update_last(Hacl_Impl_Poly1305_64_poly1305_state st, uint8_t *m, uint32_t len)
{
  uint8_t *x2 = m;
  void *ite;
  if ((uint64_t )len == (uint64_t )0)
    ite = (void *)(uint8_t )0;
  else
    ite =
      (void *)(Hacl_Impl_Poly1305_64_poly1305_process_last_block((void *)(uint8_t )0,
        st,
        x2,
        (uint64_t )len)
      , (void *)0);
  uint64_t *acc = Hacl_Impl_Poly1305_64___proj__MkState__item__h(st);
  Hacl_Impl_Poly1305_64_poly1305_last_pass(acc);
  return;
}

void Poly1305_64_finish(Hacl_Impl_Poly1305_64_poly1305_state st, uint8_t *mac, uint8_t *k)
{
  uint64_t *acc = Hacl_Impl_Poly1305_64___proj__MkState__item__h(st);
  uint64_t h0 = acc[0];
  uint64_t h1 = acc[1];
  uint64_t h2 = acc[2];
  uint64_t accl = (h1 << 44) ^ h0;
  uint64_t acch = (h2 << 24) ^ (h1 >> 20);
  uint128_t acc_;
  load128_64(acc_,accl,acch);
  uint128_t k_, mac_;
  load128_le(k_,k);
  uint128_add_mod(mac_, acc_, k_);
  store128_le(mac, mac_);
  return;
}

void Poly1305_64_crypto_onetimeauth(uint8_t *output, uint8_t *input, uint64_t len, uint8_t *k)
{
  Hacl_Standalone_Poly1305_64_crypto_onetimeauth(output, input, len, k);
  return;
}

uint32_t Poly1305_64_mul_div_16(uint32_t len)
{
  return (uint32_t )16 * (len >> (uint32_t )4);
}

void
Poly1305_64_pad_last(
  void *log,
  Hacl_Impl_Poly1305_64_poly1305_state st,
  uint8_t *input,
  uint32_t len
)
{
  void *ite;
  uint8_t b[16];
  if (len == (uint32_t )0)
    ite = (void *)(uint8_t )0;
  else
  {
    //    KRML_CHECK_SIZE((uint8_t )0, (uint32_t )16);
    memset(b, 0, (uint32_t )16 * sizeof b[0]);
    memcpy(b, input, len * sizeof input[0]);
    uint8_t *b0 = b;
    Hacl_Impl_Poly1305_64_poly1305_update((void *)(uint8_t )0, st, b0);
    ite = (void *)(uint8_t )0;
  }
}

void
Poly1305_64_poly1305_blocks_init(
  Hacl_Impl_Poly1305_64_poly1305_state st,
  uint8_t *input,
  uint32_t len,
  uint8_t *k
)
{
  uint32_t len_16 = len >> (uint32_t )4;
  uint32_t rem_16 = len & (uint32_t )15;
  uint8_t *kr = k;
  uint32_t len_ = (uint32_t )16 * (len >> (uint32_t )4);
  uint8_t *part_input = input;
  uint8_t *last_block = input + len_;
  Hacl_Standalone_Poly1305_64_poly1305_partial(st, part_input, (uint64_t )len_16, kr);
  Poly1305_64_pad_last((void *)(uint8_t )0, st, last_block, rem_16);
  return;
}

void
Poly1305_64_poly1305_blocks_continue(
  void *log,
  Hacl_Impl_Poly1305_64_poly1305_state st,
  uint8_t *input,
  uint32_t len
)
{
  uint32_t len_16 = len >> (uint32_t )4;
  uint32_t rem_16 = len & (uint32_t )15;
  uint32_t len_ = (uint32_t )16 * (len >> (uint32_t )4);
  uint8_t *part_input = input;
  uint8_t *last_block = input + len_;
  Hacl_Standalone_Poly1305_64_poly1305_blocks((void *)(uint8_t )0,
    st,
    part_input,
    (uint64_t )len_16);
  Poly1305_64_pad_last((void *)(uint8_t )0, st, last_block, rem_16);
  return;
}

void
Poly1305_64_poly1305_blocks_finish_(
  void *log,
  Hacl_Impl_Poly1305_64_poly1305_state st,
  uint8_t *input
)
{
  Hacl_Impl_Poly1305_64_poly1305_update((void *)(uint8_t )0, st, input);
  uint8_t *x2 = input + (uint32_t )16;
  void *ite;
  if ((uint64_t )0 == (uint64_t )0)
    ite = (void *)(uint8_t )0;
  else
    ite =
      (void *)(Hacl_Impl_Poly1305_64_poly1305_process_last_block((void *)(uint8_t )0,
        st,
        x2,
        (uint64_t )0)
      , (void *)0);
  uint64_t *acc = Hacl_Impl_Poly1305_64___proj__MkState__item__h(st);
  Hacl_Impl_Poly1305_64_poly1305_last_pass(acc);
  return;
}

void
Poly1305_64_poly1305_blocks_finish(
  void *log,
  Hacl_Impl_Poly1305_64_poly1305_state st,
  uint8_t *input,
  uint8_t *mac,
  uint8_t *key_s
)
{
  Hacl_Impl_Poly1305_64_poly1305_update((void *)(uint8_t )0, st, input);
  uint8_t *x2 = input + (uint32_t )16;
  void *ite;
  if ((uint64_t )0 == (uint64_t )0)
    ite = (void *)(uint8_t )0;
  else
    ite =
      (void *)(Hacl_Impl_Poly1305_64_poly1305_process_last_block((void *)(uint8_t )0,
        st,
        x2,
        (uint64_t )0)
      , (void *)0);
  uint64_t *acc = Hacl_Impl_Poly1305_64___proj__MkState__item__h(st);
  Hacl_Impl_Poly1305_64_poly1305_last_pass(acc);
  uint64_t *acc0 = Hacl_Impl_Poly1305_64___proj__MkState__item__h(st);
  uint64_t h0 = acc0[0];
  uint64_t h1 = acc0[1];
  uint64_t h2 = acc0[2];
  uint64_t accl = (h1 << 44) ^ h0;
  uint64_t acch = (h2 << 24) ^ (h1 >> 20);
  uint128_t acc_;
  load128_64(acc_,accl,acch);
  uint128_t k_, mac_;
  load128_le(k_,key_s);
  uint128_add_mod(mac_,acc_, k_);
  store128_le(mac, mac_);
  return;
}

