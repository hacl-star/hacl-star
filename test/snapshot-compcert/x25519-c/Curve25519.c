#include "Curve25519.h"
//#define inline __attribute((noinline))
//#define static
inline static void Hacl_Bignum_Modulo_carry_top(uint64_t *b)
{
  uint64_t b4 = b[4];
  uint64_t b0 = b[0];
  uint64_t mask = ((uint64_t )1 << (uint32_t )51) - (uint64_t )1;
  uint64_t b4_ = b4 & mask;
  uint64_t b0_ = b0 + (uint64_t )19 * (b4 >> (uint32_t )51);
  b[4] = b4_;
  b[0] = b0_;
}

inline static void Hacl_Bignum_Modulo_reduce(uint64_t *b)
{
  uint64_t b0 = b[0];
  b[0] = (uint64_t )19 * b0;
}

inline static void Hacl_Bignum_Modulo_carry_top_wide(uint128_t *b)
{
  uint128_t b4h;
  uint128_split(b4h,b[4],b[4],51);
  uint64_t b4_ = FStar_Int_Cast_uint128_to_uint64(b4h);
  uint128_add64(b[0], b[0], b4_ * 19);
}

inline static void
Hacl_Bignum_Fproduct_copy_from_wide_(uint64_t *output, uint128_t *input, uint32_t ctr)
{
    output[0] = FStar_Int_Cast_uint128_to_uint64(input[0]);
    output[1] = FStar_Int_Cast_uint128_to_uint64(input[1]);
    output[2] = FStar_Int_Cast_uint128_to_uint64(input[2]);
    output[3] = FStar_Int_Cast_uint128_to_uint64(input[3]);
    output[4] = FStar_Int_Cast_uint128_to_uint64(input[4]);

  /*
  for (int i = 0; i < ctr; i++) 
  {
    output[i] = FStar_Int_Cast_uint128_to_uint64(input[i]);
  }
  */
}

inline static void Hacl_Bignum_Fproduct_shift_(uint64_t *output, uint32_t ctr)
{
  
  output[4] = output[3];
  output[3] = output[2];
  output[2] = output[1];
  output[1] = output[0];

  /*
  for (int i = ctr; i > 0; i--) 
  {
    uint64_t z = output[i - (uint32_t )1];
    output[i] = z;
  }
  */
}

inline static void Hacl_Bignum_Fproduct_shift(uint64_t *output)
{
  uint64_t tmp = output[4];
  Hacl_Bignum_Fproduct_shift_(output, (uint32_t )4);
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
  uint128_t mi;
  uint128_mul_wide(mi,input[0],s);
  uint128_add(output[0], output[0], mi);
  uint128_mul_wide(mi,input[1],s);
  uint128_add(output[1], output[1], mi);
  uint128_mul_wide(mi,input[2],s);
  uint128_add(output[2], output[2], mi);
  uint128_mul_wide(mi,input[3],s);
  uint128_add(output[3], output[3], mi);
  uint128_mul_wide(mi,input[4],s);
  uint128_add(output[4], output[4], mi);
  
  /*
  for (int i = 0; i < ctr; i++) 
  {
    uint64_t ii = input[i];
    uint128_t mi;
    uint128_mul_wide(mi,ii,s);
    uint128_add(output[i], output[i], mi);
  }
  */
}

inline static void Hacl_Bignum_Fproduct_carry_wide_(uint128_t *tmp, uint32_t ctr)
{
  uint128_t th;
  uint128_split(th,tmp[0],tmp[0],51);
  uint128_add(tmp[1],tmp[1], th);
  uint128_split(th,tmp[1],tmp[1],51);
  uint128_add(tmp[2],tmp[2], th);
  uint128_split(th,tmp[2],tmp[2],51);
  uint128_add(tmp[3],tmp[3], th);
  uint128_split(th,tmp[3],tmp[3],51);
  uint128_add(tmp[4],tmp[4], th);

  /*
  for (int i = 0; i < 4; i++)
  {
    uint128_t th;
    uint128_split(th,tmp[i],tmp[i],51);
    uint128_add(tmp[i+1],tmp[i+1], th);
  }
  */
}

inline static void Hacl_Bignum_Fproduct_carry_0_to_1(uint64_t *output)
{
  uint64_t i0 = output[0];
  uint64_t i1 = output[1];
  uint64_t i0_ = i0 & ((uint64_t )1 << (uint32_t )51) - (uint64_t )1;
  uint64_t i1_ = i1 + (i0 >> (uint32_t )51);
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
  
  Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2[0], (uint32_t )5);
  Hacl_Bignum_Fmul_shift_reduce(input);
  Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2[1], (uint32_t )5);
  Hacl_Bignum_Fmul_shift_reduce(input);
  Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2[2], (uint32_t )5);
  Hacl_Bignum_Fmul_shift_reduce(input);
  Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2[3], (uint32_t )5);
  Hacl_Bignum_Fmul_shift_reduce(input);
  Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2[4], (uint32_t )5);
  /*
  for (int i = 4; i >= 0; i--)
  {
    uint32_t j = (uint32_t )4 - i;
    uint64_t input2i = input2[j];
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2i, (uint32_t )5);
    if (i > (uint32_t )0)
      Hacl_Bignum_Fmul_shift_reduce(input);
  }
  */
}

inline static void Hacl_Bignum_Fmul_fmul_(uint64_t *output, uint64_t *input, uint64_t *input2)
{
  //  KRML_CHECK_SIZE(FStar_Int_Cast_uint64_to_uint128((uint64_t )0), (uint32_t )5);
  uint64_t t[10] = {0};
  //  for (uintmax_t _i = 0; _i < (uint32_t )5; ++_i)
  //  t[_i] = FStar_Int_Cast_uint64_to_uint128((uint64_t )0);
  void *input_init = (void *)(uint8_t )0;
  Hacl_Bignum_Fmul_mul_shift_reduce_(t, (void *)(uint8_t )0, input, input2, (uint32_t )5);
  Hacl_Bignum_Fproduct_carry_wide_(t, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top_wide(t);
  Hacl_Bignum_Fproduct_copy_from_wide_(output, t, (uint32_t )5);
  Hacl_Bignum_Fproduct_carry_0_to_1(output);
}

inline static void Hacl_Bignum_Fmul_fmul(uint64_t *output, uint64_t *input, uint64_t *input2)
{
  //  KRML_CHECK_SIZE((uint64_t )0, (uint32_t )5);
  uint64_t tmp[5];
  for (int i = 0; i < 5; i++)
    tmp[i] = input[i];
  Hacl_Bignum_Fmul_fmul_(output, tmp, input2);
}

inline static void
Hacl_Bignum_Fsquare_upd_5(
  uint128_t *tmp,
  uint128_t s0,
  uint128_t s1,
  uint128_t s2,
  uint128_t s3,
  uint128_t s4
)
{
  uint128_copy(tmp[0],s0);
  uint128_copy(tmp[1],s1);
  uint128_copy(tmp[2],s2);
  uint128_copy(tmp[3],s3);
  uint128_copy(tmp[4],s4);
}

inline static void Hacl_Bignum_Fsquare_fsquare__(uint128_t *tmp, uint64_t *output)
{
  uint64_t r0 = output[0];
  uint64_t r1 = output[1];
  uint64_t r2 = output[2];
  uint64_t r3 = output[3];
  uint64_t r4 = output[4];
  uint64_t d0 = r0 * (uint64_t )2;
  uint64_t d1 = r1 * (uint64_t )2;
  uint64_t d2 = r2 * (uint64_t )2 * (uint64_t )19;
  uint64_t d419 = r4 * (uint64_t )19;
  uint64_t d4 = d419 * (uint64_t )2;
  uint128_t m1,m2,m3,s0,s1,s2,s3,s4;
  uint128_mul_wide(m1,r0,r0);
  uint128_mul_wide(m2,d4,r1);
  uint128_mul_wide(m3,d2,r3);
  uint128_add(s0,m1,m2);
  uint128_add(s0,s0,m3);

  uint128_mul_wide(m1,d0,r1);
  uint128_mul_wide(m2,d4,r2);
  uint128_mul_wide(m3,r3 * 19,r3);
  uint128_add(s1,m1,m2);
  uint128_add(s1,s1,m3);

  uint128_mul_wide(m1,d0,r2);
  uint128_mul_wide(m2,r1,r1);
  uint128_mul_wide(m3,d4,r3);
  uint128_add(s2,m1,m2);
  uint128_add(s2,s2,m3);

  uint128_mul_wide(m1,d0,r3);
  uint128_mul_wide(m2,d1,r2);
  uint128_mul_wide(m3,r4,d419);
  uint128_add(s3,m1,m2);
  uint128_add(s3,s3,m3);

  uint128_mul_wide(m1,d0,r4);
  uint128_mul_wide(m2,d1,r3);
  uint128_mul_wide(m3,r2,r2);
  uint128_add(s4,m1,m2);
  uint128_add(s4,s4,m3);

  Hacl_Bignum_Fsquare_upd_5(tmp, s0, s1, s2, s3, s4);
  return;
}

inline static void Hacl_Bignum_Fsquare_fsquare_(uint128_t *tmp, uint64_t *output)
{
  Hacl_Bignum_Fsquare_fsquare__(tmp, output);
  Hacl_Bignum_Fproduct_carry_wide_(tmp, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top_wide(tmp);
  Hacl_Bignum_Fproduct_copy_from_wide_(output, tmp, (uint32_t )5);
  Hacl_Bignum_Fproduct_carry_0_to_1(output);
  return;
}

inline static void
Hacl_Bignum_Fsquare_fsquare_times_(uint64_t *output, uint128_t *tmp, uint32_t count)
{
  for (int i = 0; i < count; i++) {
    Hacl_Bignum_Fsquare_fsquare_(tmp,output);
  }
}

inline static void
Hacl_Bignum_Fsquare_fsquare_times(uint64_t *output, uint64_t *input, uint32_t count)
{
  uint64_t t[10] = {0};
  //  for (uintmax_t _i = 0; _i < (uint32_t )5; ++_i)
  //  t[_i] = FStar_Int_Cast_uint64_to_uint128((uint64_t )0);
  for (int i = 0; i < 5; i++)
    output[i] = input[i];
  //  memcpy(output, input, (uint32_t )5 * sizeof input[0]);
  Hacl_Bignum_Fsquare_fsquare_times_(output, t, count);
}

inline static void Hacl_Bignum_Fsquare_fsquare_times_inplace(uint64_t *output, uint32_t count)
{
  //  KRML_CHECK_SIZE(FStar_Int_Cast_uint64_to_uint128((uint64_t )0), (uint32_t )5);
  uint64_t t[10] = {0};
  Hacl_Bignum_Fsquare_fsquare_times_(output, t, count);
}

inline static void Hacl_Bignum_Crecip_crecip(uint64_t *out, uint64_t *z)
{
  //  KRML_CHECK_SIZE((uint64_t )0, (uint32_t )20);
  uint64_t buf[20] = { 0 };
  uint64_t *a = buf;
  uint64_t *t00 = buf + (uint32_t )5;
  uint64_t *b0 = buf + (uint32_t )10;
  uint64_t *c0 = buf + (uint32_t )15;
  Hacl_Bignum_Fsquare_fsquare_times(a, z, (uint32_t )1);
  Hacl_Bignum_Fsquare_fsquare_times(t00, a, (uint32_t )2);
  Hacl_Bignum_Fmul_fmul(b0, t00, z);
  Hacl_Bignum_Fmul_fmul(a, b0, a);
  Hacl_Bignum_Fsquare_fsquare_times(t00, a, (uint32_t )1);
  Hacl_Bignum_Fmul_fmul(b0, t00, b0);
  Hacl_Bignum_Fsquare_fsquare_times(t00, b0, (uint32_t )5);
  uint64_t *a0 = buf;
  uint64_t *t01 = buf + (uint32_t )5;
  uint64_t *b1 = buf + (uint32_t )10;
  uint64_t *c1 = buf + (uint32_t )15;
  Hacl_Bignum_Fmul_fmul(b1, t01, b1);
  Hacl_Bignum_Fsquare_fsquare_times(t01, b1, (uint32_t )10);
  Hacl_Bignum_Fmul_fmul(c1, t01, b1);
  Hacl_Bignum_Fsquare_fsquare_times(t01, c1, (uint32_t )20);
  Hacl_Bignum_Fmul_fmul(t01, t01, c1);
  Hacl_Bignum_Fsquare_fsquare_times_inplace(t01, (uint32_t )10);
  Hacl_Bignum_Fmul_fmul(b1, t01, b1);
  Hacl_Bignum_Fsquare_fsquare_times(t01, b1, (uint32_t )50);
  uint64_t *a1 = buf;
  uint64_t *t0 = buf + (uint32_t )5;
  uint64_t *b = buf + (uint32_t )10;
  uint64_t *c = buf + (uint32_t )15;
  Hacl_Bignum_Fmul_fmul(c, t0, b);
  Hacl_Bignum_Fsquare_fsquare_times(t0, c, (uint32_t )100);
  Hacl_Bignum_Fmul_fmul(t0, t0, c);
  Hacl_Bignum_Fsquare_fsquare_times_inplace(t0, (uint32_t )50);
  Hacl_Bignum_Fmul_fmul(t0, t0, b);
  Hacl_Bignum_Fsquare_fsquare_times_inplace(t0, (uint32_t )5);
  Hacl_Bignum_Fmul_fmul(out, t0, a1);
}

inline static void
Hacl_Bignum_Fscalar_fscalar_(uint128_t *output, uint64_t *b, uint64_t s, uint32_t i)
{
  for (int i = 0; i < 5; i++) {
    uint64_t bi = b[i];
    uint128_mul_wide(output[i],bi, s);
  }
}

inline static void
Hacl_Bignum_Fscalar_fscalar(uint128_t *output, uint64_t *b, uint64_t s)
{
  uint128_mul_wide(output[0],b[0], s);
  uint128_mul_wide(output[1],b[1], s);
  uint128_mul_wide(output[2],b[2], s);
  uint128_mul_wide(output[3],b[3], s);
  uint128_mul_wide(output[4],b[4], s);
  //  Hacl_Bignum_Fscalar_fscalar_(output, b, s, (uint32_t )5);
  return;
}

inline static void Hacl_Bignum_fsum(uint64_t *a, uint64_t *b)
{
  uint64_t a0 = a[0];
  uint64_t b0 = b[0];
  uint64_t a1 = a[1];
  uint64_t b1 = b[1];
  uint64_t a2 = a[2];
  uint64_t b2 = b[2];
  uint64_t a3 = a[3];
  uint64_t b3 = b[3];
  uint64_t a4 = a[4];
  uint64_t b4 = b[4];
  a[0] = a0 + b0;
  a[1] = a1 + b1;
  a[2] = a2 + b2;
  a[3] = a3 + b3;
  a[4] = a4 + b4;
}

inline static void Hacl_Bignum_fdifference(uint64_t *a, uint64_t *b)
{
  //  KRML_CHECK_SIZE((uint64_t )0, (uint32_t )5);
  uint64_t tmp[5];
  for (int i = 0; i < 5; i++)
    tmp[i] = b[i];
  uint64_t b00 = tmp[0];
  uint64_t b10 = tmp[1];
  uint64_t b20 = tmp[2];
  uint64_t b30 = tmp[3];
  uint64_t b40 = tmp[4];
  tmp[0] = b00 + (uint64_t )0x3fffffffffff68;
  tmp[1] = b10 + (uint64_t )0x3ffffffffffff8;
  tmp[2] = b20 + (uint64_t )0x3ffffffffffff8;
  tmp[3] = b30 + (uint64_t )0x3ffffffffffff8;
  tmp[4] = b40 + (uint64_t )0x3ffffffffffff8;
  uint64_t a0 = a[0];
  uint64_t b0 = tmp[0];
  uint64_t a1 = a[1];
  uint64_t b1 = tmp[1];
  uint64_t a2 = a[2];
  uint64_t b2 = tmp[2];
  uint64_t a3 = a[3];
  uint64_t b3 = tmp[3];
  uint64_t a4 = a[4];
  uint64_t b4 = tmp[4];
  a[0] = b0 - a0;
  a[1] = b1 - a1;
  a[2] = b2 - a2;
  a[3] = b3 - a3;
  a[4] = b4 - a4;
}

inline static void Hacl_Bignum_fscalar(uint64_t *output, uint64_t *b, uint64_t s)
{
  uint64_t tmp[10] = {0};
  Hacl_Bignum_Fscalar_fscalar(tmp, b, s);
  Hacl_Bignum_Fproduct_carry_wide_(tmp, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top_wide(tmp);
  Hacl_Bignum_Fproduct_copy_from_wide_(output, tmp, (uint32_t )5);
}

inline static void Hacl_Bignum_fmul(uint64_t *output, uint64_t *a, uint64_t *b)
{
  Hacl_Bignum_Fmul_fmul(output, a, b);
  return;
}

inline static void Hacl_Bignum_crecip(uint64_t *output, uint64_t *input)
{
  Hacl_Bignum_Crecip_crecip(output, input);
  return;
}

inline static void
Hacl_EC_Point_swap_conditional_step(uint64_t *a, uint64_t *b, uint64_t swap, uint32_t ctr)
{
  uint32_t i = ctr;
  uint64_t ai0 = a[i];
  uint64_t bi0 = b[i];
  uint64_t x = swap & (ai0 ^ bi0);
  uint64_t ai = ai0 ^ x;
  uint64_t bi = bi0 ^ x;
  a[i] = ai;
  b[i] = bi;
}

inline static void
Hacl_EC_Point_swap_conditional_(uint64_t *a, uint64_t *b, uint64_t swap, uint32_t ctr)
{

  uint64_t x;
  x = swap & (a[0] ^ b[0]);
  a[0] = a[0] ^ x;
  b[0] = b[0] ^ x;

  x = swap & (a[1] ^ b[1]);
  a[1] = a[1] ^ x;
  b[1] = b[1] ^ x;

  x = swap & (a[2] ^ b[2]);
  a[2] = a[2] ^ x;
  b[2] = b[2] ^ x;

  x = swap & (a[3] ^ b[3]);
  a[3] = a[3] ^ x;
  b[3] = b[3] ^ x;

  x = swap & (a[4] ^ b[4]);
  a[4] = a[4] ^ x;
  b[4] = b[4] ^ x;
  
  /*
    Hacl_EC_Point_swap_conditional_step(a, b, swap, 0);
    Hacl_EC_Point_swap_conditional_step(a, b, swap, 1);
    Hacl_EC_Point_swap_conditional_step(a, b, swap, 2);
    Hacl_EC_Point_swap_conditional_step(a, b, swap, 3);
    Hacl_EC_Point_swap_conditional_step(a, b, swap, 4);
  */  

  /*
  for (int i = 0; i < 5; i++) 
  {
    Hacl_EC_Point_swap_conditional_step(a, b, swap, i);
  }
  */
}

inline static void Hacl_EC_Point_swap_conditional(uint64_t *a, uint64_t *b, uint64_t iswap)
{
  uint64_t swap = 0 - iswap;
 Hacl_EC_Point_swap_conditional_(a, b, swap, (uint32_t )5);
  Hacl_EC_Point_swap_conditional_(a + (uint32_t )5, b + (uint32_t )5, swap, (uint32_t )5);
  return;
}

static void Hacl_EC_Point_copy(uint64_t *output, uint64_t *input)
{
  for (int i = 0; i < 10; i++)
    output[i] = input[i];
}

static void
Hacl_EC_AddAndDouble_fmonty(
  uint64_t *pp,
  uint64_t *ppq,
  uint64_t *p,
  uint64_t *pq,
  uint64_t *qmqp
)
{
  uint64_t *qx = qmqp;
  uint64_t *x2 = pp;
  uint64_t *z2 = pp + (uint32_t )5;
  uint64_t *x3 = ppq;
  uint64_t *z3 = ppq + (uint32_t )5;
  uint64_t *x = p;
  uint64_t *z = p + (uint32_t )5;
  uint64_t *xprime = pq;
  uint64_t *zprime = pq + (uint32_t )5;
  //  KRML_CHECK_SIZE((uint64_t )0, (uint32_t )40);
  uint64_t buf[40] = { 0 };
  uint64_t *origx = buf;
  uint64_t *origxprime0 = buf + (uint32_t )5;
  uint64_t *zzz0 = buf + (uint32_t )10;
  uint64_t *xx0 = buf + (uint32_t )15;
  uint64_t *zz0 = buf + (uint32_t )20;
  uint64_t *xxprime0 = buf + (uint32_t )25;
  uint64_t *zzprime0 = buf + (uint32_t )30;
  uint64_t *zzzprime0 = buf + (uint32_t )35;
  uint64_t *origx0 = buf;
  uint64_t *origxprime = buf + (uint32_t )5;
  uint64_t *zzz1 = buf + (uint32_t )10;
  uint64_t *xx1 = buf + (uint32_t )15;
  uint64_t *zz1 = buf + (uint32_t )20;
  uint64_t *xxprime1 = buf + (uint32_t )25;
  uint64_t *zzprime1 = buf + (uint32_t )30;
  uint64_t *zzzprime1 = buf + (uint32_t )35;
  for (int i = 0; i < 5; i++)
    origx0[i] = x[i];
  Hacl_Bignum_fsum(x, z);
  Hacl_Bignum_fdifference(z, origx0);
  for (int i = 0; i < 5; i++)
    origxprime[i] = xprime[i];
  Hacl_Bignum_fsum(xprime, zprime);
  Hacl_Bignum_fdifference(zprime, origxprime);
  Hacl_Bignum_fmul(xxprime1, xprime, z);
  Hacl_Bignum_fmul(zzprime1, x, zprime);
  uint64_t *origx1 = buf;
  uint64_t *origxprime1 = buf + (uint32_t )5;
  uint64_t *zzz = buf + (uint32_t )10;
  uint64_t *xx2 = buf + (uint32_t )15;
  uint64_t *zz2 = buf + (uint32_t )20;
  uint64_t *xxprime2 = buf + (uint32_t )25;
  uint64_t *zzprime = buf + (uint32_t )30;
  uint64_t *zzzprime = buf + (uint32_t )35;
  for (int i = 0; i < 5; i++)
    origxprime1[i] = xxprime2[i];
  Hacl_Bignum_fsum(xxprime2, zzprime);
  Hacl_Bignum_fdifference(zzprime, origxprime1);
  Hacl_Bignum_Fsquare_fsquare_times(x3, xxprime2, (uint32_t )1);
  Hacl_Bignum_Fsquare_fsquare_times(zzzprime, zzprime, (uint32_t )1);
  Hacl_Bignum_fmul(z3, zzzprime, qx);
  Hacl_Bignum_Fsquare_fsquare_times(xx2, x, (uint32_t )1);
  Hacl_Bignum_Fsquare_fsquare_times(zz2, z, (uint32_t )1);
  uint64_t *origx2 = buf;
  uint64_t *origxprime2 = buf + (uint32_t )5;
  uint64_t *zzz2 = buf + (uint32_t )10;
  uint64_t *xx = buf + (uint32_t )15;
  uint64_t *zz = buf + (uint32_t )20;
  uint64_t *xxprime = buf + (uint32_t )25;
  uint64_t *zzprime2 = buf + (uint32_t )30;
  uint64_t *zzzprime2 = buf + (uint32_t )35;
  Hacl_Bignum_fmul(x2, xx, zz);
  Hacl_Bignum_fdifference(zz, xx);
  uint64_t scalar = (uint64_t )121665;
  Hacl_Bignum_fscalar(zzz2, zz, scalar);
  Hacl_Bignum_fsum(zzz2, xx);
  Hacl_Bignum_fmul(z2, zzz2, zz);
}

inline static void
Hacl_EC_Ladder_SmallLoop_cmult_small_loop_step_1(
  uint64_t *nq,
  uint64_t *nqpq,
  uint64_t *nq2,
  uint64_t *nqpq2,
  uint64_t *q,
  uint8_t byt
)
{
  uint64_t bit = (uint64_t )(byt >> (uint32_t )7);
  Hacl_EC_Point_swap_conditional(nq, nqpq, bit);
  return;
}

inline static void
Hacl_EC_Ladder_SmallLoop_cmult_small_loop_step_2(
  uint64_t *nq,
  uint64_t *nqpq,
  uint64_t *nq2,
  uint64_t *nqpq2,
  uint64_t *q,
  uint8_t byt
)
{
  Hacl_EC_AddAndDouble_fmonty(nq2, nqpq2, nq, nqpq, q);
  return;
}

inline static void
Hacl_EC_Ladder_SmallLoop_cmult_small_loop_step(
  uint64_t *nq,
  uint64_t *nqpq,
  uint64_t *nq2,
  uint64_t *nqpq2,
  uint64_t *q,
  uint8_t byt
)
{
  Hacl_EC_Ladder_SmallLoop_cmult_small_loop_step_1(nq, nqpq, nq2, nqpq2, q, byt);
  Hacl_EC_Ladder_SmallLoop_cmult_small_loop_step_2(nq, nqpq, nq2, nqpq2, q, byt);
  Hacl_EC_Ladder_SmallLoop_cmult_small_loop_step_1(nq2, nqpq2, nq, nqpq, q, byt);
  return;
}

inline static void
Hacl_EC_Ladder_SmallLoop_cmult_small_loop_double_step(
  uint64_t *nq,
  uint64_t *nqpq,
  uint64_t *nq2,
  uint64_t *nqpq2,
  uint64_t *q,
  uint8_t byt
)
{
  Hacl_EC_Ladder_SmallLoop_cmult_small_loop_step(nq, nqpq, nq2, nqpq2, q, byt);
  uint8_t byt0 = byt << (uint32_t )1;
  Hacl_EC_Ladder_SmallLoop_cmult_small_loop_step(nq2, nqpq2, nq, nqpq, q, byt0);
  return;
}

inline static void
Hacl_EC_Ladder_SmallLoop_cmult_small_loop(
  uint64_t *nq,
  uint64_t *nqpq,
  uint64_t *nq2,
  uint64_t *nqpq2,
  uint64_t *q,
  uint8_t byt,
  uint32_t j
)
{
  for (int i = 0; i < 4; i++)
  {
    Hacl_EC_Ladder_SmallLoop_cmult_small_loop_double_step(nq, nqpq, nq2, nqpq2, q, byt);
    byt = byt << (uint32_t )2;
  }
}

inline static void
Hacl_EC_Ladder_BigLoop_cmult_big_loop(
  uint8_t *n,
  uint64_t *nq,
  uint64_t *nqpq,
  uint64_t *nq2,
  uint64_t *nqpq2,
  uint64_t *q,
  uint32_t i
)
{
  /*
  if (i == (uint32_t )0)
    return;
  else
  {
    uint32_t i0 = i - (uint32_t )1;
    uint8_t byte = n[i0];
    Hacl_EC_Ladder_SmallLoop_cmult_small_loop(nq, nqpq, nq2, nqpq2, q, byte, (uint32_t )4);
    Hacl_EC_Ladder_BigLoop_cmult_big_loop(n, nq, nqpq, nq2, nqpq2, q, i0);
    return;
  }
  */
  for (int i0 = 31; i0 >= 0; i0--)
  {
    uint8_t byte = n[i0];
    Hacl_EC_Ladder_SmallLoop_cmult_small_loop(nq, nqpq, nq2, nqpq2, q, byte, (uint32_t )4);
    }
}

inline static void
Hacl_EC_Ladder_cmult_(uint64_t *result, uint64_t *point_buf, uint8_t *n, uint64_t *q)
{
  uint64_t *nq = point_buf;
  uint64_t *nqpq = point_buf + (uint32_t )10;
  uint64_t *nq2 = point_buf + (uint32_t )20;
  uint64_t *nqpq2 = point_buf + (uint32_t )30;
  Hacl_EC_Point_copy(nqpq, q);
  nq[0] = (uint64_t )1;
  Hacl_EC_Ladder_BigLoop_cmult_big_loop(n, nq, nqpq, nq2, nqpq2, q, (uint32_t )32);
  Hacl_EC_Point_copy(result, nq);
  return;
}

inline static void Hacl_EC_Ladder_cmult(uint64_t *result, uint8_t *n, uint64_t *q)
{
  //  KRML_CHECK_SIZE((uint64_t )0, (uint32_t )40);
  uint64_t point_buf[40] = { 0 };
  Hacl_EC_Ladder_cmult_(result, point_buf, n, q);
}

inline static void
Hacl_EC_Format_upd_5(
  uint64_t *output,
  uint64_t output0,
  uint64_t output1,
  uint64_t output2,
  uint64_t output3,
  uint64_t output4
)
{
  output[0] = output0;
  output[1] = output1;
  output[2] = output2;
  output[3] = output3;
  output[4] = output4;
}

inline static void
Hacl_EC_Format_upd_5_(
  uint64_t *output,
  uint64_t output0,
  uint64_t output1,
  uint64_t output2,
  uint64_t output3,
  uint64_t output4
)
{
  output[0] = output0;
  output[1] = output1;
  output[2] = output2;
  output[3] = output3;
  output[4] = output4;
}

static void Hacl_EC_Format_fexpand(uint64_t *output, uint8_t *input)
{
  uint64_t mask_51 = (uint64_t )0x7ffffffffffff;
  uint8_t *x00 = input;
  uint64_t i0 = load64_le(x00);
  uint8_t *x01 = input + (uint32_t )6;
  uint64_t i1 = load64_le(x01);
  uint8_t *x02 = input + (uint32_t )12;
  uint64_t i2 = load64_le(x02);
  uint8_t *x03 = input + (uint32_t )19;
  uint64_t i3 = load64_le(x03);
  uint8_t *x0 = input + (uint32_t )24;
  uint64_t i4 = load64_le(x0);
  uint64_t output0 = i0 & mask_51;
  uint64_t output1 = i1 >> (uint32_t )3 & mask_51;
  uint64_t output2 = i2 >> (uint32_t )6 & mask_51;
  uint64_t output3 = i3 >> (uint32_t )1 & mask_51;
  uint64_t output4 = i4 >> (uint32_t )12 & mask_51;
  Hacl_EC_Format_upd_5(output, output0, output1, output2, output3, output4);
  return;
}

inline static void
Hacl_EC_Format_store_4(uint8_t *output, uint64_t v0, uint64_t v1, uint64_t v2, uint64_t v3)
{
  uint8_t *b0 = output;
  uint8_t *b1 = output + (uint32_t )8;
  uint8_t *b2 = output + (uint32_t )16;
  uint8_t *b3 = output + (uint32_t )24;
  store64_le(b0, v0);
  store64_le(b1, v1);
  store64_le(b2, v2);
  store64_le(b3, v3);
  return;
}

static void Hacl_EC_Format_fcontract_first_carry_pass(uint64_t *input)
{
  uint64_t t0 = input[0];
  uint64_t t1 = input[1];
  uint64_t t2 = input[2];
  uint64_t t3 = input[3];
  uint64_t t4 = input[4];
  uint64_t t1_ = t1 + (t0 >> (uint32_t )51);
  uint64_t t0_ = t0 & (uint64_t )0x7ffffffffffff;
  uint64_t t2_ = t2 + (t1_ >> (uint32_t )51);
  uint64_t t1__ = t1_ & (uint64_t )0x7ffffffffffff;
  uint64_t t3_ = t3 + (t2_ >> (uint32_t )51);
  uint64_t t2__ = t2_ & (uint64_t )0x7ffffffffffff;
  uint64_t t4_ = t4 + (t3_ >> (uint32_t )51);
  uint64_t t3__ = t3_ & (uint64_t )0x7ffffffffffff;
  Hacl_EC_Format_upd_5_(input, t0_, t1__, t2__, t3__, t4_);
  return;
}

static void Hacl_EC_Format_fcontract_first_carry_full(uint64_t *input)
{
  Hacl_EC_Format_fcontract_first_carry_pass(input);
  Hacl_Bignum_Modulo_carry_top(input);
  return;
}

static void Hacl_EC_Format_fcontract_second_carry_pass(uint64_t *input)
{
  uint64_t t0 = input[0];
  uint64_t t1 = input[1];
  uint64_t t2 = input[2];
  uint64_t t3 = input[3];
  uint64_t t4 = input[4];
  uint64_t t1_ = t1 + (t0 >> (uint32_t )51);
  uint64_t t0_ = t0 & (uint64_t )0x7ffffffffffff;
  uint64_t t2_ = t2 + (t1_ >> (uint32_t )51);
  uint64_t t1__ = t1_ & (uint64_t )0x7ffffffffffff;
  uint64_t t3_ = t3 + (t2_ >> (uint32_t )51);
  uint64_t t2__ = t2_ & (uint64_t )0x7ffffffffffff;
  uint64_t t4_ = t4 + (t3_ >> (uint32_t )51);
  uint64_t t3__ = t3_ & (uint64_t )0x7ffffffffffff;
  Hacl_EC_Format_upd_5_(input, t0_, t1__, t2__, t3__, t4_);
  return;
}

static void Hacl_EC_Format_fcontract_second_carry_full(uint64_t *input)
{
  Hacl_EC_Format_fcontract_second_carry_pass(input);
  Hacl_Bignum_Modulo_carry_top(input);
  Hacl_Bignum_Fproduct_carry_0_to_1(input);
  return;
}

static void Hacl_EC_Format_fcontract_trim(uint64_t *input)
{
  uint64_t a0 = input[0];
  uint64_t a1 = input[1];
  uint64_t a2 = input[2];
  uint64_t a3 = input[3];
  uint64_t a4 = input[4];
  uint64_t mask0 = FStar_UInt64_gte_mask(a0, (uint64_t )0x7ffffffffffed);
  uint64_t mask1 = FStar_UInt64_eq_mask(a1, (uint64_t )0x7ffffffffffff);
  uint64_t mask2 = FStar_UInt64_eq_mask(a2, (uint64_t )0x7ffffffffffff);
  uint64_t mask3 = FStar_UInt64_eq_mask(a3, (uint64_t )0x7ffffffffffff);
  uint64_t mask4 = FStar_UInt64_eq_mask(a4, (uint64_t )0x7ffffffffffff);
  uint64_t mask = mask0 & mask1 & mask2 & mask3 & mask4;
  uint64_t a0_ = a0 - ((uint64_t )0x7ffffffffffed & mask);
  uint64_t a1_ = a1 - ((uint64_t )0x7ffffffffffff & mask);
  uint64_t a2_ = a2 - ((uint64_t )0x7ffffffffffff & mask);
  uint64_t a3_ = a3 - ((uint64_t )0x7ffffffffffff & mask);
  uint64_t a4_ = a4 - ((uint64_t )0x7ffffffffffff & mask);
  Hacl_EC_Format_upd_5_(input, a0_, a1_, a2_, a3_, a4_);
  return;
}

static void Hacl_EC_Format_fcontract_store(uint8_t *output, uint64_t *input)
{
  uint64_t t0 = input[0];
  uint64_t t1 = input[1];
  uint64_t t2 = input[2];
  uint64_t t3 = input[3];
  uint64_t t4 = input[4];
  uint64_t o0 = t1 << (uint32_t )51 | t0;
  uint64_t o1 = t2 << (uint32_t )38 | t1 >> (uint32_t )13;
  uint64_t o2 = t3 << (uint32_t )25 | t2 >> (uint32_t )26;
  uint64_t o3 = t4 << (uint32_t )12 | t3 >> (uint32_t )39;
  Hacl_EC_Format_store_4(output, o0, o1, o2, o3);
  return;
}

static void Hacl_EC_Format_fcontract(uint8_t *output, uint64_t *input)
{
  Hacl_EC_Format_fcontract_first_carry_full(input);
  Hacl_EC_Format_fcontract_second_carry_full(input);
  Hacl_EC_Format_fcontract_trim(input);
  Hacl_EC_Format_fcontract_store(output, input);
  return;
}

static void Hacl_EC_Format_scalar_of_point(uint8_t *scalar, uint64_t *point)
{
  uint64_t *x = point;
  uint64_t *z = point + (uint32_t )5;
  //  KRML_CHECK_SIZE((uint64_t )0, (uint32_t )10);
  uint64_t buf[10] = { 0 };
  uint64_t *zmone = buf;
  uint64_t *sc = buf + (uint32_t )5;
  Hacl_Bignum_crecip(zmone, z);
  Hacl_Bignum_fmul(sc, x, zmone);
  Hacl_EC_Format_fcontract(scalar, sc);
}

static void
Hacl_EC_crypto_scalarmult__(
  uint8_t *mypublic,
  uint8_t *scalar,
  uint8_t *basepoint,
  uint64_t *q
)
{
  //  KRML_CHECK_SIZE((uint64_t )0, (uint32_t )15);
  uint64_t buf[15] = { 0 };
  uint64_t *nq = buf;
  uint64_t *x = nq;
  uint64_t *z = nq + (uint32_t )5;
  uint64_t *zmone = buf + (uint32_t )5;
  x[0] = (uint64_t )1;
  Hacl_EC_Ladder_cmult(nq, scalar, q);
  Hacl_EC_Format_scalar_of_point(mypublic, nq);
}

static void
Hacl_EC_crypto_scalarmult_(uint8_t *mypublic, uint8_t *secret, uint8_t *basepoint, uint64_t *q)
{
  //  KRML_CHECK_SIZE((uint8_t )0, (uint32_t )32);
  uint8_t e[32] = { 0 };
  memcpy(e, secret, (uint32_t )32 * sizeof secret[0]);
  uint8_t e00 = e[0];
  uint8_t e310 = e[31];
  uint8_t e0 = e00 & (uint8_t )248;
  uint8_t e31 = e310 & (uint8_t )127;
  uint8_t e311 = e31 | (uint8_t )64;
  e[0] = e0;
  e[31] = e311;
  uint8_t *scalar = e;
  Hacl_EC_crypto_scalarmult__(mypublic, scalar, basepoint, q);
}

void Hacl_EC_crypto_scalarmult(uint8_t *mypublic, uint8_t *secret, uint8_t *basepoint)
{
  //  KRML_CHECK_SIZE((uint64_t )0, (uint32_t )10);
  uint64_t buf[10] = { 0 };
  uint64_t *x = buf;
  uint64_t *z = buf + (uint32_t )5;
  Hacl_EC_Format_fexpand(x, basepoint);
  z[0] = (uint64_t )1;
  uint64_t *q = buf;
  Hacl_EC_crypto_scalarmult_(mypublic, secret, basepoint, q);
}

void Curve25519_crypto_scalarmult(uint8_t *mypublic, uint8_t *secret, uint8_t *basepoint)
{
  Hacl_EC_crypto_scalarmult(mypublic, secret, basepoint);
  return;
}

