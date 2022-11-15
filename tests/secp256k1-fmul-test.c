#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdbool.h>
#include <time.h>

#include "Hacl_Bignum_K256.h"
//#include "secp256k1-inline.h"
#include "Hacl_Bignum_Base.h"

#include "test_helpers.h"

#define ROUNDS 209715200

static inline void carry_wide(uint64_t *out, uint64_t *f)
{
  uint64_t *uu____0 = f + (uint32_t)4U;
  uint64_t *uu____1 = f;
  uint64_t *res_j = uu____1;
  uint64_t c0 = (uint64_t)0U;
  {
    uint64_t a_i = uu____0[(uint32_t)4U * (uint32_t)0U];
    uint64_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
    c0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, (uint64_t)0x1000003D1U, c0, res_i0);
    uint64_t a_i0 = uu____0[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
    c0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, (uint64_t)0x1000003D1U, c0, res_i1);
    uint64_t a_i1 = uu____0[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
    c0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, (uint64_t)0x1000003D1U, c0, res_i2);
    uint64_t a_i2 = uu____0[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint64_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
    c0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, (uint64_t)0x1000003D1U, c0, res_i);
  }
  uint64_t r = c0;
  uint64_t c00 = r;
  uint64_t *uu____2 = f + (uint32_t)4U;
  uint64_t *uu____3 = f;
  uint128_t x = (uint128_t)c00 * (uint64_t)0x1000003D1U;
  uint64_t x_lo = (uint64_t)x;
  uint64_t x_hi = (uint64_t)(x >> (uint32_t)64U);
  uu____2[0U] = x_lo;
  uu____2[1U] = x_hi;
  uint64_t *a0 = uu____3;
  uint64_t *res0 = out;
  uint64_t c2 = (uint64_t)0U;
  KRML_MAYBE_FOR2(i,
    (uint32_t)0U,
    (uint32_t)2U,
    (uint32_t)1U,
    uint64_t t1 = a0[i];
    uint64_t t2 = uu____2[i];
    uint64_t *res_i = res0 + i;
    c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t1, t2, res_i););
  uint64_t c01 = c2;
  uint64_t *a10 = uu____3 + (uint32_t)2U;
  uint64_t *res10 = out + (uint32_t)2U;
  uint64_t c = c01;
  KRML_MAYBE_FOR2(i,
    (uint32_t)0U,
    (uint32_t)2U,
    (uint32_t)1U,
    uint64_t t1 = a10[i];
    uint64_t *res_i = res10 + i;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i););
  uint64_t c10 = c;
  uint64_t c3 = c10;
  uint64_t
  c010 =
    Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U,
      out[0U],
      c3 * (uint64_t)0x1000003D1U,
      out);
  uint64_t *a1 = out + (uint32_t)1U;
  uint64_t *res1 = out + (uint32_t)1U;
  uint64_t c1 = c010;
  KRML_MAYBE_FOR3(i,
    (uint32_t)0U,
    (uint32_t)3U,
    (uint32_t)1U,
    uint64_t t1 = a1[i];
    uint64_t *res_i = res1 + i;
    c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, (uint64_t)0U, res_i););
  uint64_t c11 = c1;
  uint64_t c12 = c11;
  out[0U] = out[0U] + c12 * (uint64_t)0x1000003D1U;
}

static inline void Hacl_Impl_K256_Field64_fmul(uint64_t *out, uint64_t *f1, uint64_t *f2)
{
  uint64_t tmp[8U] = { 0U };
  memset(tmp, 0U, (uint32_t)8U * sizeof (uint64_t));
  KRML_MAYBE_FOR4(i0,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t bj = f2[i0];
    uint64_t *res_j = tmp + i0;
    uint64_t c = (uint64_t)0U;
    {
      uint64_t a_i = f1[(uint32_t)4U * (uint32_t)0U];
      uint64_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i0);
      uint64_t a_i0 = f1[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint64_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c, res_i1);
      uint64_t a_i1 = f1[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint64_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c, res_i2);
      uint64_t a_i2 = f1[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint64_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c, res_i);
    }
    uint64_t r = c;
    tmp[(uint32_t)4U + i0] = r;);
  carry_wide(out, tmp);
}

static inline void Hacl_Impl_K256_Field64_fsqr(uint64_t *out, uint64_t *f)
{
  uint64_t tmp[8U] = { 0U };
  memset(tmp, 0U, (uint32_t)8U * sizeof (uint64_t));
  KRML_MAYBE_FOR4(i0,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *ab = f;
    uint64_t a_j = f[i0];
    uint64_t *res_j = tmp + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < i0 / (uint32_t)4U; i++)
    {
      uint64_t a_i = ab[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c, res_i0);
      uint64_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, a_j, c, res_i1);
      uint64_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, a_j, c, res_i2);
      uint64_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, a_j, c, res_i);
    }
    for (uint32_t i = i0 / (uint32_t)4U * (uint32_t)4U; i < i0; i++)
    {
      uint64_t a_i = ab[i];
      uint64_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c, res_i);
    }
    uint64_t r = c;
    tmp[i0 + i0] = r;);
  uint64_t c0 = Hacl_Bignum_Addition_bn_add_eq_len_u64((uint32_t)8U, tmp, tmp, tmp);
  uint64_t tmp1[8U] = { 0U };
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint128_t res = (uint128_t)f[i] * f[i];
    uint64_t hi = (uint64_t)(res >> (uint32_t)64U);
    uint64_t lo = (uint64_t)res;
    tmp1[(uint32_t)2U * i] = lo;
    tmp1[(uint32_t)2U * i + (uint32_t)1U] = hi;);
  uint64_t c1 = Hacl_Bignum_Addition_bn_add_eq_len_u64((uint32_t)8U, tmp, tmp1, tmp);
  carry_wide(out, tmp);
}

int main() {
  cycles a,b;
  clock_t t1,t2;
  uint64_t count = ROUNDS;

  uint64_t bignum_a[5U] = { 197876, 241305, 245979, 490424, 284994 };
  uint64_t bignum_b[5U] = { 180879, 475851, 123829, 108058, 144159 };

  // Benchmarking for Hacl_K256_Field_fmul
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_K256_Field_fmul(bignum_b, bignum_a, bignum_b);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_K256_Field_fmul(bignum_b, bignum_a, bignum_b);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff1 = t2 - t1;
  uint64_t cyc1 = b - a;

  // Benchmarking for Hacl_K256_Field_fsqr
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_K256_Field_fsqr(bignum_b, bignum_b);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_K256_Field_fsqr(bignum_b, bignum_b);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff2 = t2 - t1;
  uint64_t cyc2 = b - a;

  bool b1 = bignum_b[1] == 2 ? 0 : 1;
  printf("b1 = %d\n", b1);

  printf("\n secp256k1_fmul:\n");
  print_time(count,diff1,cyc1);
  printf("\n secp256k1_fsqr:\n");
  print_time(count,diff2,cyc2);

  //  ---------------------------------------------------

  uint64_t bignum_a4[4U] = { 197876, 241305, 245979, 490424 };
  uint64_t bignum_b4[4U] = { 180879, 475851, 123829, 108058 };
  uint64_t tmp4[16U] = { 0U };

 /* // Benchmarking for secp256k1_Field64_fmul */
 /*  for (int j = 0; j < ROUNDS; j++) { */
 /*    // (out, f1, f2, tmp) */
 /*    fmul(bignum_b4, bignum_a4, bignum_b4, tmp4); */
 /*  } */

 /*  t1 = clock(); */
 /*  a = cpucycles_begin(); */
 /*  for (int j = 0; j < ROUNDS; j++) { */
 /*    fmul(bignum_b4, bignum_a4, bignum_b4, tmp4); */
 /*  } */
 /*  b = cpucycles_end(); */
 /*  t2 = clock(); */
 /*  double diff5 = t2 - t1; */
 /*  uint64_t cyc5 = b - a; */

 /* // Benchmarking for secp256k1_Field64_fsqr */
 /*  for (int j = 0; j < ROUNDS; j++) { */
 /*    // (out, f, tmp) */
 /*    fsqr(bignum_b4, bignum_b4, tmp4); */
 /*  } */

 /*  t1 = clock(); */
 /*  a = cpucycles_begin(); */
 /*  for (int j = 0; j < ROUNDS; j++) { */
 /*    fsqr(bignum_b4, bignum_b4, tmp4); */
 /*  } */
 /*  b = cpucycles_end(); */
 /*  t2 = clock(); */
 /*  double diff6 = t2 - t1; */
 /*  uint64_t cyc6 = b - a; */

 /*  bool b2 = bignum_b4[1] == 2 ? 0 : 1; */
 /*  printf("b2 = %d\n", b2); */

 /*  printf("\n secp256k1_fmul_64 (inline asm secp256k1-inline.h):\n"); */
 /*  print_time(count,diff5,cyc5); */
 /*  printf("\n secp256k1_fsqr_64 (inline asm secp256k1-inline.h):\n"); */
 /*  print_time(count,diff6,cyc6); */

  //--------------------------------------
 // Benchmarking for secp256k1_Field64_fmul
  for (int j = 0; j < ROUNDS; j++) {
    // (out, f1, f2)
    Hacl_Impl_K256_Field64_fmul(bignum_b4, bignum_a4, bignum_b4);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Impl_K256_Field64_fmul(bignum_b4, bignum_a4, bignum_b4);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff7 = t2 - t1;
  uint64_t cyc7 = b - a;

 // Benchmarking for secp256k1_Field64_fsqr
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Impl_K256_Field64_fsqr(bignum_b4, bignum_b4);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Impl_K256_Field64_fsqr(bignum_b4, bignum_b4);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff8 = t2 - t1;
  uint64_t cyc8 = b - a;

  bool b3 = bignum_b4[1] == 2 ? 0 : 1;
  printf("b3 = %d\n", b3);

  printf("\n secp256k1_fmul_64 (slow):\n");
  print_time(count,diff7,cyc7);
  printf("\n secp256k1_fsqr_64 (slow):\n");
  print_time(count,diff8,cyc8);


  return EXIT_SUCCESS;
}
