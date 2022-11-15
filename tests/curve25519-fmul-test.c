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

#include "Hacl_Bignum25519_51.h"
#include "curve25519-inline.h"
#include "internal/Vale.h"
#include "Hacl_Curve25519_64_Slow.h"

#include "test_helpers.h"

#define ROUNDS 209715200


static inline void fmul_(uint64_t *out, uint64_t *f1, uint64_t *f2, uint64_t *tmp)
{
  uint64_t *tmp0 = tmp;
  memset(tmp0, 0U, (uint32_t)8U * sizeof (uint64_t));
  KRML_MAYBE_FOR4(i0,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t bj = f2[i0];
    uint64_t *res_j = tmp0 + i0;
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
    tmp0[(uint32_t)4U + i0] = r;);
  uint64_t *uu____0 = tmp0 + (uint32_t)4U;
  uint64_t *uu____1 = tmp0;
  uint64_t *res_j = uu____1;
  uint64_t c0 = (uint64_t)0U;
  {
    uint64_t a_i = uu____0[(uint32_t)4U * (uint32_t)0U];
    uint64_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
    c0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, (uint64_t)38U, c0, res_i0);
    uint64_t a_i0 = uu____0[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
    c0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, (uint64_t)38U, c0, res_i1);
    uint64_t a_i1 = uu____0[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
    c0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, (uint64_t)38U, c0, res_i2);
    uint64_t a_i2 = uu____0[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint64_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
    c0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, (uint64_t)38U, c0, res_i);
  }
  uint64_t r = c0;
  uint64_t c00 = r;
  uint64_t *uu____2 = tmp0;
  uint64_t
  c01 =
    Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U,
      uu____2[0U],
      c00 * (uint64_t)38U,
      out);
  uint64_t *a1 = uu____2 + (uint32_t)1U;
  uint64_t *res1 = out + (uint32_t)1U;
  uint64_t c = c01;
  KRML_MAYBE_FOR3(i,
    (uint32_t)0U,
    (uint32_t)3U,
    (uint32_t)1U,
    uint64_t t1 = a1[i];
    uint64_t *res_i = res1 + i;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i););
  uint64_t c1 = c;
  uint64_t c2 = c1;
  out[0U] = out[0U] + c2 * (uint64_t)38U;
}

static inline void fsqr_(uint64_t *out, uint64_t *f1, uint64_t *tmp)
{
  memset(tmp, 0U, (uint32_t)8U * sizeof (uint64_t));
  KRML_MAYBE_FOR4(i0,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *ab = f1;
    uint64_t a_j = f1[i0];
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
    FStar_UInt128_uint128 res = FStar_UInt128_mul_wide(f1[i], f1[i]);
    uint64_t hi = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res, (uint32_t)64U));
    uint64_t lo = FStar_UInt128_uint128_to_uint64(res);
    tmp1[(uint32_t)2U * i] = lo;
    tmp1[(uint32_t)2U * i + (uint32_t)1U] = hi;);
  uint64_t c1 = Hacl_Bignum_Addition_bn_add_eq_len_u64((uint32_t)8U, tmp, tmp1, tmp);
  uint64_t *uu____0 = tmp + (uint32_t)4U;
  uint64_t *uu____1 = tmp;
  uint64_t *res_j = uu____1;
  uint64_t c2 = (uint64_t)0U;
  {
    uint64_t a_i = uu____0[(uint32_t)4U * (uint32_t)0U];
    uint64_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
    c2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, (uint64_t)38U, c2, res_i0);
    uint64_t a_i0 = uu____0[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
    c2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, (uint64_t)38U, c2, res_i1);
    uint64_t a_i1 = uu____0[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
    c2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, (uint64_t)38U, c2, res_i2);
    uint64_t a_i2 = uu____0[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint64_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
    c2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, (uint64_t)38U, c2, res_i);
  }
  uint64_t r = c2;
  uint64_t c00 = r;
  uint64_t *uu____2 = tmp;
  uint64_t
  c01 =
    Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U,
      uu____2[0U],
      c00 * (uint64_t)38U,
      out);
  uint64_t *a1 = uu____2 + (uint32_t)1U;
  uint64_t *res1 = out + (uint32_t)1U;
  uint64_t c = c01;
  KRML_MAYBE_FOR3(i,
    (uint32_t)0U,
    (uint32_t)3U,
    (uint32_t)1U,
    uint64_t t1 = a1[i];
    uint64_t *res_i = res1 + i;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i););
  uint64_t c10 = c;
  uint64_t c3 = c10;
  out[0U] = out[0U] + c3 * (uint64_t)38U;
}


int main() {
  cycles a,b;
  clock_t t1,t2;
  uint64_t count = ROUNDS;

  uint64_t bignum_a[5U] = { 197876, 241305, 245979, 490424, 284994 };
  uint64_t bignum_b[5U] = { 180879, 475851, 123829, 108058, 144159 };

  //  ---------------------------------------------------

  FStar_UInt128_uint128 tmp[10U];
  for (uint32_t _i = 0U; _i < (uint32_t)10U; ++_i)
    tmp[_i] = FStar_UInt128_uint64_to_uint128((uint64_t)0U);

 // Benchmarking for Hacl_Impl_Curve25519_Field51_fmul
  for (int j = 0; j < ROUNDS; j++) {
    //(out, f1, f2, tmp); tmp is unused
    Hacl_Impl_Curve25519_Field51_fmul(bignum_b, bignum_a, bignum_b, tmp);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Impl_Curve25519_Field51_fmul(bignum_b, bignum_a, bignum_b, tmp);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff3 = t2 - t1;
  uint64_t cyc3 = b - a;

 // Benchmarking for Hacl_Impl_Curve25519_Field51_fsqr
  for (int j = 0; j < ROUNDS; j++) {
    //(out, f, tmp); tmp is unused
    Hacl_Impl_Curve25519_Field51_fsqr(bignum_b, bignum_b, tmp);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Impl_Curve25519_Field51_fsqr(bignum_b, bignum_b, tmp);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff4 = t2 - t1;
  uint64_t cyc4 = b - a;

  bool b1 = bignum_b[1] == 2 ? 0 : 1;
  printf("b1 = %d\n", b1);

  printf("\n curve25519_fmul_51:\n");
  print_time(count,diff3,cyc3);
  printf("\n curve25519_fsqr_51:\n");
  print_time(count,diff4,cyc4);

  //-------------------------------------------
  uint64_t bignum_a4[4U] = { 197876, 241305, 245979, 490424 };
  uint64_t bignum_b4[4U] = { 180879, 475851, 123829, 108058 };
  uint64_t tmp4[16U] = { 0U };

 // Benchmarking for Curve25519_Field64_fmul
  for (int j = 0; j < ROUNDS; j++) {
    // (out, f1, f2, tmp)
    fmul(bignum_b4, bignum_a4, bignum_b4, tmp4);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    fmul(bignum_b4, bignum_a4, bignum_b4, tmp4);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff5 = t2 - t1;
  uint64_t cyc5 = b - a;

 // Benchmarking for Curve25519_Field64_fsqr
  for (int j = 0; j < ROUNDS; j++) {
    // (out, f, tmp)
    fsqr(bignum_b4, bignum_b4, tmp4);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    fsqr(bignum_b4, bignum_b4, tmp4);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff6 = t2 - t1;
  uint64_t cyc6 = b - a;

  bool b2 = bignum_b4[1] == 2 ? 0 : 1;
  printf("b2 = %d\n", b2);

  printf("\n curve25519_fmul_64 (inline asm curve25519-inline.h):\n");
  print_time(count,diff5,cyc5);
  printf("\n curve25519_fsqr_64 (inline asm curve25519-inline.h):\n");
  print_time(count,diff6,cyc6);


 // Benchmarking for Curve25519_Field64_fmul
  for (int j = 0; j < ROUNDS; j++) {
    // (tmp, f1, out, f2)
    fmul_e(tmp4, bignum_b4, bignum_b4, bignum_a4);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    fmul_e(tmp4, bignum_b4, bignum_b4, bignum_a4);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff7 = t2 - t1;
  uint64_t cyc7 = b - a;

 // Benchmarking for Curve25519_Field64_fsqr
  for (int j = 0; j < ROUNDS; j++) {
    // (tmp, f1, out)
    fsqr_e(tmp4, bignum_b4, bignum_b4);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    fsqr_e(tmp4, bignum_b4, bignum_b4);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff8 = t2 - t1;
  uint64_t cyc8 = b - a;

  bool b3 = bignum_b4[1] == 2 ? 0 : 1;
  printf("b3 = %d\n", b3);

  printf("\n curve25519_fmul_64 (asm .S):\n");
  print_time(count,diff7,cyc7);
  printf("\n curve25519_fsqr_64 (asm .S):\n");
  print_time(count,diff8,cyc8);

  //-------------------------------------------
  uint64_t tmp8[8U] = { 0U };

 // Benchmarking for Curve25519_Field64_Slow_fmul
  for (int j = 0; j < ROUNDS; j++) {
    // (out, f1, f2, tmp)
    fmul_(bignum_b4, bignum_a4, bignum_b4, tmp4);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    fmul_(bignum_b4, bignum_a4, bignum_b4, tmp4);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff9 = t2 - t1;
  uint64_t cyc9 = b - a;

 // Benchmarking for Curve25519_Field64_Slow_fsqr
  for (int j = 0; j < ROUNDS; j++) {
    // (out, f, tmp)
    fsqr_(bignum_b4, bignum_b4, tmp4);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    fsqr_(bignum_b4, bignum_b4, tmp4);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff10 = t2 - t1;
  uint64_t cyc10 = b - a;


  bool b4 = bignum_b4[1] == 2 ? 0 : 1;
  printf("b4 = %d\n", b4);

  printf("\n curve25519_fmul_64 (slow):\n");
  print_time(count,diff9,cyc9);
  printf("\n curve25519_fsqr_64 (slow):\n");
  print_time(count,diff10,cyc10);

  return EXIT_SUCCESS;
}
