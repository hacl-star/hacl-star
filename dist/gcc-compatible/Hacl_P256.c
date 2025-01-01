/* MIT License
 *
 * Copyright (c) 2016-2022 INRIA, CMU and Microsoft Corporation
 * Copyright (c) 2022-2023 HACL* Contributors
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#include "Hacl_P256.h"

#include "internal/Hacl_Krmllib.h"
#include "internal/Hacl_Bignum_Base.h"
#include "lib_intrinsics.h"

static inline uint64_t bn_is_eq_mask(uint64_t *x, uint64_t *y)
{
  uint64_t mask = 0xFFFFFFFFFFFFFFFFULL;
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t uu____0 = FStar_UInt64_eq_mask(x[i], y[i]);
    mask = uu____0 & mask;);
  uint64_t mask1 = mask;
  return mask1;
}

static inline void bn_cmovznz(uint64_t *a, uint64_t b, uint64_t *c, uint64_t *d)
{
  uint64_t mask = ~FStar_UInt64_eq_mask(b, 0ULL);
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = a;
    uint64_t uu____0 = c[i];
    uint64_t x = uu____0 ^ (mask & (d[i] ^ uu____0));
    os[i] = x;);
}

static inline void bn_add_mod(uint64_t *a, uint64_t *b, uint64_t *c, uint64_t *d)
{
  uint64_t c10 = 0ULL;
  {
    uint64_t t1 = c[4U * 0U];
    uint64_t t20 = d[4U * 0U];
    uint64_t *res_i0 = a + 4U * 0U;
    c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t1, t20, res_i0);
    uint64_t t10 = c[4U * 0U + 1U];
    uint64_t t21 = d[4U * 0U + 1U];
    uint64_t *res_i1 = a + 4U * 0U + 1U;
    c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t10, t21, res_i1);
    uint64_t t11 = c[4U * 0U + 2U];
    uint64_t t22 = d[4U * 0U + 2U];
    uint64_t *res_i2 = a + 4U * 0U + 2U;
    c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t11, t22, res_i2);
    uint64_t t12 = c[4U * 0U + 3U];
    uint64_t t2 = d[4U * 0U + 3U];
    uint64_t *res_i = a + 4U * 0U + 3U;
    c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t12, t2, res_i);
  }
  uint64_t c0 = c10;
  uint64_t tmp[4U] = { 0U };
  uint64_t c1 = 0ULL;
  {
    uint64_t t1 = a[4U * 0U];
    uint64_t t20 = b[4U * 0U];
    uint64_t *res_i0 = tmp + 4U * 0U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, res_i0);
    uint64_t t10 = a[4U * 0U + 1U];
    uint64_t t21 = b[4U * 0U + 1U];
    uint64_t *res_i1 = tmp + 4U * 0U + 1U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t10, t21, res_i1);
    uint64_t t11 = a[4U * 0U + 2U];
    uint64_t t22 = b[4U * 0U + 2U];
    uint64_t *res_i2 = tmp + 4U * 0U + 2U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t11, t22, res_i2);
    uint64_t t12 = a[4U * 0U + 3U];
    uint64_t t2 = b[4U * 0U + 3U];
    uint64_t *res_i = tmp + 4U * 0U + 3U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t12, t2, res_i);
  }
  uint64_t c11 = c1;
  uint64_t c2 = c0 - c11;
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = a;
    uint64_t x = (c2 & a[i]) | (~c2 & tmp[i]);
    os[i] = x;);
}

static inline uint64_t bn_sub(uint64_t *a, uint64_t *b, uint64_t *c)
{
  uint64_t c1 = 0ULL;
  {
    uint64_t t1 = b[4U * 0U];
    uint64_t t20 = c[4U * 0U];
    uint64_t *res_i0 = a + 4U * 0U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, res_i0);
    uint64_t t10 = b[4U * 0U + 1U];
    uint64_t t21 = c[4U * 0U + 1U];
    uint64_t *res_i1 = a + 4U * 0U + 1U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t10, t21, res_i1);
    uint64_t t11 = b[4U * 0U + 2U];
    uint64_t t22 = c[4U * 0U + 2U];
    uint64_t *res_i2 = a + 4U * 0U + 2U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t11, t22, res_i2);
    uint64_t t12 = b[4U * 0U + 3U];
    uint64_t t2 = c[4U * 0U + 3U];
    uint64_t *res_i = a + 4U * 0U + 3U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t12, t2, res_i);
  }
  uint64_t c10 = c1;
  return c10;
}

static inline void bn_sub_mod(uint64_t *a, uint64_t *b, uint64_t *c, uint64_t *d)
{
  uint64_t c10 = 0ULL;
  {
    uint64_t t1 = c[4U * 0U];
    uint64_t t20 = d[4U * 0U];
    uint64_t *res_i0 = a + 4U * 0U;
    c10 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c10, t1, t20, res_i0);
    uint64_t t10 = c[4U * 0U + 1U];
    uint64_t t21 = d[4U * 0U + 1U];
    uint64_t *res_i1 = a + 4U * 0U + 1U;
    c10 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c10, t10, t21, res_i1);
    uint64_t t11 = c[4U * 0U + 2U];
    uint64_t t22 = d[4U * 0U + 2U];
    uint64_t *res_i2 = a + 4U * 0U + 2U;
    c10 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c10, t11, t22, res_i2);
    uint64_t t12 = c[4U * 0U + 3U];
    uint64_t t2 = d[4U * 0U + 3U];
    uint64_t *res_i = a + 4U * 0U + 3U;
    c10 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c10, t12, t2, res_i);
  }
  uint64_t c0 = c10;
  uint64_t tmp[4U] = { 0U };
  uint64_t c1 = 0ULL;
  {
    uint64_t t1 = a[4U * 0U];
    uint64_t t20 = b[4U * 0U];
    uint64_t *res_i0 = tmp + 4U * 0U;
    c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t20, res_i0);
    uint64_t t10 = a[4U * 0U + 1U];
    uint64_t t21 = b[4U * 0U + 1U];
    uint64_t *res_i1 = tmp + 4U * 0U + 1U;
    c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t10, t21, res_i1);
    uint64_t t11 = a[4U * 0U + 2U];
    uint64_t t22 = b[4U * 0U + 2U];
    uint64_t *res_i2 = tmp + 4U * 0U + 2U;
    c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t11, t22, res_i2);
    uint64_t t12 = a[4U * 0U + 3U];
    uint64_t t2 = b[4U * 0U + 3U];
    uint64_t *res_i = tmp + 4U * 0U + 3U;
    c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t12, t2, res_i);
  }
  uint64_t c11 = c1;
  KRML_MAYBE_UNUSED_VAR(c11);
  uint64_t c2 = 0ULL - c0;
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = a;
    uint64_t x = (c2 & tmp[i]) | (~c2 & a[i]);
    os[i] = x;);
}

static inline void bn_mul(uint64_t *a, uint64_t *b, uint64_t *c)
{
  memset(a, 0U, 8U * sizeof (uint64_t));
  KRML_MAYBE_FOR4(i0,
    0U,
    4U,
    1U,
    uint64_t bj = c[i0];
    uint64_t *res_j = a + i0;
    uint64_t c1 = 0ULL;
    {
      uint64_t a_i = b[4U * 0U];
      uint64_t *res_i0 = res_j + 4U * 0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c1, res_i0);
      uint64_t a_i0 = b[4U * 0U + 1U];
      uint64_t *res_i1 = res_j + 4U * 0U + 1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c1, res_i1);
      uint64_t a_i1 = b[4U * 0U + 2U];
      uint64_t *res_i2 = res_j + 4U * 0U + 2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c1, res_i2);
      uint64_t a_i2 = b[4U * 0U + 3U];
      uint64_t *res_i = res_j + 4U * 0U + 3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c1, res_i);
    }
    uint64_t r = c1;
    a[4U + i0] = r;);
}

static inline void bn_sqr(uint64_t *a, uint64_t *b)
{
  memset(a, 0U, 8U * sizeof (uint64_t));
  KRML_MAYBE_FOR4(i0,
    0U,
    4U,
    1U,
    uint64_t *ab = b;
    uint64_t a_j = b[i0];
    uint64_t *res_j = a + i0;
    uint64_t c = 0ULL;
    for (uint32_t i = 0U; i < i0 / 4U; i++)
    {
      uint64_t a_i = ab[4U * i];
      uint64_t *res_i0 = res_j + 4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c, res_i0);
      uint64_t a_i0 = ab[4U * i + 1U];
      uint64_t *res_i1 = res_j + 4U * i + 1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, a_j, c, res_i1);
      uint64_t a_i1 = ab[4U * i + 2U];
      uint64_t *res_i2 = res_j + 4U * i + 2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, a_j, c, res_i2);
      uint64_t a_i2 = ab[4U * i + 3U];
      uint64_t *res_i = res_j + 4U * i + 3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, a_j, c, res_i);
    }
    for (uint32_t i = i0 / 4U * 4U; i < i0; i++)
    {
      uint64_t a_i = ab[i];
      uint64_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c, res_i);
    }
    uint64_t r = c;
    a[i0 + i0] = r;);
  uint64_t c0 = Hacl_Bignum_Addition_bn_add_eq_len_u64(8U, a, a, a);
  KRML_MAYBE_UNUSED_VAR(c0);
  uint64_t tmp[8U] = { 0U };
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    FStar_UInt128_uint128 res = FStar_UInt128_mul_wide(b[i], b[i]);
    uint64_t hi = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res, 64U));
    uint64_t lo = FStar_UInt128_uint128_to_uint64(res);
    tmp[2U * i] = lo;
    tmp[2U * i + 1U] = hi;);
  uint64_t c1 = Hacl_Bignum_Addition_bn_add_eq_len_u64(8U, a, tmp, a);
  KRML_MAYBE_UNUSED_VAR(c1);
}

static inline void bn_to_bytes_be(uint8_t *a, uint64_t *b)
{
  uint8_t tmp[32U] = { 0U };
  KRML_MAYBE_UNUSED_VAR(tmp);
  KRML_MAYBE_FOR4(i, 0U, 4U, 1U, store64_be(a + i * 8U, b[4U - i - 1U]););
}

static inline void bn_from_bytes_be(uint64_t *a, uint8_t *b)
{
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = a;
    uint64_t u = load64_be(b + (4U - i - 1U) * 8U);
    uint64_t x = u;
    os[i] = x;);
}

static inline void p256_make_prime(uint64_t *n)
{
  n[0U] = 0xffffffffffffffffULL;
  n[1U] = 0xffffffffULL;
  n[2U] = 0x0ULL;
  n[3U] = 0xffffffff00000001ULL;
}

static inline void p256_make_order(uint64_t *n)
{
  n[0U] = 0xf3b9cac2fc632551ULL;
  n[1U] = 0xbce6faada7179e84ULL;
  n[2U] = 0xffffffffffffffffULL;
  n[3U] = 0xffffffff00000000ULL;
}

static inline void p256_make_a_coeff(uint64_t *a)
{
  a[0U] = 0xfffffffffffffffcULL;
  a[1U] = 0x3ffffffffULL;
  a[2U] = 0x0ULL;
  a[3U] = 0xfffffffc00000004ULL;
}

static inline void p256_make_b_coeff(uint64_t *b)
{
  b[0U] = 0xd89cdf6229c4bddfULL;
  b[1U] = 0xacf005cd78843090ULL;
  b[2U] = 0xe5a220abf7212ed6ULL;
  b[3U] = 0xdc30061d04874834ULL;
}

static inline void p256_make_g_x(uint64_t *n)
{
  n[0U] = 0x79e730d418a9143cULL;
  n[1U] = 0x75ba95fc5fedb601ULL;
  n[2U] = 0x79fb732b77622510ULL;
  n[3U] = 0x18905f76a53755c6ULL;
}

static inline void p256_make_g_y(uint64_t *n)
{
  n[0U] = 0xddf25357ce95560aULL;
  n[1U] = 0x8b4ab8e4ba19e45cULL;
  n[2U] = 0xd2e88688dd21f325ULL;
  n[3U] = 0x8571ff1825885d85ULL;
}

static inline void p256_make_fmont_R2(uint64_t *n)
{
  n[0U] = 0x3ULL;
  n[1U] = 0xfffffffbffffffffULL;
  n[2U] = 0xfffffffffffffffeULL;
  n[3U] = 0x4fffffffdULL;
}

static inline void p256_make_fzero(uint64_t *n)
{
  n[0U] = 0ULL;
  n[1U] = 0ULL;
  n[2U] = 0ULL;
  n[3U] = 0ULL;
}

static inline void p256_make_fone(uint64_t *n)
{
  n[0U] = 0x1ULL;
  n[1U] = 0xffffffff00000000ULL;
  n[2U] = 0xffffffffffffffffULL;
  n[3U] = 0xfffffffeULL;
}

static inline void fmont_reduction(uint64_t *res, uint64_t *x)
{
  uint64_t n[4U] = { 0U };
  p256_make_prime(n);
  uint64_t c0 = 0ULL;
  KRML_MAYBE_FOR4(i0,
    0U,
    4U,
    1U,
    uint64_t qj = 1ULL * x[i0];
    uint64_t *res_j0 = x + i0;
    uint64_t c = 0ULL;
    {
      uint64_t a_i = n[4U * 0U];
      uint64_t *res_i0 = res_j0 + 4U * 0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c, res_i0);
      uint64_t a_i0 = n[4U * 0U + 1U];
      uint64_t *res_i1 = res_j0 + 4U * 0U + 1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, qj, c, res_i1);
      uint64_t a_i1 = n[4U * 0U + 2U];
      uint64_t *res_i2 = res_j0 + 4U * 0U + 2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, qj, c, res_i2);
      uint64_t a_i2 = n[4U * 0U + 3U];
      uint64_t *res_i = res_j0 + 4U * 0U + 3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, qj, c, res_i);
    }
    uint64_t r = c;
    uint64_t c1 = r;
    uint64_t *resb = x + 4U + i0;
    uint64_t res_j = x[4U + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c1, res_j, resb););
  memcpy(res, x + 4U, 4U * sizeof (uint64_t));
  uint64_t c00 = c0;
  uint64_t tmp[4U] = { 0U };
  uint64_t c = 0ULL;
  {
    uint64_t t1 = res[4U * 0U];
    uint64_t t20 = n[4U * 0U];
    uint64_t *res_i0 = tmp + 4U * 0U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = res[4U * 0U + 1U];
    uint64_t t21 = n[4U * 0U + 1U];
    uint64_t *res_i1 = tmp + 4U * 0U + 1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = res[4U * 0U + 2U];
    uint64_t t22 = n[4U * 0U + 2U];
    uint64_t *res_i2 = tmp + 4U * 0U + 2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = res[4U * 0U + 3U];
    uint64_t t2 = n[4U * 0U + 3U];
    uint64_t *res_i = tmp + 4U * 0U + 3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  uint64_t c1 = c;
  uint64_t c2 = c00 - c1;
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = res;
    uint64_t x1 = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x1;);
}

static inline void qmont_reduction(uint64_t *res, uint64_t *x)
{
  uint64_t n[4U] = { 0U };
  p256_make_order(n);
  uint64_t c0 = 0ULL;
  KRML_MAYBE_FOR4(i0,
    0U,
    4U,
    1U,
    uint64_t qj = 0xccd1c8aaee00bc4fULL * x[i0];
    uint64_t *res_j0 = x + i0;
    uint64_t c = 0ULL;
    {
      uint64_t a_i = n[4U * 0U];
      uint64_t *res_i0 = res_j0 + 4U * 0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c, res_i0);
      uint64_t a_i0 = n[4U * 0U + 1U];
      uint64_t *res_i1 = res_j0 + 4U * 0U + 1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, qj, c, res_i1);
      uint64_t a_i1 = n[4U * 0U + 2U];
      uint64_t *res_i2 = res_j0 + 4U * 0U + 2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, qj, c, res_i2);
      uint64_t a_i2 = n[4U * 0U + 3U];
      uint64_t *res_i = res_j0 + 4U * 0U + 3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, qj, c, res_i);
    }
    uint64_t r = c;
    uint64_t c1 = r;
    uint64_t *resb = x + 4U + i0;
    uint64_t res_j = x[4U + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c1, res_j, resb););
  memcpy(res, x + 4U, 4U * sizeof (uint64_t));
  uint64_t c00 = c0;
  uint64_t tmp[4U] = { 0U };
  uint64_t c = 0ULL;
  {
    uint64_t t1 = res[4U * 0U];
    uint64_t t20 = n[4U * 0U];
    uint64_t *res_i0 = tmp + 4U * 0U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = res[4U * 0U + 1U];
    uint64_t t21 = n[4U * 0U + 1U];
    uint64_t *res_i1 = tmp + 4U * 0U + 1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = res[4U * 0U + 2U];
    uint64_t t22 = n[4U * 0U + 2U];
    uint64_t *res_i2 = tmp + 4U * 0U + 2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = res[4U * 0U + 3U];
    uint64_t t2 = n[4U * 0U + 3U];
    uint64_t *res_i = tmp + 4U * 0U + 3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  uint64_t c1 = c;
  uint64_t c2 = c00 - c1;
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = res;
    uint64_t x1 = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x1;);
}

static inline uint64_t bn_is_lt_prime_mask(uint64_t *f)
{
  uint64_t tmp[4U] = { 0U };
  p256_make_prime(tmp);
  uint64_t c = bn_sub(tmp, f, tmp);
  return 0ULL - c;
}

static inline void fadd0(uint64_t *a, uint64_t *b, uint64_t *c)
{
  uint64_t n[4U] = { 0U };
  p256_make_prime(n);
  bn_add_mod(a, n, b, c);
}

static inline void fsub0(uint64_t *a, uint64_t *b, uint64_t *c)
{
  uint64_t n[4U] = { 0U };
  p256_make_prime(n);
  bn_sub_mod(a, n, b, c);
}

static inline void fmul0(uint64_t *a, uint64_t *b, uint64_t *c)
{
  uint64_t tmp[8U] = { 0U };
  bn_mul(tmp, b, c);
  fmont_reduction(a, tmp);
}

static inline void fsqr0(uint64_t *a, uint64_t *b)
{
  uint64_t tmp[8U] = { 0U };
  bn_sqr(tmp, b);
  fmont_reduction(a, tmp);
}

static inline void from_mont(uint64_t *a, uint64_t *b)
{
  uint64_t tmp[8U] = { 0U };
  memcpy(tmp, b, 4U * sizeof (uint64_t));
  fmont_reduction(a, tmp);
}

static inline void to_mont(uint64_t *a, uint64_t *b)
{
  uint64_t r2modn[4U] = { 0U };
  p256_make_fmont_R2(r2modn);
  uint64_t tmp[8U] = { 0U };
  bn_mul(tmp, b, r2modn);
  fmont_reduction(a, tmp);
}

static inline void p256_finv(uint64_t *res, uint64_t *a)
{
  uint64_t tmp[16U] = { 0U };
  uint64_t *x30 = tmp;
  uint64_t *x2 = tmp + 4U;
  uint64_t *tmp1 = tmp + 8U;
  uint64_t *tmp2 = tmp + 12U;
  memcpy(x2, a, 4U * sizeof (uint64_t));
  {
    fsqr0(x2, x2);
  }
  fmul0(x2, x2, a);
  memcpy(x30, x2, 4U * sizeof (uint64_t));
  {
    fsqr0(x30, x30);
  }
  fmul0(x30, x30, a);
  memcpy(tmp1, x30, 4U * sizeof (uint64_t));
  KRML_MAYBE_FOR3(i, 0U, 3U, 1U, fsqr0(tmp1, tmp1););
  fmul0(tmp1, tmp1, x30);
  memcpy(tmp2, tmp1, 4U * sizeof (uint64_t));
  KRML_MAYBE_FOR6(i, 0U, 6U, 1U, fsqr0(tmp2, tmp2););
  fmul0(tmp2, tmp2, tmp1);
  memcpy(tmp1, tmp2, 4U * sizeof (uint64_t));
  KRML_MAYBE_FOR3(i, 0U, 3U, 1U, fsqr0(tmp1, tmp1););
  fmul0(tmp1, tmp1, x30);
  memcpy(x30, tmp1, 4U * sizeof (uint64_t));
  KRML_MAYBE_FOR15(i, 0U, 15U, 1U, fsqr0(x30, x30););
  fmul0(x30, x30, tmp1);
  memcpy(tmp1, x30, 4U * sizeof (uint64_t));
  KRML_MAYBE_FOR2(i, 0U, 2U, 1U, fsqr0(tmp1, tmp1););
  fmul0(tmp1, tmp1, x2);
  memcpy(x2, tmp1, 4U * sizeof (uint64_t));
  for (uint32_t i = 0U; i < 32U; i++)
  {
    fsqr0(x2, x2);
  }
  fmul0(x2, x2, a);
  for (uint32_t i = 0U; i < 128U; i++)
  {
    fsqr0(x2, x2);
  }
  fmul0(x2, x2, tmp1);
  for (uint32_t i = 0U; i < 32U; i++)
  {
    fsqr0(x2, x2);
  }
  fmul0(x2, x2, tmp1);
  for (uint32_t i = 0U; i < 30U; i++)
  {
    fsqr0(x2, x2);
  }
  fmul0(x2, x2, x30);
  KRML_MAYBE_FOR2(i, 0U, 2U, 1U, fsqr0(x2, x2););
  fmul0(tmp1, x2, a);
  memcpy(res, tmp1, 4U * sizeof (uint64_t));
}

static inline void p256_fsqrt(uint64_t *res, uint64_t *a)
{
  uint64_t tmp[8U] = { 0U };
  uint64_t *tmp1 = tmp;
  uint64_t *tmp2 = tmp + 4U;
  memcpy(tmp1, a, 4U * sizeof (uint64_t));
  {
    fsqr0(tmp1, tmp1);
  }
  fmul0(tmp1, tmp1, a);
  memcpy(tmp2, tmp1, 4U * sizeof (uint64_t));
  KRML_MAYBE_FOR2(i, 0U, 2U, 1U, fsqr0(tmp2, tmp2););
  fmul0(tmp2, tmp2, tmp1);
  memcpy(tmp1, tmp2, 4U * sizeof (uint64_t));
  KRML_MAYBE_FOR4(i, 0U, 4U, 1U, fsqr0(tmp1, tmp1););
  fmul0(tmp1, tmp1, tmp2);
  memcpy(tmp2, tmp1, 4U * sizeof (uint64_t));
  KRML_MAYBE_FOR8(i, 0U, 8U, 1U, fsqr0(tmp2, tmp2););
  fmul0(tmp2, tmp2, tmp1);
  memcpy(tmp1, tmp2, 4U * sizeof (uint64_t));
  KRML_MAYBE_FOR16(i, 0U, 16U, 1U, fsqr0(tmp1, tmp1););
  fmul0(tmp1, tmp1, tmp2);
  memcpy(tmp2, tmp1, 4U * sizeof (uint64_t));
  for (uint32_t i = 0U; i < 32U; i++)
  {
    fsqr0(tmp2, tmp2);
  }
  fmul0(tmp2, tmp2, a);
  for (uint32_t i = 0U; i < 96U; i++)
  {
    fsqr0(tmp2, tmp2);
  }
  fmul0(tmp2, tmp2, a);
  for (uint32_t i = 0U; i < 94U; i++)
  {
    fsqr0(tmp2, tmp2);
  }
  memcpy(res, tmp2, 4U * sizeof (uint64_t));
}

static inline uint64_t load_qelem_conditional(uint64_t *a, uint8_t *b)
{
  bn_from_bytes_be(a, b);
  uint64_t tmp[4U] = { 0U };
  p256_make_order(tmp);
  uint64_t c = bn_sub(tmp, a, tmp);
  uint64_t is_lt_order = 0ULL - c;
  uint64_t bn_zero[4U] = { 0U };
  uint64_t res = bn_is_eq_mask(a, bn_zero);
  uint64_t is_eq_zero = res;
  uint64_t is_b_valid = is_lt_order & ~is_eq_zero;
  uint64_t oneq[4U] = { 0U };
  oneq[0U] = 1ULL;
  oneq[1U] = 0ULL;
  oneq[2U] = 0ULL;
  oneq[3U] = 0ULL;
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = a;
    uint64_t uu____0 = oneq[i];
    uint64_t x = uu____0 ^ (is_b_valid & (a[i] ^ uu____0));
    os[i] = x;);
  return is_b_valid;
}

static inline void qmod_short(uint64_t *a, uint64_t *b)
{
  uint64_t tmp[4U] = { 0U };
  p256_make_order(tmp);
  uint64_t c = bn_sub(tmp, b, tmp);
  bn_cmovznz(a, c, tmp, b);
}

static inline void qadd(uint64_t *a, uint64_t *b, uint64_t *c)
{
  uint64_t n[4U] = { 0U };
  p256_make_order(n);
  bn_add_mod(a, n, b, c);
}

static inline void from_qmont(uint64_t *a, uint64_t *b)
{
  uint64_t tmp[8U] = { 0U };
  memcpy(tmp, b, 4U * sizeof (uint64_t));
  qmont_reduction(a, tmp);
}

static inline void qmul(uint64_t *a, uint64_t *b, uint64_t *c)
{
  uint64_t tmp[8U] = { 0U };
  bn_mul(tmp, b, c);
  qmont_reduction(a, tmp);
}

static inline void qsqr(uint64_t *a, uint64_t *b)
{
  uint64_t tmp[8U] = { 0U };
  bn_sqr(tmp, b);
  qmont_reduction(a, tmp);
}

static inline void p256_qinv(uint64_t *res, uint64_t *r)
{
  uint64_t tmp[28U] = { 0U };
  uint64_t *x6 = tmp;
  uint64_t *x_11 = tmp + 4U;
  uint64_t *x_101 = tmp + 8U;
  uint64_t *x_111 = tmp + 12U;
  uint64_t *x_1111 = tmp + 16U;
  uint64_t *x_10101 = tmp + 20U;
  uint64_t *x_101111 = tmp + 24U;
  memcpy(x6, r, 4U * sizeof (uint64_t));
  {
    qsqr(x6, x6);
  }
  qmul(x_11, x6, r);
  qmul(x_101, x6, x_11);
  qmul(x_111, x6, x_101);
  memcpy(x6, x_101, 4U * sizeof (uint64_t));
  {
    qsqr(x6, x6);
  }
  qmul(x_1111, x_101, x6);
  {
    qsqr(x6, x6);
  }
  qmul(x_10101, x6, r);
  memcpy(x6, x_10101, 4U * sizeof (uint64_t));
  {
    qsqr(x6, x6);
  }
  qmul(x_101111, x_101, x6);
  qmul(x6, x_10101, x6);
  uint64_t tmp1[4U] = { 0U };
  KRML_MAYBE_FOR2(i, 0U, 2U, 1U, qsqr(x6, x6););
  qmul(x6, x6, x_11);
  memcpy(tmp1, x6, 4U * sizeof (uint64_t));
  KRML_MAYBE_FOR8(i, 0U, 8U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x6);
  memcpy(x6, tmp1, 4U * sizeof (uint64_t));
  KRML_MAYBE_FOR16(i, 0U, 16U, 1U, qsqr(x6, x6););
  qmul(x6, x6, tmp1);
  memcpy(tmp1, x6, 4U * sizeof (uint64_t));
  for (uint32_t i = 0U; i < 64U; i++)
  {
    qsqr(tmp1, tmp1);
  }
  qmul(tmp1, tmp1, x6);
  for (uint32_t i = 0U; i < 32U; i++)
  {
    qsqr(tmp1, tmp1);
  }
  qmul(tmp1, tmp1, x6);
  KRML_MAYBE_FOR6(i, 0U, 6U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_101111);
  KRML_MAYBE_FOR5(i, 0U, 5U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_111);
  KRML_MAYBE_FOR4(i, 0U, 4U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_11);
  KRML_MAYBE_FOR5(i, 0U, 5U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_1111);
  KRML_MAYBE_FOR5(i, 0U, 5U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_10101);
  KRML_MAYBE_FOR4(i, 0U, 4U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_101);
  KRML_MAYBE_FOR3(i, 0U, 3U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_101);
  KRML_MAYBE_FOR3(i, 0U, 3U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_101);
  KRML_MAYBE_FOR5(i, 0U, 5U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_111);
  KRML_MAYBE_FOR9(i, 0U, 9U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_101111);
  KRML_MAYBE_FOR6(i, 0U, 6U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_1111);
  KRML_MAYBE_FOR2(i, 0U, 2U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, r);
  KRML_MAYBE_FOR5(i, 0U, 5U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, r);
  KRML_MAYBE_FOR6(i, 0U, 6U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_1111);
  KRML_MAYBE_FOR5(i, 0U, 5U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_111);
  KRML_MAYBE_FOR4(i, 0U, 4U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_111);
  KRML_MAYBE_FOR5(i, 0U, 5U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_111);
  KRML_MAYBE_FOR5(i, 0U, 5U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_101);
  KRML_MAYBE_FOR3(i, 0U, 3U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_11);
  KRML_MAYBE_FOR10(i, 0U, 10U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_101111);
  KRML_MAYBE_FOR2(i, 0U, 2U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_11);
  KRML_MAYBE_FOR5(i, 0U, 5U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_11);
  KRML_MAYBE_FOR5(i, 0U, 5U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_11);
  KRML_MAYBE_FOR3(i, 0U, 3U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, r);
  KRML_MAYBE_FOR7(i, 0U, 7U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_10101);
  KRML_MAYBE_FOR6(i, 0U, 6U, 1U, qsqr(tmp1, tmp1););
  qmul(tmp1, tmp1, x_1111);
  memcpy(x6, tmp1, 4U * sizeof (uint64_t));
  memcpy(res, x6, 4U * sizeof (uint64_t));
}

static inline void point_add(uint64_t *x, uint64_t *y, uint64_t *xy)
{
  uint64_t tmp[36U] = { 0U };
  uint64_t *t0 = tmp;
  uint64_t *t1 = tmp + 24U;
  uint64_t *x3 = t1;
  uint64_t *y3 = t1 + 4U;
  uint64_t *z3 = t1 + 8U;
  uint64_t *t01 = t0;
  uint64_t *t11 = t0 + 4U;
  uint64_t *t2 = t0 + 8U;
  uint64_t *t3 = t0 + 12U;
  uint64_t *t4 = t0 + 16U;
  uint64_t *t5 = t0 + 20U;
  uint64_t *x1 = x;
  uint64_t *y1 = x + 4U;
  uint64_t *z10 = x + 8U;
  uint64_t *x20 = y;
  uint64_t *y20 = y + 4U;
  uint64_t *z20 = y + 8U;
  fmul0(t01, x1, x20);
  fmul0(t11, y1, y20);
  fmul0(t2, z10, z20);
  fadd0(t3, x1, y1);
  fadd0(t4, x20, y20);
  fmul0(t3, t3, t4);
  fadd0(t4, t01, t11);
  uint64_t *y10 = x + 4U;
  uint64_t *z11 = x + 8U;
  uint64_t *y2 = y + 4U;
  uint64_t *z21 = y + 8U;
  fsub0(t3, t3, t4);
  fadd0(t4, y10, z11);
  fadd0(t5, y2, z21);
  fmul0(t4, t4, t5);
  fadd0(t5, t11, t2);
  fsub0(t4, t4, t5);
  uint64_t *x10 = x;
  uint64_t *z1 = x + 8U;
  uint64_t *x2 = y;
  uint64_t *z2 = y + 8U;
  fadd0(x3, x10, z1);
  fadd0(y3, x2, z2);
  fmul0(x3, x3, y3);
  fadd0(y3, t01, t2);
  fsub0(y3, x3, y3);
  uint64_t b_coeff[4U] = { 0U };
  p256_make_b_coeff(b_coeff);
  fmul0(z3, b_coeff, t2);
  fsub0(x3, y3, z3);
  fadd0(z3, x3, x3);
  fadd0(x3, x3, z3);
  fsub0(z3, t11, x3);
  fadd0(x3, t11, x3);
  uint64_t b_coeff0[4U] = { 0U };
  p256_make_b_coeff(b_coeff0);
  fmul0(y3, b_coeff0, y3);
  fadd0(t11, t2, t2);
  fadd0(t2, t11, t2);
  fsub0(y3, y3, t2);
  fsub0(y3, y3, t01);
  fadd0(t11, y3, y3);
  fadd0(y3, t11, y3);
  fadd0(t11, t01, t01);
  fadd0(t01, t11, t01);
  fsub0(t01, t01, t2);
  fmul0(t11, t4, y3);
  fmul0(t2, t01, y3);
  fmul0(y3, x3, z3);
  fadd0(y3, y3, t2);
  fmul0(x3, t3, x3);
  fsub0(x3, x3, t11);
  fmul0(z3, t4, z3);
  fmul0(t11, t3, t01);
  fadd0(z3, z3, t11);
  memcpy(xy, t1, 12U * sizeof (uint64_t));
}

static inline void point_double(uint64_t *x, uint64_t *xx)
{
  uint64_t tmp[20U] = { 0U };
  uint64_t *x1 = x;
  uint64_t *z = x + 8U;
  uint64_t *x3 = xx;
  uint64_t *y3 = xx + 4U;
  uint64_t *z3 = xx + 8U;
  uint64_t *t0 = tmp;
  uint64_t *t1 = tmp + 4U;
  uint64_t *t2 = tmp + 8U;
  uint64_t *t3 = tmp + 12U;
  uint64_t *t4 = tmp + 16U;
  uint64_t *x2 = x;
  uint64_t *y = x + 4U;
  uint64_t *z1 = x + 8U;
  fsqr0(t0, x2);
  fsqr0(t1, y);
  fsqr0(t2, z1);
  fmul0(t3, x2, y);
  fadd0(t3, t3, t3);
  fmul0(t4, y, z1);
  fmul0(z3, x1, z);
  fadd0(z3, z3, z3);
  uint64_t b_coeff[4U] = { 0U };
  p256_make_b_coeff(b_coeff);
  fmul0(y3, b_coeff, t2);
  fsub0(y3, y3, z3);
  fadd0(x3, y3, y3);
  fadd0(y3, x3, y3);
  fsub0(x3, t1, y3);
  fadd0(y3, t1, y3);
  fmul0(y3, x3, y3);
  fmul0(x3, x3, t3);
  fadd0(t3, t2, t2);
  fadd0(t2, t2, t3);
  uint64_t b_coeff0[4U] = { 0U };
  p256_make_b_coeff(b_coeff0);
  fmul0(z3, b_coeff0, z3);
  fsub0(z3, z3, t2);
  fsub0(z3, z3, t0);
  fadd0(t3, z3, z3);
  fadd0(z3, z3, t3);
  fadd0(t3, t0, t0);
  fadd0(t0, t3, t0);
  fsub0(t0, t0, t2);
  fmul0(t0, t0, z3);
  fadd0(y3, y3, t0);
  fadd0(t0, t4, t4);
  fmul0(z3, t0, z3);
  fsub0(x3, x3, z3);
  fmul0(z3, t0, t1);
  fadd0(z3, z3, z3);
  fadd0(z3, z3, z3);
}

static inline void point_zero(uint64_t *one)
{
  uint64_t *x = one;
  uint64_t *y = one + 4U;
  uint64_t *z = one + 8U;
  p256_make_fzero(x);
  p256_make_fone(y);
  p256_make_fzero(z);
}

static const
uint64_t
p256_basepoint_table_w4[192U] =
  {
    0ULL, 0ULL, 0ULL, 0ULL, 1ULL, 18446744069414584320ULL, 18446744073709551615ULL, 4294967294ULL,
    0ULL, 0ULL, 0ULL, 0ULL, 8784043285714375740ULL, 8483257759279461889ULL, 8789745728267363600ULL,
    1770019616739251654ULL, 15992936863339206154ULL, 10037038012062884956ULL,
    15197544864945402661ULL, 9615747158586711429ULL, 1ULL, 18446744069414584320ULL,
    18446744073709551615ULL, 4294967294ULL, 10634854829044225757ULL, 351552716085025155ULL,
    10645315080955407736ULL, 3609262091244858135ULL, 15760741698986874125ULL,
    14936374388219697827ULL, 15751360096993017895ULL, 18012233706239762398ULL,
    1993877568177495041ULL, 10345888787846536528ULL, 7746511691117935375ULL,
    14517043990409914413ULL, 14122549297570634151ULL, 16934610359517083771ULL,
    5724511325497097418ULL, 8983432969107448705ULL, 2687429970334080245ULL, 16525396802810050288ULL,
    7602596488871585854ULL, 4813919589149203084ULL, 7680395813780804519ULL, 6687709583048023590ULL,
    18086445169104142027ULL, 9637814708330203929ULL, 14785108459960679090ULL,
    3838023279095023581ULL, 3555615526157830307ULL, 5177066488380472871ULL, 18218186719108038403ULL,
    16281556341699656105ULL, 1524227924561461191ULL, 4148060517641909597ULL, 2858290374115363433ULL,
    8942772026334130620ULL, 3034451298319885113ULL, 8447866036736640940ULL, 11204933433076256578ULL,
    18333595740249588297ULL, 8259597024804538246ULL, 9539734295777539786ULL, 9797290423046626413ULL,
    5777303437849646537ULL, 8739356909899132020ULL, 14815960973766782158ULL,
    15286581798204509801ULL, 17597362577777019682ULL, 13259283710820519742ULL,
    10501322996899164670ULL, 1221138904338319642ULL, 14586685489551951885ULL, 895326705426031212ULL,
    14398171728560617847ULL, 9592550823745097391ULL, 17240998489162206026ULL,
    8085479283308189196ULL, 14844657737893882826ULL, 15923425394150618234ULL,
    2997808084773249525ULL, 494323555453660587ULL, 1215695327517794764ULL, 9476207381098391690ULL,
    7480789678419122995ULL, 15212230329321082489ULL, 436189395349576388ULL, 17377474396456660834ULL,
    15237013929655017939ULL, 11444428846883781676ULL, 5112749694521428575ULL, 950829367509872073ULL,
    17665036182057559519ULL, 17205133339690002313ULL, 16233765170251334549ULL,
    10122775683257972591ULL, 3352514236455632420ULL, 9143148522359954691ULL, 601191684005658860ULL,
    13398772186646349998ULL, 15512696600132928431ULL, 9128416073728948653ULL,
    11233051033546138578ULL, 6769345682610122833ULL, 10823233224575054288ULL,
    9997725227559980175ULL, 6733425642852897415ULL, 16302206918151466066ULL, 1669330822143265921ULL,
    2661645605036546002ULL, 17182558479745802165ULL, 1165082692376932040ULL, 9470595929011488359ULL,
    6142147329285324932ULL, 4829075085998111287ULL, 10231370681107338930ULL, 9591876895322495239ULL,
    10316468561384076618ULL, 11592503647238064235ULL, 13395813606055179632ULL,
    511127033980815508ULL, 12434976573147649880ULL, 3425094795384359127ULL, 6816971736303023445ULL,
    15444670609021139344ULL, 9464349818322082360ULL, 16178216413042376883ULL,
    9595540370774317348ULL, 7229365182662875710ULL, 4601177649460012843ULL, 5455046447382487090ULL,
    10854066421606187521ULL, 15913416821879788071ULL, 2297365362023460173ULL,
    2603252216454941350ULL, 6768791943870490934ULL, 15705936687122754810ULL, 9537096567546600694ULL,
    17580538144855035062ULL, 4496542856965746638ULL, 8444341625922124942ULL,
    12191263903636183168ULL, 17427332907535974165ULL, 14307569739254103736ULL,
    13900598742063266169ULL, 7176996424355977650ULL, 5709008170379717479ULL,
    14471312052264549092ULL, 1464519909491759867ULL, 3328154641049602121ULL,
    13020349337171136774ULL, 2772166279972051938ULL, 10854476939425975292ULL,
    1967189930534630940ULL, 2802919076529341959ULL, 14792226094833519208ULL,
    14675640928566522177ULL, 14838974364643800837ULL, 17631460696099549980ULL,
    17434186275364935469ULL, 2665648200587705473ULL, 13202122464492564051ULL,
    7576287350918073341ULL, 2272206013910186424ULL, 14558761641743937843ULL, 5675729149929979729ULL,
    9043135187561613166ULL, 11750149293830589225ULL, 740555197954307911ULL, 9871738005087190699ULL,
    17178667634283502053ULL, 18046255991533013265ULL, 4458222096988430430ULL,
    8452427758526311627ULL, 13825286929656615266ULL, 13956286357198391218ULL,
    15875692916799995079ULL, 10634895319157013920ULL, 13230116118036304207ULL,
    8795317393614625606ULL, 7001710806858862020ULL, 7949746088586183478ULL, 14677556044923602317ULL,
    11184023437485843904ULL, 11215864722023085094ULL, 6444464081471519014ULL,
    1706241174022415217ULL, 8243975633057550613ULL, 15502902453836085864ULL, 3799182188594003953ULL,
    3538840175098724094ULL
  };

static const
uint64_t
p256_g_pow2_64_table_w4[192U] =
  {
    0ULL, 0ULL, 0ULL, 0ULL, 1ULL, 18446744069414584320ULL, 18446744073709551615ULL, 4294967294ULL,
    0ULL, 0ULL, 0ULL, 0ULL, 1499621593102562565ULL, 16692369783039433128ULL,
    15337520135922861848ULL, 5455737214495366228ULL, 17827017231032529600ULL,
    12413621606240782649ULL, 2290483008028286132ULL, 15752017553340844820ULL,
    4846430910634234874ULL, 10861682798464583253ULL, 15404737222404363049ULL, 363586619281562022ULL,
    9866710912401645115ULL, 1162548847543228595ULL, 7649967190445130486ULL, 5212340432230915749ULL,
    7572620550182916491ULL, 14876145112448665096ULL, 2063227348838176167ULL, 3519435548295415847ULL,
    8390400282019023103ULL, 17666843593163037841ULL, 9450204148816496323ULL, 8483374507652916768ULL,
    6254661047265818424ULL, 16382127809582285023ULL, 125359443771153172ULL, 1374336701588437897ULL,
    11362596098420127726ULL, 2101654420738681387ULL, 12772780342444840510ULL,
    12546934328908550060ULL, 8331880412333790397ULL, 11687262051473819904ULL,
    8926848496503457587ULL, 9603974142010467857ULL, 13199952163826973175ULL, 2189856264898797734ULL,
    11356074861870267226ULL, 2027714896422561895ULL, 5261606367808050149ULL, 153855954337762312ULL,
    6375919692894573986ULL, 12364041207536146533ULL, 1891896010455057160ULL, 1568123795087313171ULL,
    18138710056556660101ULL, 6004886947510047736ULL, 4811859325589542932ULL, 3618763430148954981ULL,
    11434521746258554122ULL, 10086341535864049427ULL, 8073421629570399570ULL,
    12680586148814729338ULL, 9619958020761569612ULL, 15827203580658384478ULL,
    12832694810937550406ULL, 14977975484447400910ULL, 5478002389061063653ULL,
    14731136312639060880ULL, 4317867687275472033ULL, 6642650962855259884ULL, 2514254944289495285ULL,
    14231405641534478436ULL, 4045448346091518946ULL, 8985477013445972471ULL, 8869039454457032149ULL,
    4356978486208692970ULL, 10805288613335538577ULL, 12832353127812502042ULL,
    4576590051676547490ULL, 6728053735138655107ULL, 17814206719173206184ULL, 79790138573994940ULL,
    17920293215101822267ULL, 13422026625585728864ULL, 5018058010492547271ULL, 110232326023384102ULL,
    10834264070056942976ULL, 15222249086119088588ULL, 15119439519142044997ULL,
    11655511970063167313ULL, 1614477029450566107ULL, 3619322817271059794ULL, 9352862040415412867ULL,
    14017522553242747074ULL, 13138513643674040327ULL, 3610195242889455765ULL,
    8371069193996567291ULL, 12670227996544662654ULL, 1205961025092146303ULL,
    13106709934003962112ULL, 4350113471327723407ULL, 15060941403739680459ULL,
    13639127647823205030ULL, 10790943339357725715ULL, 498760574280648264ULL,
    17922071907832082887ULL, 15122670976670152145ULL, 6275027991110214322ULL,
    7250912847491816402ULL, 15206617260142982380ULL, 3385668313694152877ULL,
    17522479771766801905ULL, 2965919117476170655ULL, 1553238516603269404ULL, 5820770015631050991ULL,
    4999445222232605348ULL, 9245650860833717444ULL, 1508811811724230728ULL, 5190684913765614385ULL,
    15692927070934536166ULL, 12981978499190500902ULL, 5143491963193394698ULL,
    7705698092144084129ULL, 581120653055084783ULL, 13886552864486459714ULL, 6290301270652587255ULL,
    8663431529954393128ULL, 17033405846475472443ULL, 5206780355442651635ULL,
    12580364474736467688ULL, 17934601912005283310ULL, 15119491731028933652ULL,
    17848231399859044858ULL, 4427673319524919329ULL, 2673607337074368008ULL,
    14034876464294699949ULL, 10938948975420813697ULL, 15202340615298669183ULL,
    5496603454069431071ULL, 2486526142064906845ULL, 4507882119510526802ULL, 13888151172411390059ULL,
    15049027856908071726ULL, 9667231543181973158ULL, 6406671575277563202ULL, 3395801050331215139ULL,
    9813607433539108308ULL, 2681417728820980381ULL, 18407064643927113994ULL, 7707177692113485527ULL,
    14218149384635317074ULL, 3658668346206375919ULL, 15404713991002362166ULL,
    10152074687696195207ULL, 10926946599582128139ULL, 16907298600007085320ULL,
    16544287219664720279ULL, 11007075933432813205ULL, 8652245965145713599ULL,
    7857626748965990384ULL, 5602306604520095870ULL, 2525139243938658618ULL, 14405696176872077447ULL,
    18432270482137885332ULL, 9913880809120071177ULL, 16896141737831216972ULL,
    7484791498211214829ULL, 15635259968266497469ULL, 8495118537612215624ULL, 4915477980562575356ULL,
    16453519279754924350ULL, 14462108244565406969ULL, 14837837755237096687ULL,
    14130171078892575346ULL, 15423793222528491497ULL, 5460399262075036084ULL,
    16085440580308415349ULL, 26873200736954488ULL, 5603655807457499550ULL, 3342202915871129617ULL,
    1604413932150236626ULL, 9684226585089458974ULL, 1213229904006618539ULL, 6782978662408837236ULL,
    11197029877749307372ULL, 14085968786551657744ULL, 17352273610494009342ULL,
    7876582961192434984ULL
  };

static const
uint64_t
p256_g_pow2_128_table_w4[192U] =
  {
    0ULL, 0ULL, 0ULL, 0ULL, 1ULL, 18446744069414584320ULL, 18446744073709551615ULL, 4294967294ULL,
    0ULL, 0ULL, 0ULL, 0ULL, 14619254753077084366ULL, 13913835116514008593ULL,
    15060744674088488145ULL, 17668414598203068685ULL, 10761169236902342334ULL,
    15467027479157446221ULL, 14989185522423469618ULL, 14354539272510107003ULL,
    14298211796392133693ULL, 13270323784253711450ULL, 13380964971965046957ULL,
    8686204248456909699ULL, 17434630286744937066ULL, 1355903775279084720ULL, 7554695053550308662ULL,
    11354971222741863570ULL, 564601613420749879ULL, 8466325837259054896ULL, 10752965181772434263ULL,
    11405876547368426319ULL, 13791894568738930940ULL, 8230587134406354675ULL,
    12415514098722758608ULL, 18414183046995786744ULL, 15508000368227372870ULL,
    5781062464627999307ULL, 15339429052219195590ULL, 16038703753810741903ULL,
    9587718938298980714ULL, 4822658817952386407ULL, 1376351024833260660ULL, 1120174910554766702ULL,
    1730170933262569274ULL, 5187428548444533500ULL, 16242053503368957131ULL, 3036811119519868279ULL,
    1760267587958926638ULL, 170244572981065185ULL, 8063080791967388171ULL, 4824892826607692737ULL,
    16286391083472040552ULL, 11945158615253358747ULL, 14096887760410224200ULL,
    1613720831904557039ULL, 14316966673761197523ULL, 17411006201485445341ULL,
    8112301506943158801ULL, 2069889233927989984ULL, 10082848378277483927ULL, 3609691194454404430ULL,
    6110437205371933689ULL, 9769135977342231601ULL, 11977962151783386478ULL,
    18088718692559983573ULL, 11741637975753055ULL, 11110390325701582190ULL, 1341402251566067019ULL,
    3028229550849726478ULL, 10438984083997451310ULL, 12730851885100145709ULL,
    11524169532089894189ULL, 4523375903229602674ULL, 2028602258037385622ULL,
    17082839063089388410ULL, 6103921364634113167ULL, 17066180888225306102ULL,
    11395680486707876195ULL, 10952892272443345484ULL, 8792831960605859401ULL,
    14194485427742325139ULL, 15146020821144305250ULL, 1654766014957123343ULL,
    7955526243090948551ULL, 3989277566080493308ULL, 12229385116397931231ULL,
    13430548930727025562ULL, 3434892688179800602ULL, 8431998794645622027ULL,
    12132530981596299272ULL, 2289461608863966999ULL, 18345870950201487179ULL,
    13517947207801901576ULL, 5213113244172561159ULL, 17632986594098340879ULL,
    4405251818133148856ULL, 11783009269435447793ULL, 9332138983770046035ULL,
    12863411548922539505ULL, 3717030292816178224ULL, 10026078446427137374ULL,
    11167295326594317220ULL, 12425328773141588668ULL, 5760335125172049352ULL,
    9016843701117277863ULL, 5657892835694680172ULL, 11025130589305387464ULL, 1368484957977406173ULL,
    17361351345281258834ULL, 1907113641956152700ULL, 16439233413531427752ULL,
    5893322296986588932ULL, 14000206906171746627ULL, 14979266987545792900ULL,
    6926291766898221120ULL, 7162023296083360752ULL, 14762747553625382529ULL,
    12610831658612406849ULL, 10462926899548715515ULL, 4794017723140405312ULL,
    5234438200490163319ULL, 8019519110339576320ULL, 7194604241290530100ULL, 12626770134810813246ULL,
    10793074474236419890ULL, 11323224347913978783ULL, 16831128015895380245ULL,
    18323094195124693378ULL, 2361097165281567692ULL, 15755578675014279498ULL,
    14289876470325854580ULL, 12856787656093616839ULL, 3578928531243900594ULL,
    3847532758790503699ULL, 8377953190224748743ULL, 3314546646092744596ULL, 800810188859334358ULL,
    4626344124229343596ULL, 6620381605850876621ULL, 11422073570955989527ULL,
    12676813626484814469ULL, 16725029886764122240ULL, 16648497372773830008ULL,
    9135702594931291048ULL, 16080949688826680333ULL, 11528096561346602947ULL,
    2632498067099740984ULL, 11583842699108800714ULL, 8378404864573610526ULL, 1076560261627788534ULL,
    13836015994325032828ULL, 11234295937817067909ULL, 5893659808396722708ULL,
    11277421142886984364ULL, 8968549037166726491ULL, 14841374331394032822ULL,
    9967344773947889341ULL, 8799244393578496085ULL, 5094686877301601410ULL, 8780316747074726862ULL,
    9119697306829835718ULL, 15381243327921855368ULL, 2686250164449435196ULL,
    16466917280442198358ULL, 13791704489163125216ULL, 16955859337117924272ULL,
    17112836394923783642ULL, 4639176427338618063ULL, 16770029310141094964ULL,
    11049953922966416185ULL, 12012669590884098968ULL, 4859326885929417214ULL, 896380084392586061ULL,
    7153028362977034008ULL, 10540021163316263301ULL, 9318277998512936585ULL,
    18344496977694796523ULL, 11374737400567645494ULL, 17158800051138212954ULL,
    18343197867863253153ULL, 18204799297967861226ULL, 15798973531606348828ULL,
    9870158263408310459ULL, 17578869832774612627ULL, 8395748875822696932ULL,
    15310679007370670872ULL, 11205576736030808860ULL, 10123429210002838967ULL,
    5910544144088393959ULL, 14016615653353687369ULL, 11191676704772957822ULL
  };

static const
uint64_t
p256_g_pow2_192_table_w4[192U] =
  {
    0ULL, 0ULL, 0ULL, 0ULL, 1ULL, 18446744069414584320ULL, 18446744073709551615ULL, 4294967294ULL,
    0ULL, 0ULL, 0ULL, 0ULL, 7870395003430845958ULL, 18001862936410067720ULL, 8006461232116967215ULL,
    5921313779532424762ULL, 10702113371959864307ULL, 8070517410642379879ULL, 7139806720777708306ULL,
    8253938546650739833ULL, 17490482834545705718ULL, 1065249776797037500ULL, 5018258455937968775ULL,
    14100621120178668337ULL, 8392845221328116213ULL, 14630296398338540788ULL,
    4268947906723414372ULL, 9231207002243517909ULL, 14261219637616504262ULL, 7786881626982345356ULL,
    11412720751765882139ULL, 14119585051365330009ULL, 15281626286521302128ULL,
    6350171933454266732ULL, 16559468304937127866ULL, 13200760478271693417ULL,
    6733381546280350776ULL, 3801404890075189193ULL, 2741036364686993903ULL, 3218612940540174008ULL,
    10894914335165419505ULL, 11862941430149998362ULL, 4223151729402839584ULL,
    2913215088487087887ULL, 14562168920104952953ULL, 2170089393468287453ULL,
    10520900655016579352ULL, 7040362608949989273ULL, 8376510559381705307ULL, 9142237200448131532ULL,
    5696859948123854080ULL, 925422306716081180ULL, 11155545953469186421ULL, 1888208646862572812ULL,
    11151095998248845721ULL, 15793503271680275267ULL, 7729877044494854851ULL,
    6235134673193032913ULL, 7364280682182401564ULL, 5479679373325519985ULL, 17966037684582301763ULL,
    14140891609330279185ULL, 5814744449740463867ULL, 5652588426712591652ULL, 774745682988690912ULL,
    13228255573220500373ULL, 11949122068786859397ULL, 8021166392900770376ULL,
    7994323710948720063ULL, 9924618472877849977ULL, 17618517523141194266ULL, 2750424097794401714ULL,
    15481749570715253207ULL, 14646964509921760497ULL, 1037442848094301355ULL,
    6295995947389299132ULL, 16915049722317579514ULL, 10493877400992990313ULL,
    18391008753060553521ULL, 483942209623707598ULL, 2017775662838016613ULL, 5933251998459363553ULL,
    11789135019970707407ULL, 5484123723153268336ULL, 13246954648848484954ULL,
    4774374393926023505ULL, 14863995618704457336ULL, 13220153167104973625ULL,
    5988445485312390826ULL, 17580359464028944682ULL, 7297100131969874771ULL, 379931507867989375ULL,
    10927113096513421444ULL, 17688881974428340857ULL, 4259872578781463333ULL,
    8573076295966784472ULL, 16389829450727275032ULL, 1667243868963568259ULL,
    17730726848925960919ULL, 11408899874569778008ULL, 3576527582023272268ULL,
    16492920640224231656ULL, 7906130545972460130ULL, 13878604278207681266ULL, 41446695125652041ULL,
    8891615271337333503ULL, 2594537723613594470ULL, 7699579176995770924ULL, 147458463055730655ULL,
    12120406862739088406ULL, 12044892493010567063ULL, 8554076749615475136ULL,
    1005097692260929999ULL, 2687202654471188715ULL, 9457588752176879209ULL, 17472884880062444019ULL,
    9792097892056020166ULL, 2525246678512797150ULL, 15958903035313115662ULL,
    11336038170342247032ULL, 11560342382835141123ULL, 6212009033479929024ULL,
    8214308203775021229ULL, 8475469210070503698ULL, 13287024123485719563ULL,
    12956951963817520723ULL, 10693035819908470465ULL, 11375478788224786725ULL,
    16934625208487120398ULL, 10094585729115874495ULL, 2763884524395905776ULL,
    13535890148969964883ULL, 13514657411765064358ULL, 9903074440788027562ULL,
    17324720726421199990ULL, 2273931039117368789ULL, 3442641041506157854ULL, 1119853641236409612ULL,
    12037070344296077989ULL, 581736433335671746ULL, 6019150647054369174ULL, 14864096138068789375ULL,
    6652995210998318662ULL, 12773883697029175304ULL, 12751275631451845119ULL,
    11449095003038250478ULL, 1025805267334366480ULL, 2764432500300815015ULL,
    18274564429002844381ULL, 10445634195592600351ULL, 11814099592837202735ULL,
    5006796893679120289ULL, 6908397253997261914ULL, 13266696965302879279ULL, 7768715053015037430ULL,
    3569923738654785686ULL, 5844853453464857549ULL, 1837340805629559110ULL, 1034657624388283114ULL,
    711244516069456460ULL, 12519286026957934814ULL, 2613464944620837619ULL, 10003023321338286213ULL,
    7291332092642881376ULL, 9832199564117004897ULL, 3280736694860799890ULL, 6416452202849179874ULL,
    7326961381798642069ULL, 8435688798040635029ULL, 16630141263910982958ULL,
    17222635514422533318ULL, 9482787389178881499ULL, 836561194658263905ULL, 3405319043337616649ULL,
    2786146577568026518ULL, 7625483685691626321ULL, 6728084875304656716ULL, 1140997959232544268ULL,
    12847384827606303792ULL, 1719121337754572070ULL, 12863589482936438532ULL,
    3880712899640530862ULL, 2748456882813671564ULL, 4775988900044623019ULL, 8937847374382191162ULL,
    3767367347172252295ULL, 13468672401049388646ULL, 14359032216842397576ULL,
    2002555958685443975ULL, 16488678606651526810ULL, 11826135409597474760ULL,
    15296495673182508601ULL
  };

static const
uint64_t
p256_basepoint_table_w5[384U] =
  {
    0ULL, 0ULL, 0ULL, 0ULL, 1ULL, 18446744069414584320ULL, 18446744073709551615ULL, 4294967294ULL,
    0ULL, 0ULL, 0ULL, 0ULL, 8784043285714375740ULL, 8483257759279461889ULL, 8789745728267363600ULL,
    1770019616739251654ULL, 15992936863339206154ULL, 10037038012062884956ULL,
    15197544864945402661ULL, 9615747158586711429ULL, 1ULL, 18446744069414584320ULL,
    18446744073709551615ULL, 4294967294ULL, 10634854829044225757ULL, 351552716085025155ULL,
    10645315080955407736ULL, 3609262091244858135ULL, 15760741698986874125ULL,
    14936374388219697827ULL, 15751360096993017895ULL, 18012233706239762398ULL,
    1993877568177495041ULL, 10345888787846536528ULL, 7746511691117935375ULL,
    14517043990409914413ULL, 14122549297570634151ULL, 16934610359517083771ULL,
    5724511325497097418ULL, 8983432969107448705ULL, 2687429970334080245ULL, 16525396802810050288ULL,
    7602596488871585854ULL, 4813919589149203084ULL, 7680395813780804519ULL, 6687709583048023590ULL,
    18086445169104142027ULL, 9637814708330203929ULL, 14785108459960679090ULL,
    3838023279095023581ULL, 3555615526157830307ULL, 5177066488380472871ULL, 18218186719108038403ULL,
    16281556341699656105ULL, 1524227924561461191ULL, 4148060517641909597ULL, 2858290374115363433ULL,
    8942772026334130620ULL, 3034451298319885113ULL, 8447866036736640940ULL, 11204933433076256578ULL,
    18333595740249588297ULL, 8259597024804538246ULL, 9539734295777539786ULL, 9797290423046626413ULL,
    5777303437849646537ULL, 8739356909899132020ULL, 14815960973766782158ULL,
    15286581798204509801ULL, 17597362577777019682ULL, 13259283710820519742ULL,
    10501322996899164670ULL, 1221138904338319642ULL, 14586685489551951885ULL, 895326705426031212ULL,
    14398171728560617847ULL, 9592550823745097391ULL, 17240998489162206026ULL,
    8085479283308189196ULL, 14844657737893882826ULL, 15923425394150618234ULL,
    2997808084773249525ULL, 494323555453660587ULL, 1215695327517794764ULL, 9476207381098391690ULL,
    7480789678419122995ULL, 15212230329321082489ULL, 436189395349576388ULL, 17377474396456660834ULL,
    15237013929655017939ULL, 11444428846883781676ULL, 5112749694521428575ULL, 950829367509872073ULL,
    17665036182057559519ULL, 17205133339690002313ULL, 16233765170251334549ULL,
    10122775683257972591ULL, 3352514236455632420ULL, 9143148522359954691ULL, 601191684005658860ULL,
    13398772186646349998ULL, 15512696600132928431ULL, 9128416073728948653ULL,
    11233051033546138578ULL, 6769345682610122833ULL, 10823233224575054288ULL,
    9997725227559980175ULL, 6733425642852897415ULL, 16302206918151466066ULL, 1669330822143265921ULL,
    2661645605036546002ULL, 17182558479745802165ULL, 1165082692376932040ULL, 9470595929011488359ULL,
    6142147329285324932ULL, 4829075085998111287ULL, 10231370681107338930ULL, 9591876895322495239ULL,
    10316468561384076618ULL, 11592503647238064235ULL, 13395813606055179632ULL,
    511127033980815508ULL, 12434976573147649880ULL, 3425094795384359127ULL, 6816971736303023445ULL,
    15444670609021139344ULL, 9464349818322082360ULL, 16178216413042376883ULL,
    9595540370774317348ULL, 7229365182662875710ULL, 4601177649460012843ULL, 5455046447382487090ULL,
    10854066421606187521ULL, 15913416821879788071ULL, 2297365362023460173ULL,
    2603252216454941350ULL, 6768791943870490934ULL, 15705936687122754810ULL, 9537096567546600694ULL,
    17580538144855035062ULL, 4496542856965746638ULL, 8444341625922124942ULL,
    12191263903636183168ULL, 17427332907535974165ULL, 14307569739254103736ULL,
    13900598742063266169ULL, 7176996424355977650ULL, 5709008170379717479ULL,
    14471312052264549092ULL, 1464519909491759867ULL, 3328154641049602121ULL,
    13020349337171136774ULL, 2772166279972051938ULL, 10854476939425975292ULL,
    1967189930534630940ULL, 2802919076529341959ULL, 14792226094833519208ULL,
    14675640928566522177ULL, 14838974364643800837ULL, 17631460696099549980ULL,
    17434186275364935469ULL, 2665648200587705473ULL, 13202122464492564051ULL,
    7576287350918073341ULL, 2272206013910186424ULL, 14558761641743937843ULL, 5675729149929979729ULL,
    9043135187561613166ULL, 11750149293830589225ULL, 740555197954307911ULL, 9871738005087190699ULL,
    17178667634283502053ULL, 18046255991533013265ULL, 4458222096988430430ULL,
    8452427758526311627ULL, 13825286929656615266ULL, 13956286357198391218ULL,
    15875692916799995079ULL, 10634895319157013920ULL, 13230116118036304207ULL,
    8795317393614625606ULL, 7001710806858862020ULL, 7949746088586183478ULL, 14677556044923602317ULL,
    11184023437485843904ULL, 11215864722023085094ULL, 6444464081471519014ULL,
    1706241174022415217ULL, 8243975633057550613ULL, 15502902453836085864ULL, 3799182188594003953ULL,
    3538840175098724094ULL, 13240193491554624643ULL, 12365034249541329920ULL,
    2924326828590977357ULL, 5687195797140589099ULL, 16880427227292834531ULL, 9691471435758991112ULL,
    16642385273732487288ULL, 12173806747523009914ULL, 13142722756877876849ULL,
    8370377548305121979ULL, 17988526053752025426ULL, 4818750752684100334ULL, 5669241919350361655ULL,
    4964810303238518540ULL, 16709712747671533191ULL, 4461414404267448242ULL, 3971798785139504238ULL,
    6276818948740422136ULL, 1426735892164275762ULL, 7943622674892418919ULL, 9864274225563929680ULL,
    57815533745003233ULL, 10893588105168960233ULL, 15739162732907069535ULL, 3923866849462073470ULL,
    12279826158399226875ULL, 1533015761334846582ULL, 15860156818568437510ULL,
    8252625373831297988ULL, 9666953804812706358ULL, 8767785238646914634ULL, 14382179044941403551ULL,
    10401039907264254245ULL, 8584860003763157350ULL, 3120462679504470266ULL, 8670255778748340069ULL,
    5313789577940369984ULL, 16977072364454789224ULL, 12199578693972188324ULL,
    18211098771672599237ULL, 12868831556008795030ULL, 5310155061431048194ULL,
    18114153238435112606ULL, 14482365809278304512ULL, 12520721662723001511ULL,
    405943624021143002ULL, 8146944101507657423ULL, 181739317780393495ULL, 81743892273670099ULL,
    14759561962550473930ULL, 4592623849546992939ULL, 6916440441743449719ULL, 1304610503530809833ULL,
    5464930909232486441ULL, 15414883617496224671ULL, 8129283345256790ULL, 18294252198413739489ULL,
    17394115281884857288ULL, 7808348415224731235ULL, 13195566655747230608ULL,
    8568194219353949094ULL, 15329813048672122440ULL, 9604275495885785744ULL, 1577712551205219835ULL,
    15964209008022052790ULL, 15087297920782098160ULL, 3946031512438511898ULL,
    10050061168984440631ULL, 11382452014533138316ULL, 6313670788911952792ULL,
    12015989229696164014ULL, 5946702628076168852ULL, 5219995658774362841ULL,
    12230141881068377972ULL, 12361195202673441956ULL, 4732862275653856711ULL,
    17221430380805252370ULL, 15397525953897375810ULL, 16557437297239563045ULL,
    10101683801868971351ULL, 1402611372245592868ULL, 1931806383735563658ULL,
    10991705207471512479ULL, 861333583207471392ULL, 15207766844626322355ULL, 9224628129811432393ULL,
    3497069567089055613ULL, 11956632757898590316ULL, 8733729372586312960ULL,
    18091521051714930927ULL, 77582787724373283ULL, 9922437373519669237ULL, 3079321456325704615ULL,
    12171198408512478457ULL, 17179130884012147596ULL, 6839115479620367181ULL,
    4421032569964105406ULL, 10353331468657256053ULL, 17400988720335968824ULL,
    17138855889417480540ULL, 4507980080381370611ULL, 10703175719793781886ULL,
    12598516658725890426ULL, 8353463412173898932ULL, 17703029389228422404ULL,
    9313111267107226233ULL, 5441322942995154196ULL, 8952817660034465484ULL, 17571113341183703118ULL,
    7375087953801067019ULL, 13381466302076453648ULL, 3218165271423914596ULL,
    16956372157249382685ULL, 509080090049418841ULL, 13374233893294084913ULL, 2988537624204297086ULL,
    4979195832939384620ULL, 3803931594068976394ULL, 10731535883829627646ULL,
    12954845047607194278ULL, 10494298062560667399ULL, 4967351022190213065ULL,
    13391917938145756456ULL, 951370484866918160ULL, 13531334179067685307ULL,
    12868421357919390599ULL, 15918857042998130258ULL, 17769743831936974016ULL,
    7137921979260368809ULL, 12461369180685892062ULL, 827476514081935199ULL, 15107282134224767230ULL,
    10084765752802805748ULL, 3303739059392464407ULL, 17859532612136591428ULL,
    10949414770405040164ULL, 12838613589371008785ULL, 5554397169231540728ULL,
    18375114572169624408ULL, 15649286703242390139ULL, 2957281557463706877ULL,
    14000350446219393213ULL, 14355199721749620351ULL, 2730856240099299695ULL,
    17528131000714705752ULL, 2537498525883536360ULL, 6121058967084509393ULL,
    16897667060435514221ULL, 12367869599571112440ULL, 3388831797050807508ULL,
    16791449724090982798ULL, 2673426123453294928ULL, 11369313542384405846ULL,
    15641960333586432634ULL, 15080962589658958379ULL, 7747943772340226569ULL,
    8075023376199159152ULL, 8485093027378306528ULL, 13503706844122243648ULL, 8401961362938086226ULL,
    8125426002124226402ULL, 9005399361407785203ULL, 6847968030066906634ULL, 11934937736309295197ULL,
    5116750888594772351ULL, 2817039227179245227ULL, 17724206901239332980ULL, 4985702708254058578ULL,
    5786345435756642871ULL, 17772527414940936938ULL, 1201320251272957006ULL,
    15787430120324348129ULL, 6305488781359965661ULL, 12423900845502858433ULL,
    17485949424202277720ULL, 2062237315546855852ULL, 10353639467860902375ULL,
    2315398490451287299ULL, 15394572894814882621ULL, 232866113801165640ULL, 7413443736109338926ULL,
    902719806551551191ULL, 16568853118619045174ULL, 14202214862428279177ULL,
    11719595395278861192ULL, 5890053236389907647ULL, 9996196494965833627ULL,
    12967056942364782577ULL, 9034128755157395787ULL, 17898204904710512655ULL,
    8229373445062993977ULL, 13580036169519833644ULL
  };

static inline void precomp_get_consttime(const uint64_t *table, uint64_t bits_l, uint64_t *tmp)
{
  memcpy(tmp, (uint64_t *)table, 12U * sizeof (uint64_t));
  KRML_MAYBE_FOR15(i0,
    0U,
    15U,
    1U,
    uint64_t c = FStar_UInt64_eq_mask(bits_l, (uint64_t)(i0 + 1U));
    const uint64_t *res_j = table + (i0 + 1U) * 12U;
    KRML_MAYBE_FOR12(i,
      0U,
      12U,
      1U,
      uint64_t *os = tmp;
      uint64_t x = (c & res_j[i]) | (~c & tmp[i]);
      os[i] = x;););
}

static inline void point_mul(uint64_t *res, uint64_t *scalar, uint64_t *p)
{
  uint64_t table[192U] = { 0U };
  uint64_t tmp[12U] = { 0U };
  uint64_t *t0 = table;
  uint64_t *t1 = table + 12U;
  point_zero(t0);
  memcpy(t1, p, 12U * sizeof (uint64_t));
  KRML_MAYBE_FOR7(i,
    0U,
    7U,
    1U,
    uint64_t *t11 = table + (i + 1U) * 12U;
    point_double(t11, tmp);
    memcpy(table + (2U * i + 2U) * 12U, tmp, 12U * sizeof (uint64_t));
    uint64_t *t2 = table + (2U * i + 2U) * 12U;
    point_add(p, t2, tmp);
    memcpy(table + (2U * i + 3U) * 12U, tmp, 12U * sizeof (uint64_t)););
  point_zero(res);
  uint64_t tmp0[12U] = { 0U };
  for (uint32_t i0 = 0U; i0 < 64U; i0++)
  {
    KRML_MAYBE_FOR4(i, 0U, 4U, 1U, point_double(res, res););
    uint32_t k = 256U - 4U * i0 - 4U;
    uint64_t bits_l = Hacl_Bignum_Lib_bn_get_bits_u64(4U, scalar, k, 4U);
    memcpy(tmp0, (uint64_t *)table, 12U * sizeof (uint64_t));
    KRML_MAYBE_FOR15(i1,
      0U,
      15U,
      1U,
      uint64_t c = FStar_UInt64_eq_mask(bits_l, (uint64_t)(i1 + 1U));
      const uint64_t *res_j = table + (i1 + 1U) * 12U;
      KRML_MAYBE_FOR12(i,
        0U,
        12U,
        1U,
        uint64_t *os = tmp0;
        uint64_t x = (c & res_j[i]) | (~c & tmp0[i]);
        os[i] = x;););
    point_add(res, tmp0, res);
  }
}

static inline void point_mul_g(uint64_t *res, uint64_t *scalar)
{
  uint64_t q1[12U] = { 0U };
  uint64_t *x = q1;
  uint64_t *y = q1 + 4U;
  uint64_t *z = q1 + 8U;
  p256_make_g_x(x);
  p256_make_g_y(y);
  p256_make_fone(z);
  uint64_t
  q2[12U] =
    {
      1499621593102562565ULL, 16692369783039433128ULL, 15337520135922861848ULL,
      5455737214495366228ULL, 17827017231032529600ULL, 12413621606240782649ULL,
      2290483008028286132ULL, 15752017553340844820ULL, 4846430910634234874ULL,
      10861682798464583253ULL, 15404737222404363049ULL, 363586619281562022ULL
    };
  uint64_t
  q3[12U] =
    {
      14619254753077084366ULL, 13913835116514008593ULL, 15060744674088488145ULL,
      17668414598203068685ULL, 10761169236902342334ULL, 15467027479157446221ULL,
      14989185522423469618ULL, 14354539272510107003ULL, 14298211796392133693ULL,
      13270323784253711450ULL, 13380964971965046957ULL, 8686204248456909699ULL
    };
  uint64_t
  q4[12U] =
    {
      7870395003430845958ULL, 18001862936410067720ULL, 8006461232116967215ULL,
      5921313779532424762ULL, 10702113371959864307ULL, 8070517410642379879ULL,
      7139806720777708306ULL, 8253938546650739833ULL, 17490482834545705718ULL,
      1065249776797037500ULL, 5018258455937968775ULL, 14100621120178668337ULL
    };
  uint64_t *r1 = scalar;
  uint64_t *r2 = scalar + 1U;
  uint64_t *r3 = scalar + 2U;
  uint64_t *r4 = scalar + 3U;
  point_zero(res);
  uint64_t tmp[12U] = { 0U };
  KRML_MAYBE_FOR16(i,
    0U,
    16U,
    1U,
    KRML_MAYBE_FOR4(i0, 0U, 4U, 1U, point_double(res, res););
    uint32_t k = 64U - 4U * i - 4U;
    uint64_t bits_l = Hacl_Bignum_Lib_bn_get_bits_u64(1U, r4, k, 4U);
    precomp_get_consttime(p256_g_pow2_192_table_w4, bits_l, tmp);
    point_add(res, tmp, res);
    uint32_t k0 = 64U - 4U * i - 4U;
    uint64_t bits_l0 = Hacl_Bignum_Lib_bn_get_bits_u64(1U, r3, k0, 4U);
    precomp_get_consttime(p256_g_pow2_128_table_w4, bits_l0, tmp);
    point_add(res, tmp, res);
    uint32_t k1 = 64U - 4U * i - 4U;
    uint64_t bits_l1 = Hacl_Bignum_Lib_bn_get_bits_u64(1U, r2, k1, 4U);
    precomp_get_consttime(p256_g_pow2_64_table_w4, bits_l1, tmp);
    point_add(res, tmp, res);
    uint32_t k2 = 64U - 4U * i - 4U;
    uint64_t bits_l2 = Hacl_Bignum_Lib_bn_get_bits_u64(1U, r1, k2, 4U);
    precomp_get_consttime(p256_basepoint_table_w4, bits_l2, tmp);
    point_add(res, tmp, res););
  KRML_MAYBE_UNUSED_VAR(q1);
  KRML_MAYBE_UNUSED_VAR(q2);
  KRML_MAYBE_UNUSED_VAR(q3);
  KRML_MAYBE_UNUSED_VAR(q4);
}

static inline void
point_mul_double_g(uint64_t *res, uint64_t *scalar1, uint64_t *scalar2, uint64_t *q2)
{
  uint64_t q1[12U] = { 0U };
  uint64_t *x = q1;
  uint64_t *y = q1 + 4U;
  uint64_t *z = q1 + 8U;
  p256_make_g_x(x);
  p256_make_g_y(y);
  p256_make_fone(z);
  uint64_t table2[384U] = { 0U };
  uint64_t tmp[12U] = { 0U };
  uint64_t *t0 = table2;
  uint64_t *t1 = table2 + 12U;
  point_zero(t0);
  memcpy(t1, q2, 12U * sizeof (uint64_t));
  KRML_MAYBE_FOR15(i,
    0U,
    15U,
    1U,
    uint64_t *t11 = table2 + (i + 1U) * 12U;
    point_double(t11, tmp);
    memcpy(table2 + (2U * i + 2U) * 12U, tmp, 12U * sizeof (uint64_t));
    uint64_t *t2 = table2 + (2U * i + 2U) * 12U;
    point_add(q2, t2, tmp);
    memcpy(table2 + (2U * i + 3U) * 12U, tmp, 12U * sizeof (uint64_t)););
  uint64_t tmp0[12U] = { 0U };
  uint32_t i0 = 255U;
  uint64_t bits_c = Hacl_Bignum_Lib_bn_get_bits_u64(4U, scalar1, i0, 5U);
  uint32_t bits_l32 = (uint32_t)bits_c;
  const uint64_t *a_bits_l = p256_basepoint_table_w5 + bits_l32 * 12U;
  memcpy(res, (uint64_t *)a_bits_l, 12U * sizeof (uint64_t));
  uint32_t i1 = 255U;
  uint64_t bits_c0 = Hacl_Bignum_Lib_bn_get_bits_u64(4U, scalar2, i1, 5U);
  uint32_t bits_l320 = (uint32_t)bits_c0;
  const uint64_t *a_bits_l0 = table2 + bits_l320 * 12U;
  memcpy(tmp0, (uint64_t *)a_bits_l0, 12U * sizeof (uint64_t));
  point_add(res, tmp0, res);
  uint64_t tmp1[12U] = { 0U };
  for (uint32_t i = 0U; i < 51U; i++)
  {
    KRML_MAYBE_FOR5(i2, 0U, 5U, 1U, point_double(res, res););
    uint32_t k = 255U - 5U * i - 5U;
    uint64_t bits_l = Hacl_Bignum_Lib_bn_get_bits_u64(4U, scalar2, k, 5U);
    uint32_t bits_l321 = (uint32_t)bits_l;
    const uint64_t *a_bits_l1 = table2 + bits_l321 * 12U;
    memcpy(tmp1, (uint64_t *)a_bits_l1, 12U * sizeof (uint64_t));
    point_add(res, tmp1, res);
    uint32_t k0 = 255U - 5U * i - 5U;
    uint64_t bits_l0 = Hacl_Bignum_Lib_bn_get_bits_u64(4U, scalar1, k0, 5U);
    uint32_t bits_l322 = (uint32_t)bits_l0;
    const uint64_t *a_bits_l2 = p256_basepoint_table_w5 + bits_l322 * 12U;
    memcpy(tmp1, (uint64_t *)a_bits_l2, 12U * sizeof (uint64_t));
    point_add(res, tmp1, res);
  }
}

static inline bool
ecdsa_sign_msg_as_qelem(
  uint8_t *signature,
  uint64_t *m_q,
  uint8_t *private_key,
  uint8_t *nonce
)
{
  uint64_t rsdk_q[16U] = { 0U };
  uint64_t *r_q = rsdk_q;
  uint64_t *s_q = rsdk_q + 4U;
  uint64_t *d_a = rsdk_q + 8U;
  uint64_t *k_q = rsdk_q + 12U;
  uint64_t is_sk_valid = load_qelem_conditional(d_a, private_key);
  uint64_t is_nonce_valid = load_qelem_conditional(k_q, nonce);
  uint64_t are_sk_nonce_valid = is_sk_valid & is_nonce_valid;
  uint64_t p[12U] = { 0U };
  point_mul_g(p, k_q);
  uint64_t zinv[4U] = { 0U };
  uint64_t *px = p;
  uint64_t *pz = p + 8U;
  p256_finv(zinv, pz);
  fmul0(r_q, px, zinv);
  from_mont(r_q, r_q);
  qmod_short(r_q, r_q);
  uint64_t kinv[4U] = { 0U };
  p256_qinv(kinv, k_q);
  qmul(s_q, r_q, d_a);
  from_qmont(m_q, m_q);
  qadd(s_q, m_q, s_q);
  qmul(s_q, kinv, s_q);
  bn_to_bytes_be(signature, r_q);
  bn_to_bytes_be(signature + 32U, s_q);
  uint64_t bn_zero0[4U] = { 0U };
  uint64_t res = bn_is_eq_mask(r_q, bn_zero0);
  uint64_t is_r_zero = res;
  uint64_t bn_zero[4U] = { 0U };
  uint64_t res0 = bn_is_eq_mask(s_q, bn_zero);
  uint64_t is_s_zero = res0;
  uint64_t m = are_sk_nonce_valid & (~is_r_zero & ~is_s_zero);
  bool res1 = m == 0xFFFFFFFFFFFFFFFFULL;
  return res1;
}

static inline bool
ecdsa_verify_msg_as_qelem(
  uint64_t *m_q,
  uint8_t *public_key,
  uint8_t *signature_r,
  uint8_t *signature_s
)
{
  uint64_t tmp[28U] = { 0U };
  uint64_t *pk = tmp;
  uint64_t *r_q = tmp + 12U;
  uint64_t *s_q = tmp + 16U;
  uint64_t *u1 = tmp + 20U;
  uint64_t *u2 = tmp + 24U;
  uint64_t p_aff[8U] = { 0U };
  uint8_t *p_x = public_key;
  uint8_t *p_y = public_key + 32U;
  uint64_t *bn_p_x = p_aff;
  uint64_t *bn_p_y = p_aff + 4U;
  bn_from_bytes_be(bn_p_x, p_x);
  bn_from_bytes_be(bn_p_y, p_y);
  uint64_t *px0 = p_aff;
  uint64_t *py0 = p_aff + 4U;
  uint64_t lessX = bn_is_lt_prime_mask(px0);
  uint64_t lessY = bn_is_lt_prime_mask(py0);
  uint64_t res0 = lessX & lessY;
  bool is_xy_valid = res0 == 0xFFFFFFFFFFFFFFFFULL;
  bool res;
  if (!is_xy_valid)
  {
    res = false;
  }
  else
  {
    uint64_t rp[4U] = { 0U };
    uint64_t tx[4U] = { 0U };
    uint64_t ty[4U] = { 0U };
    uint64_t *px = p_aff;
    uint64_t *py = p_aff + 4U;
    to_mont(tx, px);
    to_mont(ty, py);
    uint64_t tmp1[4U] = { 0U };
    fsqr0(rp, tx);
    fmul0(rp, rp, tx);
    p256_make_a_coeff(tmp1);
    fmul0(tmp1, tmp1, tx);
    fadd0(rp, tmp1, rp);
    p256_make_b_coeff(tmp1);
    fadd0(rp, tmp1, rp);
    fsqr0(ty, ty);
    uint64_t r = bn_is_eq_mask(ty, rp);
    uint64_t r0 = r;
    bool r1 = r0 == 0xFFFFFFFFFFFFFFFFULL;
    res = r1;
  }
  if (res)
  {
    uint64_t *px = p_aff;
    uint64_t *py = p_aff + 4U;
    uint64_t *rx = pk;
    uint64_t *ry = pk + 4U;
    uint64_t *rz = pk + 8U;
    to_mont(rx, px);
    to_mont(ry, py);
    p256_make_fone(rz);
  }
  bool is_pk_valid = res;
  bn_from_bytes_be(r_q, signature_r);
  bn_from_bytes_be(s_q, signature_s);
  uint64_t tmp10[4U] = { 0U };
  p256_make_order(tmp10);
  uint64_t c = bn_sub(tmp10, r_q, tmp10);
  uint64_t is_lt_order = 0ULL - c;
  uint64_t bn_zero0[4U] = { 0U };
  uint64_t res1 = bn_is_eq_mask(r_q, bn_zero0);
  uint64_t is_eq_zero = res1;
  uint64_t is_r_valid = is_lt_order & ~is_eq_zero;
  uint64_t tmp11[4U] = { 0U };
  p256_make_order(tmp11);
  uint64_t c0 = bn_sub(tmp11, s_q, tmp11);
  uint64_t is_lt_order0 = 0ULL - c0;
  uint64_t bn_zero1[4U] = { 0U };
  uint64_t res2 = bn_is_eq_mask(s_q, bn_zero1);
  uint64_t is_eq_zero0 = res2;
  uint64_t is_s_valid = is_lt_order0 & ~is_eq_zero0;
  bool is_rs_valid = is_r_valid == 0xFFFFFFFFFFFFFFFFULL && is_s_valid == 0xFFFFFFFFFFFFFFFFULL;
  if (!(is_pk_valid && is_rs_valid))
  {
    return false;
  }
  uint64_t sinv[4U] = { 0U };
  p256_qinv(sinv, s_q);
  uint64_t tmp1[4U] = { 0U };
  from_qmont(tmp1, m_q);
  qmul(u1, sinv, tmp1);
  uint64_t tmp12[4U] = { 0U };
  from_qmont(tmp12, r_q);
  qmul(u2, sinv, tmp12);
  uint64_t res3[12U] = { 0U };
  point_mul_double_g(res3, u1, u2, pk);
  uint64_t *pz0 = res3 + 8U;
  uint64_t bn_zero[4U] = { 0U };
  uint64_t res10 = bn_is_eq_mask(pz0, bn_zero);
  uint64_t m = res10;
  if (m == 0xFFFFFFFFFFFFFFFFULL)
  {
    return false;
  }
  uint64_t x[4U] = { 0U };
  uint64_t zinv[4U] = { 0U };
  uint64_t *px = res3;
  uint64_t *pz = res3 + 8U;
  p256_finv(zinv, pz);
  fmul0(x, px, zinv);
  from_mont(x, x);
  qmod_short(x, x);
  uint64_t m0 = bn_is_eq_mask(x, r_q);
  bool res11 = m0 == 0xFFFFFFFFFFFFFFFFULL;
  return res11;
}


/*******************************************************************************

 Verified C library for ECDSA and ECDH functions over the P-256 NIST curve.

 This module implements signing and verification, key validation, conversions
 between various point representations, and ECDH key agreement.

*******************************************************************************/

/*****************/
/* ECDSA signing */
/*****************/

/*
  As per the standard, a hash function *shall* be used. Therefore, we recommend
  using one of the three combined hash-and-sign variants.
*/

/**
Create an ECDSA signature using SHA2-256.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `private_key` and `nonce` are valid:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve
*/
bool
Hacl_P256_ecdsa_sign_p256_sha2(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
)
{
  uint64_t m_q[4U] = { 0U };
  uint8_t mHash[32U] = { 0U };
  Hacl_Hash_SHA2_hash_256(mHash, msg, msg_len);
  KRML_MAYBE_UNUSED_VAR(msg_len);
  uint8_t *mHash32 = mHash;
  bn_from_bytes_be(m_q, mHash32);
  qmod_short(m_q, m_q);
  bool res = ecdsa_sign_msg_as_qelem(signature, m_q, private_key, nonce);
  return res;
}

/**
Create an ECDSA signature using SHA2-384.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `private_key` and `nonce` are valid:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve
*/
bool
Hacl_P256_ecdsa_sign_p256_sha384(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
)
{
  uint64_t m_q[4U] = { 0U };
  uint8_t mHash[48U] = { 0U };
  Hacl_Hash_SHA2_hash_384(mHash, msg, msg_len);
  KRML_MAYBE_UNUSED_VAR(msg_len);
  uint8_t *mHash32 = mHash;
  bn_from_bytes_be(m_q, mHash32);
  qmod_short(m_q, m_q);
  bool res = ecdsa_sign_msg_as_qelem(signature, m_q, private_key, nonce);
  return res;
}

/**
Create an ECDSA signature using SHA2-512.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `private_key` and `nonce` are valid:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve
*/
bool
Hacl_P256_ecdsa_sign_p256_sha512(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
)
{
  uint64_t m_q[4U] = { 0U };
  uint8_t mHash[64U] = { 0U };
  Hacl_Hash_SHA2_hash_512(mHash, msg, msg_len);
  KRML_MAYBE_UNUSED_VAR(msg_len);
  uint8_t *mHash32 = mHash;
  bn_from_bytes_be(m_q, mHash32);
  qmod_short(m_q, m_q);
  bool res = ecdsa_sign_msg_as_qelem(signature, m_q, private_key, nonce);
  return res;
}

/**
Create an ECDSA signature WITHOUT hashing first.

  This function is intended to receive a hash of the input.
  For convenience, we recommend using one of the hash-and-sign combined functions above.

  The argument `msg` MUST be at least 32 bytes (i.e. `msg_len >= 32`).

  NOTE: The equivalent functions in OpenSSL and Fiat-Crypto both accept inputs
  smaller than 32 bytes. These libraries left-pad the input with enough zeroes to
  reach the minimum 32 byte size. Clients who need behavior identical to OpenSSL
  need to perform the left-padding themselves.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `private_key` and `nonce` are valid values:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve
*/
bool
Hacl_P256_ecdsa_sign_p256_without_hash(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
)
{
  uint64_t m_q[4U] = { 0U };
  uint8_t mHash[32U] = { 0U };
  memcpy(mHash, msg, 32U * sizeof (uint8_t));
  KRML_MAYBE_UNUSED_VAR(msg_len);
  uint8_t *mHash32 = mHash;
  bn_from_bytes_be(m_q, mHash32);
  qmod_short(m_q, m_q);
  bool res = ecdsa_sign_msg_as_qelem(signature, m_q, private_key, nonce);
  return res;
}


/**********************/
/* ECDSA verification */
/**********************/

/**
Verify an ECDSA signature using SHA2-256.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The argument `public_key` (x || y) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `signature_r` and `signature_s` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `public_key` is valid
*/
bool
Hacl_P256_ecdsa_verif_p256_sha2(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature_r,
  uint8_t *signature_s
)
{
  uint64_t m_q[4U] = { 0U };
  uint8_t mHash[32U] = { 0U };
  Hacl_Hash_SHA2_hash_256(mHash, msg, msg_len);
  KRML_MAYBE_UNUSED_VAR(msg_len);
  uint8_t *mHash32 = mHash;
  bn_from_bytes_be(m_q, mHash32);
  qmod_short(m_q, m_q);
  bool res = ecdsa_verify_msg_as_qelem(m_q, public_key, signature_r, signature_s);
  return res;
}

/**
Verify an ECDSA signature using SHA2-384.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The argument `public_key` (x || y) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `signature_r` and `signature_s` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `public_key` is valid
*/
bool
Hacl_P256_ecdsa_verif_p256_sha384(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature_r,
  uint8_t *signature_s
)
{
  uint64_t m_q[4U] = { 0U };
  uint8_t mHash[48U] = { 0U };
  Hacl_Hash_SHA2_hash_384(mHash, msg, msg_len);
  KRML_MAYBE_UNUSED_VAR(msg_len);
  uint8_t *mHash32 = mHash;
  bn_from_bytes_be(m_q, mHash32);
  qmod_short(m_q, m_q);
  bool res = ecdsa_verify_msg_as_qelem(m_q, public_key, signature_r, signature_s);
  return res;
}

/**
Verify an ECDSA signature using SHA2-512.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The argument `public_key` (x || y) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `signature_r` and `signature_s` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `public_key` is valid
*/
bool
Hacl_P256_ecdsa_verif_p256_sha512(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature_r,
  uint8_t *signature_s
)
{
  uint64_t m_q[4U] = { 0U };
  uint8_t mHash[64U] = { 0U };
  Hacl_Hash_SHA2_hash_512(mHash, msg, msg_len);
  KRML_MAYBE_UNUSED_VAR(msg_len);
  uint8_t *mHash32 = mHash;
  bn_from_bytes_be(m_q, mHash32);
  qmod_short(m_q, m_q);
  bool res = ecdsa_verify_msg_as_qelem(m_q, public_key, signature_r, signature_s);
  return res;
}

/**
Verify an ECDSA signature WITHOUT hashing first.

  This function is intended to receive a hash of the input.
  For convenience, we recommend using one of the hash-and-verify combined functions above.

  The argument `msg` MUST be at least 32 bytes (i.e. `msg_len >= 32`).

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The argument `public_key` (x || y) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `signature_r` and `signature_s` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `public_key` is valid
*/
bool
Hacl_P256_ecdsa_verif_without_hash(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature_r,
  uint8_t *signature_s
)
{
  uint64_t m_q[4U] = { 0U };
  uint8_t mHash[32U] = { 0U };
  memcpy(mHash, msg, 32U * sizeof (uint8_t));
  KRML_MAYBE_UNUSED_VAR(msg_len);
  uint8_t *mHash32 = mHash;
  bn_from_bytes_be(m_q, mHash32);
  qmod_short(m_q, m_q);
  bool res = ecdsa_verify_msg_as_qelem(m_q, public_key, signature_r, signature_s);
  return res;
}


/******************/
/* Key validation */
/******************/

/**
Public key validation.

  The function returns `true` if a public key is valid and `false` otherwise.

  The argument `public_key` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The public key (x || y) is valid (with respect to SP 800-56A):
    • the public key is not the “point at infinity”, represented as O.
    • the affine x and y coordinates of the point represented by the public key are
      in the range [0, p – 1] where p is the prime defining the finite field.
    • y^2 = x^3 + ax + b where a and b are the coefficients of the curve equation.
  The last extract is taken from: https://neilmadden.blog/2017/05/17/so-how-do-you-validate-nist-ecdh-public-keys/
*/
bool Hacl_P256_validate_public_key(uint8_t *public_key)
{
  uint64_t point_jac[12U] = { 0U };
  uint64_t p_aff[8U] = { 0U };
  uint8_t *p_x = public_key;
  uint8_t *p_y = public_key + 32U;
  uint64_t *bn_p_x = p_aff;
  uint64_t *bn_p_y = p_aff + 4U;
  bn_from_bytes_be(bn_p_x, p_x);
  bn_from_bytes_be(bn_p_y, p_y);
  uint64_t *px0 = p_aff;
  uint64_t *py0 = p_aff + 4U;
  uint64_t lessX = bn_is_lt_prime_mask(px0);
  uint64_t lessY = bn_is_lt_prime_mask(py0);
  uint64_t res0 = lessX & lessY;
  bool is_xy_valid = res0 == 0xFFFFFFFFFFFFFFFFULL;
  bool res;
  if (!is_xy_valid)
  {
    res = false;
  }
  else
  {
    uint64_t rp[4U] = { 0U };
    uint64_t tx[4U] = { 0U };
    uint64_t ty[4U] = { 0U };
    uint64_t *px = p_aff;
    uint64_t *py = p_aff + 4U;
    to_mont(tx, px);
    to_mont(ty, py);
    uint64_t tmp[4U] = { 0U };
    fsqr0(rp, tx);
    fmul0(rp, rp, tx);
    p256_make_a_coeff(tmp);
    fmul0(tmp, tmp, tx);
    fadd0(rp, tmp, rp);
    p256_make_b_coeff(tmp);
    fadd0(rp, tmp, rp);
    fsqr0(ty, ty);
    uint64_t r = bn_is_eq_mask(ty, rp);
    uint64_t r0 = r;
    bool r1 = r0 == 0xFFFFFFFFFFFFFFFFULL;
    res = r1;
  }
  if (res)
  {
    uint64_t *px = p_aff;
    uint64_t *py = p_aff + 4U;
    uint64_t *rx = point_jac;
    uint64_t *ry = point_jac + 4U;
    uint64_t *rz = point_jac + 8U;
    to_mont(rx, px);
    to_mont(ry, py);
    p256_make_fone(rz);
  }
  bool res1 = res;
  return res1;
}

/**
Private key validation.

  The function returns `true` if a private key is valid and `false` otherwise.

  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The private key is valid:
    • 0 < `private_key` < the order of the curve
*/
bool Hacl_P256_validate_private_key(uint8_t *private_key)
{
  uint64_t bn_sk[4U] = { 0U };
  bn_from_bytes_be(bn_sk, private_key);
  uint64_t tmp[4U] = { 0U };
  p256_make_order(tmp);
  uint64_t c = bn_sub(tmp, bn_sk, tmp);
  uint64_t is_lt_order = 0ULL - c;
  uint64_t bn_zero[4U] = { 0U };
  uint64_t res = bn_is_eq_mask(bn_sk, bn_zero);
  uint64_t is_eq_zero = res;
  uint64_t res0 = is_lt_order & ~is_eq_zero;
  return res0 == 0xFFFFFFFFFFFFFFFFULL;
}

/*******************************************************************************
  Parsing and Serializing public keys.

  A public key is a point (x, y) on the P-256 NIST curve.

  The point can be represented in the following three ways.
    • raw          = [ x || y ], 64 bytes
    • uncompressed = [ 0x04 || x || y ], 65 bytes
    • compressed   = [ (0x02 for even `y` and 0x03 for odd `y`) || x ], 33 bytes

*******************************************************************************/


/**
Convert a public key from uncompressed to its raw form.

  The function returns `true` for successful conversion of a public key and `false` otherwise.

  The outparam `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `pk` points to 65 bytes of valid memory, i.e., uint8_t[65].

  The function DOESN'T check whether (x, y) is a valid point.
*/
bool Hacl_P256_uncompressed_to_raw(uint8_t *pk, uint8_t *pk_raw)
{
  uint8_t pk0 = pk[0U];
  if (pk0 != 0x04U)
  {
    return false;
  }
  memcpy(pk_raw, pk + 1U, 64U * sizeof (uint8_t));
  return true;
}

/**
Convert a public key from compressed to its raw form.

  The function returns `true` for successful conversion of a public key and `false` otherwise.

  The outparam `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `pk` points to 33 bytes of valid memory, i.e., uint8_t[33].

  The function also checks whether (x, y) is a valid point.
*/
bool Hacl_P256_compressed_to_raw(uint8_t *pk, uint8_t *pk_raw)
{
  uint64_t xa[4U] = { 0U };
  uint64_t ya[4U] = { 0U };
  uint8_t *pk_xb = pk + 1U;
  uint8_t s0 = pk[0U];
  uint8_t s01 = s0;
  bool b;
  if (!(s01 == 0x02U || s01 == 0x03U))
  {
    b = false;
  }
  else
  {
    uint8_t *xb = pk + 1U;
    bn_from_bytes_be(xa, xb);
    uint64_t is_x_valid = bn_is_lt_prime_mask(xa);
    bool is_x_valid1 = is_x_valid == 0xFFFFFFFFFFFFFFFFULL;
    bool is_y_odd = s01 == 0x03U;
    if (!is_x_valid1)
    {
      b = false;
    }
    else
    {
      uint64_t y2M[4U] = { 0U };
      uint64_t xM[4U] = { 0U };
      uint64_t yM[4U] = { 0U };
      to_mont(xM, xa);
      uint64_t tmp[4U] = { 0U };
      fsqr0(y2M, xM);
      fmul0(y2M, y2M, xM);
      p256_make_a_coeff(tmp);
      fmul0(tmp, tmp, xM);
      fadd0(y2M, tmp, y2M);
      p256_make_b_coeff(tmp);
      fadd0(y2M, tmp, y2M);
      p256_fsqrt(yM, y2M);
      from_mont(ya, yM);
      fsqr0(yM, yM);
      uint64_t r = bn_is_eq_mask(yM, y2M);
      uint64_t r0 = r;
      bool is_y_valid = r0 == 0xFFFFFFFFFFFFFFFFULL;
      bool is_y_valid0 = is_y_valid;
      if (!is_y_valid0)
      {
        b = false;
      }
      else
      {
        uint64_t is_y_odd1 = ya[0U] & 1ULL;
        bool is_y_odd2 = is_y_odd1 == 1ULL;
        uint64_t zero[4U] = { 0U };
        if (is_y_odd2 != is_y_odd)
        {
          fsub0(ya, zero, ya);
        }
        b = true;
      }
    }
  }
  if (b)
  {
    memcpy(pk_raw, pk_xb, 32U * sizeof (uint8_t));
    bn_to_bytes_be(pk_raw + 32U, ya);
  }
  return b;
}

/**
Convert a public key from raw to its uncompressed form.

  The outparam `pk` points to 65 bytes of valid memory, i.e., uint8_t[65].
  The argument `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T check whether (x, y) is a valid point.
*/
void Hacl_P256_raw_to_uncompressed(uint8_t *pk_raw, uint8_t *pk)
{
  pk[0U] = 0x04U;
  memcpy(pk + 1U, pk_raw, 64U * sizeof (uint8_t));
}

/**
Convert a public key from raw to its compressed form.

  The outparam `pk` points to 33 bytes of valid memory, i.e., uint8_t[33].
  The argument `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T check whether (x, y) is a valid point.
*/
void Hacl_P256_raw_to_compressed(uint8_t *pk_raw, uint8_t *pk)
{
  uint8_t *pk_x = pk_raw;
  uint8_t *pk_y = pk_raw + 32U;
  uint64_t bn_f[4U] = { 0U };
  bn_from_bytes_be(bn_f, pk_y);
  uint64_t is_odd_f = bn_f[0U] & 1ULL;
  pk[0U] = (uint32_t)(uint8_t)is_odd_f + 0x02U;
  memcpy(pk + 1U, pk_x, 32U * sizeof (uint8_t));
}


/******************/
/* ECDH agreement */
/******************/

/**
Compute the public key from the private key.

  The function returns `true` if a private key is valid and `false` otherwise.

  The outparam `public_key`  points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The private key is valid:
    • 0 < `private_key` < the order of the curve.
*/
bool Hacl_P256_dh_initiator(uint8_t *public_key, uint8_t *private_key)
{
  uint64_t tmp[16U] = { 0U };
  uint64_t *sk = tmp;
  uint64_t *pk = tmp + 4U;
  uint64_t is_sk_valid = load_qelem_conditional(sk, private_key);
  point_mul_g(pk, sk);
  uint64_t aff_p[8U] = { 0U };
  uint64_t zinv[4U] = { 0U };
  uint64_t *px = pk;
  uint64_t *py0 = pk + 4U;
  uint64_t *pz = pk + 8U;
  uint64_t *x = aff_p;
  uint64_t *y = aff_p + 4U;
  p256_finv(zinv, pz);
  fmul0(x, px, zinv);
  fmul0(y, py0, zinv);
  from_mont(x, x);
  from_mont(y, y);
  uint64_t *px0 = aff_p;
  uint64_t *py = aff_p + 4U;
  bn_to_bytes_be(public_key, px0);
  bn_to_bytes_be(public_key + 32U, py);
  return is_sk_valid == 0xFFFFFFFFFFFFFFFFULL;
}

/**
Execute the diffie-hellmann key exchange.

  The function returns `true` for successful creation of an ECDH shared secret and
  `false` otherwise.

  The outparam `shared_secret` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `their_pubkey` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `private_key` and `their_pubkey` are valid.
*/
bool
Hacl_P256_dh_responder(uint8_t *shared_secret, uint8_t *their_pubkey, uint8_t *private_key)
{
  uint64_t tmp[128U] = { 0U };
  uint64_t *sk = tmp;
  uint64_t *pk = tmp + 4U;
  uint64_t p_aff[8U] = { 0U };
  uint8_t *p_x = their_pubkey;
  uint8_t *p_y = their_pubkey + 32U;
  uint64_t *bn_p_x = p_aff;
  uint64_t *bn_p_y = p_aff + 4U;
  bn_from_bytes_be(bn_p_x, p_x);
  bn_from_bytes_be(bn_p_y, p_y);
  uint64_t *px0 = p_aff;
  uint64_t *py0 = p_aff + 4U;
  uint64_t lessX = bn_is_lt_prime_mask(px0);
  uint64_t lessY = bn_is_lt_prime_mask(py0);
  uint64_t res0 = lessX & lessY;
  bool is_xy_valid = res0 == 0xFFFFFFFFFFFFFFFFULL;
  bool res;
  if (!is_xy_valid)
  {
    res = false;
  }
  else
  {
    uint64_t rp[4U] = { 0U };
    uint64_t tx[4U] = { 0U };
    uint64_t ty[4U] = { 0U };
    uint64_t *px = p_aff;
    uint64_t *py = p_aff + 4U;
    to_mont(tx, px);
    to_mont(ty, py);
    uint64_t tmp1[4U] = { 0U };
    fsqr0(rp, tx);
    fmul0(rp, rp, tx);
    p256_make_a_coeff(tmp1);
    fmul0(tmp1, tmp1, tx);
    fadd0(rp, tmp1, rp);
    p256_make_b_coeff(tmp1);
    fadd0(rp, tmp1, rp);
    fsqr0(ty, ty);
    uint64_t r = bn_is_eq_mask(ty, rp);
    uint64_t r0 = r;
    bool r1 = r0 == 0xFFFFFFFFFFFFFFFFULL;
    res = r1;
  }
  if (res)
  {
    uint64_t *px = p_aff;
    uint64_t *py = p_aff + 4U;
    uint64_t *rx = pk;
    uint64_t *ry = pk + 4U;
    uint64_t *rz = pk + 8U;
    to_mont(rx, px);
    to_mont(ry, py);
    p256_make_fone(rz);
  }
  bool is_pk_valid = res;
  uint64_t is_sk_valid = load_qelem_conditional(sk, private_key);
  uint64_t ss_proj[12U] = { 0U };
  if (is_pk_valid)
  {
    point_mul(ss_proj, sk, pk);
    uint64_t aff_p[8U] = { 0U };
    uint64_t zinv[4U] = { 0U };
    uint64_t *px = ss_proj;
    uint64_t *py1 = ss_proj + 4U;
    uint64_t *pz = ss_proj + 8U;
    uint64_t *x = aff_p;
    uint64_t *y = aff_p + 4U;
    p256_finv(zinv, pz);
    fmul0(x, px, zinv);
    fmul0(y, py1, zinv);
    from_mont(x, x);
    from_mont(y, y);
    uint64_t *px1 = aff_p;
    uint64_t *py = aff_p + 4U;
    bn_to_bytes_be(shared_secret, px1);
    bn_to_bytes_be(shared_secret + 32U, py);
  }
  return is_sk_valid == 0xFFFFFFFFFFFFFFFFULL && is_pk_valid;
}

