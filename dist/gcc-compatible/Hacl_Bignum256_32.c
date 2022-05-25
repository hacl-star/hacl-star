/* MIT License
 *
 * Copyright (c) 2016-2020 INRIA, CMU and Microsoft Corporation
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


#include "Hacl_Bignum256_32.h"

#include "internal/Hacl_Krmllib.h"
#include "internal/Hacl_Bignum.h"

/*******************************************************************************

A verified 256-bit bignum library.

This is a 32-bit optimized version, where bignums are represented as an array
of eight unsigned 32-bit integers, i.e. uint32_t[8]. Furthermore, the
limbs are stored in little-endian format, i.e. the least significant limb is at
index 0. Each limb is stored in native format in memory. Example:

  uint32_t sixteen[8] = { 0x10; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00 }

We strongly encourage users to go through the conversion functions, e.g.
bn_from_bytes_be, to i) not depend on internal representation choices and ii)
have the ability to switch easily to a 64-bit optimized version in the future.

*******************************************************************************/

/************************/
/* Arithmetic functions */
/************************/


/*
Write `a + b mod 2^256` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 256-bit bignums, i.e. uint32_t[8]
*/
uint32_t Hacl_Bignum256_32_add(uint32_t *a, uint32_t *b, uint32_t *res)
{
  uint32_t c = (uint32_t)0U;
  {
    uint32_t t1 = a[(uint32_t)4U * (uint32_t)0U];
    uint32_t t20 = b[(uint32_t)4U * (uint32_t)0U];
    uint32_t *res_i0 = res + (uint32_t)4U * (uint32_t)0U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t1, t20, res_i0);
    uint32_t t10 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint32_t t21 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint32_t *res_i1 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t10, t21, res_i1);
    uint32_t t11 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint32_t t22 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint32_t *res_i2 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t11, t22, res_i2);
    uint32_t t12 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint32_t t2 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint32_t *res_i = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t12, t2, res_i);
  }
  {
    uint32_t t1 = a[(uint32_t)4U * (uint32_t)1U];
    uint32_t t20 = b[(uint32_t)4U * (uint32_t)1U];
    uint32_t *res_i0 = res + (uint32_t)4U * (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t1, t20, res_i0);
    uint32_t t10 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
    uint32_t t21 = b[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
    uint32_t *res_i1 = res + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t10, t21, res_i1);
    uint32_t t11 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
    uint32_t t22 = b[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
    uint32_t *res_i2 = res + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t11, t22, res_i2);
    uint32_t t12 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
    uint32_t t2 = b[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
    uint32_t *res_i = res + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t12, t2, res_i);
  }
  return c;
}

/*
Write `a - b mod 2^256` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 256-bit bignums, i.e. uint32_t[8]
*/
uint32_t Hacl_Bignum256_32_sub(uint32_t *a, uint32_t *b, uint32_t *res)
{
  uint32_t c = (uint32_t)0U;
  {
    uint32_t t1 = a[(uint32_t)4U * (uint32_t)0U];
    uint32_t t20 = b[(uint32_t)4U * (uint32_t)0U];
    uint32_t *res_i0 = res + (uint32_t)4U * (uint32_t)0U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, t20, res_i0);
    uint32_t t10 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint32_t t21 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint32_t *res_i1 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t10, t21, res_i1);
    uint32_t t11 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint32_t t22 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint32_t *res_i2 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t11, t22, res_i2);
    uint32_t t12 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint32_t t2 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint32_t *res_i = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t12, t2, res_i);
  }
  {
    uint32_t t1 = a[(uint32_t)4U * (uint32_t)1U];
    uint32_t t20 = b[(uint32_t)4U * (uint32_t)1U];
    uint32_t *res_i0 = res + (uint32_t)4U * (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, t20, res_i0);
    uint32_t t10 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
    uint32_t t21 = b[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
    uint32_t *res_i1 = res + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t10, t21, res_i1);
    uint32_t t11 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
    uint32_t t22 = b[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
    uint32_t *res_i2 = res + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t11, t22, res_i2);
    uint32_t t12 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
    uint32_t t2 = b[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
    uint32_t *res_i = res + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t12, t2, res_i);
  }
  return c;
}

/*
Write `(a + b) mod n` in `res`.

  The arguments a, b, n and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • a < n
  • b < n
*/
void Hacl_Bignum256_32_add_mod(uint32_t *n, uint32_t *a, uint32_t *b, uint32_t *res)
{
  uint32_t c0 = (uint32_t)0U;
  {
    uint32_t t1 = a[(uint32_t)4U * (uint32_t)0U];
    uint32_t t20 = b[(uint32_t)4U * (uint32_t)0U];
    uint32_t *res_i0 = res + (uint32_t)4U * (uint32_t)0U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t1, t20, res_i0);
    uint32_t t10 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint32_t t21 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint32_t *res_i1 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t10, t21, res_i1);
    uint32_t t11 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint32_t t22 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint32_t *res_i2 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t11, t22, res_i2);
    uint32_t t12 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint32_t t2 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint32_t *res_i = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t12, t2, res_i);
  }
  {
    uint32_t t1 = a[(uint32_t)4U * (uint32_t)1U];
    uint32_t t20 = b[(uint32_t)4U * (uint32_t)1U];
    uint32_t *res_i0 = res + (uint32_t)4U * (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t1, t20, res_i0);
    uint32_t t10 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
    uint32_t t21 = b[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
    uint32_t *res_i1 = res + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t10, t21, res_i1);
    uint32_t t11 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
    uint32_t t22 = b[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
    uint32_t *res_i2 = res + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t11, t22, res_i2);
    uint32_t t12 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
    uint32_t t2 = b[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
    uint32_t *res_i = res + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t12, t2, res_i);
  }
  uint32_t c00 = c0;
  uint32_t tmp[8U] = { 0U };
  uint32_t c = (uint32_t)0U;
  {
    uint32_t t1 = res[(uint32_t)4U * (uint32_t)0U];
    uint32_t t20 = n[(uint32_t)4U * (uint32_t)0U];
    uint32_t *res_i0 = tmp + (uint32_t)4U * (uint32_t)0U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, t20, res_i0);
    uint32_t t10 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint32_t t21 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint32_t *res_i1 = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t10, t21, res_i1);
    uint32_t t11 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint32_t t22 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint32_t *res_i2 = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t11, t22, res_i2);
    uint32_t t12 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint32_t t2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint32_t *res_i = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t12, t2, res_i);
  }
  {
    uint32_t t1 = res[(uint32_t)4U * (uint32_t)1U];
    uint32_t t20 = n[(uint32_t)4U * (uint32_t)1U];
    uint32_t *res_i0 = tmp + (uint32_t)4U * (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, t20, res_i0);
    uint32_t t10 = res[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
    uint32_t t21 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
    uint32_t *res_i1 = tmp + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t10, t21, res_i1);
    uint32_t t11 = res[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
    uint32_t t22 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
    uint32_t *res_i2 = tmp + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t11, t22, res_i2);
    uint32_t t12 = res[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
    uint32_t t2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
    uint32_t *res_i = tmp + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t12, t2, res_i);
  }
  uint32_t c1 = c;
  uint32_t c2 = c00 - c1;
  {
    uint32_t *os = res;
    uint32_t x = (c2 & res[0U]) | (~c2 & tmp[0U]);
    os[0U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & res[1U]) | (~c2 & tmp[1U]);
    os[1U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & res[2U]) | (~c2 & tmp[2U]);
    os[2U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & res[3U]) | (~c2 & tmp[3U]);
    os[3U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & res[4U]) | (~c2 & tmp[4U]);
    os[4U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & res[5U]) | (~c2 & tmp[5U]);
    os[5U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & res[6U]) | (~c2 & tmp[6U]);
    os[6U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & res[7U]) | (~c2 & tmp[7U]);
    os[7U] = x;
  }
}

/*
Write `(a - b) mod n` in `res`.

  The arguments a, b, n and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • a < n
  • b < n
*/
void Hacl_Bignum256_32_sub_mod(uint32_t *n, uint32_t *a, uint32_t *b, uint32_t *res)
{
  uint32_t c0 = (uint32_t)0U;
  {
    uint32_t t1 = a[(uint32_t)4U * (uint32_t)0U];
    uint32_t t20 = b[(uint32_t)4U * (uint32_t)0U];
    uint32_t *res_i0 = res + (uint32_t)4U * (uint32_t)0U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t1, t20, res_i0);
    uint32_t t10 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint32_t t21 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint32_t *res_i1 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t10, t21, res_i1);
    uint32_t t11 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint32_t t22 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint32_t *res_i2 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t11, t22, res_i2);
    uint32_t t12 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint32_t t2 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint32_t *res_i = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t12, t2, res_i);
  }
  {
    uint32_t t1 = a[(uint32_t)4U * (uint32_t)1U];
    uint32_t t20 = b[(uint32_t)4U * (uint32_t)1U];
    uint32_t *res_i0 = res + (uint32_t)4U * (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t1, t20, res_i0);
    uint32_t t10 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
    uint32_t t21 = b[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
    uint32_t *res_i1 = res + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t10, t21, res_i1);
    uint32_t t11 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
    uint32_t t22 = b[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
    uint32_t *res_i2 = res + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t11, t22, res_i2);
    uint32_t t12 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
    uint32_t t2 = b[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
    uint32_t *res_i = res + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t12, t2, res_i);
  }
  uint32_t c00 = c0;
  uint32_t tmp[8U] = { 0U };
  uint32_t c = (uint32_t)0U;
  {
    uint32_t t1 = res[(uint32_t)4U * (uint32_t)0U];
    uint32_t t20 = n[(uint32_t)4U * (uint32_t)0U];
    uint32_t *res_i0 = tmp + (uint32_t)4U * (uint32_t)0U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t1, t20, res_i0);
    uint32_t t10 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint32_t t21 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint32_t *res_i1 = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t10, t21, res_i1);
    uint32_t t11 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint32_t t22 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint32_t *res_i2 = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t11, t22, res_i2);
    uint32_t t12 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint32_t t2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint32_t *res_i = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t12, t2, res_i);
  }
  {
    uint32_t t1 = res[(uint32_t)4U * (uint32_t)1U];
    uint32_t t20 = n[(uint32_t)4U * (uint32_t)1U];
    uint32_t *res_i0 = tmp + (uint32_t)4U * (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t1, t20, res_i0);
    uint32_t t10 = res[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
    uint32_t t21 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
    uint32_t *res_i1 = tmp + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t10, t21, res_i1);
    uint32_t t11 = res[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
    uint32_t t22 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
    uint32_t *res_i2 = tmp + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t11, t22, res_i2);
    uint32_t t12 = res[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
    uint32_t t2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
    uint32_t *res_i = tmp + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t12, t2, res_i);
  }
  uint32_t c1 = c;
  uint32_t c2 = (uint32_t)0U - c00;
  {
    uint32_t *os = res;
    uint32_t x = (c2 & tmp[0U]) | (~c2 & res[0U]);
    os[0U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & tmp[1U]) | (~c2 & res[1U]);
    os[1U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & tmp[2U]) | (~c2 & res[2U]);
    os[2U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & tmp[3U]) | (~c2 & res[3U]);
    os[3U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & tmp[4U]) | (~c2 & res[4U]);
    os[4U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & tmp[5U]) | (~c2 & res[5U]);
    os[5U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & tmp[6U]) | (~c2 & res[6U]);
    os[6U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & tmp[7U]) | (~c2 & res[7U]);
    os[7U] = x;
  }
}

/*
Write `a * b` in `res`.

  The arguments a and b are meant to be 256-bit bignums, i.e. uint32_t[8].
  The outparam res is meant to be a 512-bit bignum, i.e. uint32_t[16].
*/
void Hacl_Bignum256_32_mul(uint32_t *a, uint32_t *b, uint32_t *res)
{
  memset(res, 0U, (uint32_t)16U * sizeof (uint32_t));
  {
    uint32_t bj = b[0U];
    uint32_t *res_j = res;
    uint32_t c = (uint32_t)0U;
    {
      uint32_t a_i = a[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
      uint32_t a_i0 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
      uint32_t a_i1 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
      uint32_t a_i2 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i);
    }
    {
      uint32_t a_i = a[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
      uint32_t a_i0 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
      uint32_t a_i1 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
      uint32_t a_i2 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i);
    }
    uint32_t r = c;
    res[(uint32_t)8U + (uint32_t)0U] = r;
  }
  {
    uint32_t bj = b[1U];
    uint32_t *res_j = res + (uint32_t)1U;
    uint32_t c = (uint32_t)0U;
    {
      uint32_t a_i = a[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
      uint32_t a_i0 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
      uint32_t a_i1 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
      uint32_t a_i2 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i);
    }
    {
      uint32_t a_i = a[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
      uint32_t a_i0 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
      uint32_t a_i1 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
      uint32_t a_i2 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i);
    }
    uint32_t r = c;
    res[(uint32_t)8U + (uint32_t)1U] = r;
  }
  {
    uint32_t bj = b[2U];
    uint32_t *res_j = res + (uint32_t)2U;
    uint32_t c = (uint32_t)0U;
    {
      uint32_t a_i = a[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
      uint32_t a_i0 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
      uint32_t a_i1 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
      uint32_t a_i2 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i);
    }
    {
      uint32_t a_i = a[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
      uint32_t a_i0 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
      uint32_t a_i1 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
      uint32_t a_i2 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i);
    }
    uint32_t r = c;
    res[(uint32_t)8U + (uint32_t)2U] = r;
  }
  {
    uint32_t bj = b[3U];
    uint32_t *res_j = res + (uint32_t)3U;
    uint32_t c = (uint32_t)0U;
    {
      uint32_t a_i = a[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
      uint32_t a_i0 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
      uint32_t a_i1 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
      uint32_t a_i2 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i);
    }
    {
      uint32_t a_i = a[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
      uint32_t a_i0 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
      uint32_t a_i1 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
      uint32_t a_i2 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i);
    }
    uint32_t r = c;
    res[(uint32_t)8U + (uint32_t)3U] = r;
  }
  {
    uint32_t bj = b[4U];
    uint32_t *res_j = res + (uint32_t)4U;
    uint32_t c = (uint32_t)0U;
    {
      uint32_t a_i = a[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
      uint32_t a_i0 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
      uint32_t a_i1 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
      uint32_t a_i2 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i);
    }
    {
      uint32_t a_i = a[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
      uint32_t a_i0 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
      uint32_t a_i1 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
      uint32_t a_i2 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i);
    }
    uint32_t r = c;
    res[(uint32_t)8U + (uint32_t)4U] = r;
  }
  {
    uint32_t bj = b[5U];
    uint32_t *res_j = res + (uint32_t)5U;
    uint32_t c = (uint32_t)0U;
    {
      uint32_t a_i = a[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
      uint32_t a_i0 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
      uint32_t a_i1 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
      uint32_t a_i2 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i);
    }
    {
      uint32_t a_i = a[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
      uint32_t a_i0 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
      uint32_t a_i1 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
      uint32_t a_i2 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i);
    }
    uint32_t r = c;
    res[(uint32_t)8U + (uint32_t)5U] = r;
  }
  {
    uint32_t bj = b[6U];
    uint32_t *res_j = res + (uint32_t)6U;
    uint32_t c = (uint32_t)0U;
    {
      uint32_t a_i = a[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
      uint32_t a_i0 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
      uint32_t a_i1 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
      uint32_t a_i2 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i);
    }
    {
      uint32_t a_i = a[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
      uint32_t a_i0 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
      uint32_t a_i1 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
      uint32_t a_i2 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i);
    }
    uint32_t r = c;
    res[(uint32_t)8U + (uint32_t)6U] = r;
  }
  {
    uint32_t bj = b[7U];
    uint32_t *res_j = res + (uint32_t)7U;
    uint32_t c = (uint32_t)0U;
    {
      uint32_t a_i = a[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
      uint32_t a_i0 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
      uint32_t a_i1 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
      uint32_t a_i2 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i);
    }
    {
      uint32_t a_i = a[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
      uint32_t a_i0 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
      uint32_t a_i1 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
      uint32_t a_i2 = a[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i);
    }
    uint32_t r = c;
    res[(uint32_t)8U + (uint32_t)7U] = r;
  }
}

/*
Write `a * a` in `res`.

  The argument a is meant to be a 256-bit bignum, i.e. uint32_t[8].
  The outparam res is meant to be a 512-bit bignum, i.e. uint32_t[16].
*/
void Hacl_Bignum256_32_sqr(uint32_t *a, uint32_t *res)
{
  memset(res, 0U, (uint32_t)16U * sizeof (uint32_t));
  {
    uint32_t *ab = a;
    uint32_t a_j = a[0U];
    uint32_t *res_j = res;
    uint32_t c = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)0U / (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i0);
      uint32_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c, res_i1);
      uint32_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c, res_i2);
      uint32_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c, res_i);
    }
    for (uint32_t i = (uint32_t)0U / (uint32_t)4U * (uint32_t)4U; i < (uint32_t)0U; i++)
    {
      uint32_t a_i = ab[i];
      uint32_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i);
    }
    uint32_t r = c;
    res[(uint32_t)0U + (uint32_t)0U] = r;
  }
  {
    uint32_t *ab = a;
    uint32_t a_j = a[1U];
    uint32_t *res_j = res + (uint32_t)1U;
    uint32_t c = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U / (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i0);
      uint32_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c, res_i1);
      uint32_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c, res_i2);
      uint32_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c, res_i);
    }
    for (uint32_t i = (uint32_t)1U / (uint32_t)4U * (uint32_t)4U; i < (uint32_t)1U; i++)
    {
      uint32_t a_i = ab[i];
      uint32_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i);
    }
    uint32_t r = c;
    res[(uint32_t)1U + (uint32_t)1U] = r;
  }
  {
    uint32_t *ab = a;
    uint32_t a_j = a[2U];
    uint32_t *res_j = res + (uint32_t)2U;
    uint32_t c = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)2U / (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i0);
      uint32_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c, res_i1);
      uint32_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c, res_i2);
      uint32_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c, res_i);
    }
    for (uint32_t i = (uint32_t)2U / (uint32_t)4U * (uint32_t)4U; i < (uint32_t)2U; i++)
    {
      uint32_t a_i = ab[i];
      uint32_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i);
    }
    uint32_t r = c;
    res[(uint32_t)2U + (uint32_t)2U] = r;
  }
  {
    uint32_t *ab = a;
    uint32_t a_j = a[3U];
    uint32_t *res_j = res + (uint32_t)3U;
    uint32_t c = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)3U / (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i0);
      uint32_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c, res_i1);
      uint32_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c, res_i2);
      uint32_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c, res_i);
    }
    for (uint32_t i = (uint32_t)3U / (uint32_t)4U * (uint32_t)4U; i < (uint32_t)3U; i++)
    {
      uint32_t a_i = ab[i];
      uint32_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i);
    }
    uint32_t r = c;
    res[(uint32_t)3U + (uint32_t)3U] = r;
  }
  {
    uint32_t *ab = a;
    uint32_t a_j = a[4U];
    uint32_t *res_j = res + (uint32_t)4U;
    uint32_t c = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i0);
      uint32_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c, res_i1);
      uint32_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c, res_i2);
      uint32_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c, res_i);
    }
    for (uint32_t i = (uint32_t)4U / (uint32_t)4U * (uint32_t)4U; i < (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[i];
      uint32_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i);
    }
    uint32_t r = c;
    res[(uint32_t)4U + (uint32_t)4U] = r;
  }
  {
    uint32_t *ab = a;
    uint32_t a_j = a[5U];
    uint32_t *res_j = res + (uint32_t)5U;
    uint32_t c = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)5U / (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i0);
      uint32_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c, res_i1);
      uint32_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c, res_i2);
      uint32_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c, res_i);
    }
    for (uint32_t i = (uint32_t)5U / (uint32_t)4U * (uint32_t)4U; i < (uint32_t)5U; i++)
    {
      uint32_t a_i = ab[i];
      uint32_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i);
    }
    uint32_t r = c;
    res[(uint32_t)5U + (uint32_t)5U] = r;
  }
  {
    uint32_t *ab = a;
    uint32_t a_j = a[6U];
    uint32_t *res_j = res + (uint32_t)6U;
    uint32_t c = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)6U / (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i0);
      uint32_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c, res_i1);
      uint32_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c, res_i2);
      uint32_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c, res_i);
    }
    for (uint32_t i = (uint32_t)6U / (uint32_t)4U * (uint32_t)4U; i < (uint32_t)6U; i++)
    {
      uint32_t a_i = ab[i];
      uint32_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i);
    }
    uint32_t r = c;
    res[(uint32_t)6U + (uint32_t)6U] = r;
  }
  {
    uint32_t *ab = a;
    uint32_t a_j = a[7U];
    uint32_t *res_j = res + (uint32_t)7U;
    uint32_t c = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)7U / (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i0);
      uint32_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c, res_i1);
      uint32_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c, res_i2);
      uint32_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c, res_i);
    }
    for (uint32_t i = (uint32_t)7U / (uint32_t)4U * (uint32_t)4U; i < (uint32_t)7U; i++)
    {
      uint32_t a_i = ab[i];
      uint32_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i);
    }
    uint32_t r = c;
    res[(uint32_t)7U + (uint32_t)7U] = r;
  }
  uint32_t c0 = Hacl_Bignum_Addition_bn_add_eq_len_u32((uint32_t)16U, res, res, res);
  uint32_t tmp[16U] = { 0U };
  {
    uint64_t res1 = (uint64_t)a[0U] * (uint64_t)a[0U];
    uint32_t hi = (uint32_t)(res1 >> (uint32_t)32U);
    uint32_t lo = (uint32_t)res1;
    tmp[(uint32_t)2U * (uint32_t)0U] = lo;
    tmp[(uint32_t)2U * (uint32_t)0U + (uint32_t)1U] = hi;
  }
  {
    uint64_t res1 = (uint64_t)a[1U] * (uint64_t)a[1U];
    uint32_t hi = (uint32_t)(res1 >> (uint32_t)32U);
    uint32_t lo = (uint32_t)res1;
    tmp[(uint32_t)2U * (uint32_t)1U] = lo;
    tmp[(uint32_t)2U * (uint32_t)1U + (uint32_t)1U] = hi;
  }
  {
    uint64_t res1 = (uint64_t)a[2U] * (uint64_t)a[2U];
    uint32_t hi = (uint32_t)(res1 >> (uint32_t)32U);
    uint32_t lo = (uint32_t)res1;
    tmp[(uint32_t)2U * (uint32_t)2U] = lo;
    tmp[(uint32_t)2U * (uint32_t)2U + (uint32_t)1U] = hi;
  }
  {
    uint64_t res1 = (uint64_t)a[3U] * (uint64_t)a[3U];
    uint32_t hi = (uint32_t)(res1 >> (uint32_t)32U);
    uint32_t lo = (uint32_t)res1;
    tmp[(uint32_t)2U * (uint32_t)3U] = lo;
    tmp[(uint32_t)2U * (uint32_t)3U + (uint32_t)1U] = hi;
  }
  {
    uint64_t res1 = (uint64_t)a[4U] * (uint64_t)a[4U];
    uint32_t hi = (uint32_t)(res1 >> (uint32_t)32U);
    uint32_t lo = (uint32_t)res1;
    tmp[(uint32_t)2U * (uint32_t)4U] = lo;
    tmp[(uint32_t)2U * (uint32_t)4U + (uint32_t)1U] = hi;
  }
  {
    uint64_t res1 = (uint64_t)a[5U] * (uint64_t)a[5U];
    uint32_t hi = (uint32_t)(res1 >> (uint32_t)32U);
    uint32_t lo = (uint32_t)res1;
    tmp[(uint32_t)2U * (uint32_t)5U] = lo;
    tmp[(uint32_t)2U * (uint32_t)5U + (uint32_t)1U] = hi;
  }
  {
    uint64_t res1 = (uint64_t)a[6U] * (uint64_t)a[6U];
    uint32_t hi = (uint32_t)(res1 >> (uint32_t)32U);
    uint32_t lo = (uint32_t)res1;
    tmp[(uint32_t)2U * (uint32_t)6U] = lo;
    tmp[(uint32_t)2U * (uint32_t)6U + (uint32_t)1U] = hi;
  }
  {
    uint64_t res1 = (uint64_t)a[7U] * (uint64_t)a[7U];
    uint32_t hi = (uint32_t)(res1 >> (uint32_t)32U);
    uint32_t lo = (uint32_t)res1;
    tmp[(uint32_t)2U * (uint32_t)7U] = lo;
    tmp[(uint32_t)2U * (uint32_t)7U + (uint32_t)1U] = hi;
  }
  uint32_t c1 = Hacl_Bignum_Addition_bn_add_eq_len_u32((uint32_t)16U, res, tmp, res);
}

static inline void precompr2(uint32_t nBits, uint32_t *n, uint32_t *res)
{
  memset(res, 0U, (uint32_t)8U * sizeof (uint32_t));
  uint32_t i = nBits / (uint32_t)32U;
  uint32_t j = nBits % (uint32_t)32U;
  res[i] = res[i] | (uint32_t)1U << j;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)512U - nBits; i0++)
  {
    Hacl_Bignum256_32_add_mod(n, res, res, res);
  }
}

static inline void reduction(uint32_t *n, uint32_t nInv, uint32_t *c, uint32_t *res)
{
  uint32_t c0 = (uint32_t)0U;
  {
    uint32_t qj = nInv * c[0U];
    uint32_t *res_j0 = c;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + (uint32_t)8U + (uint32_t)0U;
    uint32_t res_j = c[(uint32_t)8U + (uint32_t)0U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
  }
  {
    uint32_t qj = nInv * c[1U];
    uint32_t *res_j0 = c + (uint32_t)1U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + (uint32_t)8U + (uint32_t)1U;
    uint32_t res_j = c[(uint32_t)8U + (uint32_t)1U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
  }
  {
    uint32_t qj = nInv * c[2U];
    uint32_t *res_j0 = c + (uint32_t)2U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + (uint32_t)8U + (uint32_t)2U;
    uint32_t res_j = c[(uint32_t)8U + (uint32_t)2U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
  }
  {
    uint32_t qj = nInv * c[3U];
    uint32_t *res_j0 = c + (uint32_t)3U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + (uint32_t)8U + (uint32_t)3U;
    uint32_t res_j = c[(uint32_t)8U + (uint32_t)3U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
  }
  {
    uint32_t qj = nInv * c[4U];
    uint32_t *res_j0 = c + (uint32_t)4U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + (uint32_t)8U + (uint32_t)4U;
    uint32_t res_j = c[(uint32_t)8U + (uint32_t)4U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
  }
  {
    uint32_t qj = nInv * c[5U];
    uint32_t *res_j0 = c + (uint32_t)5U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + (uint32_t)8U + (uint32_t)5U;
    uint32_t res_j = c[(uint32_t)8U + (uint32_t)5U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
  }
  {
    uint32_t qj = nInv * c[6U];
    uint32_t *res_j0 = c + (uint32_t)6U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + (uint32_t)8U + (uint32_t)6U;
    uint32_t res_j = c[(uint32_t)8U + (uint32_t)6U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
  }
  {
    uint32_t qj = nInv * c[7U];
    uint32_t *res_j0 = c + (uint32_t)7U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + (uint32_t)8U + (uint32_t)7U;
    uint32_t res_j = c[(uint32_t)8U + (uint32_t)7U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
  }
  memcpy(res, c + (uint32_t)8U, (uint32_t)8U * sizeof (uint32_t));
  uint32_t c00 = c0;
  uint32_t tmp[8U] = { 0U };
  uint32_t c1 = (uint32_t)0U;
  {
    uint32_t t1 = res[(uint32_t)4U * (uint32_t)0U];
    uint32_t t20 = n[(uint32_t)4U * (uint32_t)0U];
    uint32_t *res_i0 = tmp + (uint32_t)4U * (uint32_t)0U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t1, t20, res_i0);
    uint32_t t10 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint32_t t21 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint32_t *res_i1 = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t10, t21, res_i1);
    uint32_t t11 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint32_t t22 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint32_t *res_i2 = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t11, t22, res_i2);
    uint32_t t12 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint32_t t2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint32_t *res_i = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t12, t2, res_i);
  }
  {
    uint32_t t1 = res[(uint32_t)4U * (uint32_t)1U];
    uint32_t t20 = n[(uint32_t)4U * (uint32_t)1U];
    uint32_t *res_i0 = tmp + (uint32_t)4U * (uint32_t)1U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t1, t20, res_i0);
    uint32_t t10 = res[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
    uint32_t t21 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
    uint32_t *res_i1 = tmp + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t10, t21, res_i1);
    uint32_t t11 = res[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
    uint32_t t22 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
    uint32_t *res_i2 = tmp + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t11, t22, res_i2);
    uint32_t t12 = res[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
    uint32_t t2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
    uint32_t *res_i = tmp + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t12, t2, res_i);
  }
  uint32_t c10 = c1;
  uint32_t c2 = c00 - c10;
  {
    uint32_t *os = res;
    uint32_t x = (c2 & res[0U]) | (~c2 & tmp[0U]);
    os[0U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & res[1U]) | (~c2 & tmp[1U]);
    os[1U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & res[2U]) | (~c2 & tmp[2U]);
    os[2U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & res[3U]) | (~c2 & tmp[3U]);
    os[3U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & res[4U]) | (~c2 & tmp[4U]);
    os[4U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & res[5U]) | (~c2 & tmp[5U]);
    os[5U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & res[6U]) | (~c2 & tmp[6U]);
    os[6U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (c2 & res[7U]) | (~c2 & tmp[7U]);
    os[7U] = x;
  }
}

static inline void areduction(uint32_t *n, uint32_t nInv, uint32_t *c, uint32_t *res)
{
  uint32_t c0 = (uint32_t)0U;
  {
    uint32_t qj = nInv * c[0U];
    uint32_t *res_j0 = c;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + (uint32_t)8U + (uint32_t)0U;
    uint32_t res_j = c[(uint32_t)8U + (uint32_t)0U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
  }
  {
    uint32_t qj = nInv * c[1U];
    uint32_t *res_j0 = c + (uint32_t)1U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + (uint32_t)8U + (uint32_t)1U;
    uint32_t res_j = c[(uint32_t)8U + (uint32_t)1U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
  }
  {
    uint32_t qj = nInv * c[2U];
    uint32_t *res_j0 = c + (uint32_t)2U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + (uint32_t)8U + (uint32_t)2U;
    uint32_t res_j = c[(uint32_t)8U + (uint32_t)2U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
  }
  {
    uint32_t qj = nInv * c[3U];
    uint32_t *res_j0 = c + (uint32_t)3U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + (uint32_t)8U + (uint32_t)3U;
    uint32_t res_j = c[(uint32_t)8U + (uint32_t)3U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
  }
  {
    uint32_t qj = nInv * c[4U];
    uint32_t *res_j0 = c + (uint32_t)4U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + (uint32_t)8U + (uint32_t)4U;
    uint32_t res_j = c[(uint32_t)8U + (uint32_t)4U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
  }
  {
    uint32_t qj = nInv * c[5U];
    uint32_t *res_j0 = c + (uint32_t)5U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + (uint32_t)8U + (uint32_t)5U;
    uint32_t res_j = c[(uint32_t)8U + (uint32_t)5U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
  }
  {
    uint32_t qj = nInv * c[6U];
    uint32_t *res_j0 = c + (uint32_t)6U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + (uint32_t)8U + (uint32_t)6U;
    uint32_t res_j = c[(uint32_t)8U + (uint32_t)6U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
  }
  {
    uint32_t qj = nInv * c[7U];
    uint32_t *res_j0 = c + (uint32_t)7U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + (uint32_t)8U + (uint32_t)7U;
    uint32_t res_j = c[(uint32_t)8U + (uint32_t)7U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
  }
  memcpy(res, c + (uint32_t)8U, (uint32_t)8U * sizeof (uint32_t));
  uint32_t c00 = c0;
  uint32_t tmp[8U] = { 0U };
  uint32_t c1 = Hacl_Bignum256_32_sub(res, n, tmp);
  uint32_t m = (uint32_t)0U - c00;
  {
    uint32_t *os = res;
    uint32_t x = (m & tmp[0U]) | (~m & res[0U]);
    os[0U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (m & tmp[1U]) | (~m & res[1U]);
    os[1U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (m & tmp[2U]) | (~m & res[2U]);
    os[2U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (m & tmp[3U]) | (~m & res[3U]);
    os[3U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (m & tmp[4U]) | (~m & res[4U]);
    os[4U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (m & tmp[5U]) | (~m & res[5U]);
    os[5U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (m & tmp[6U]) | (~m & res[6U]);
    os[6U] = x;
  }
  {
    uint32_t *os = res;
    uint32_t x = (m & tmp[7U]) | (~m & res[7U]);
    os[7U] = x;
  }
}

static inline void
amont_mul(uint32_t *n, uint32_t nInv_u64, uint32_t *aM, uint32_t *bM, uint32_t *resM)
{
  uint32_t c[16U] = { 0U };
  memset(c, 0U, (uint32_t)16U * sizeof (uint32_t));
  {
    uint32_t bj = bM[0U];
    uint32_t *res_j = c;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = aM[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c1, res_i0);
      uint32_t a_i0 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c1, res_i1);
      uint32_t a_i1 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c1, res_i2);
      uint32_t a_i2 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c1, res_i);
    }
    {
      uint32_t a_i = aM[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c1, res_i0);
      uint32_t a_i0 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c1, res_i1);
      uint32_t a_i1 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c1, res_i2);
      uint32_t a_i2 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c1, res_i);
    }
    uint32_t r = c1;
    c[(uint32_t)8U + (uint32_t)0U] = r;
  }
  {
    uint32_t bj = bM[1U];
    uint32_t *res_j = c + (uint32_t)1U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = aM[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c1, res_i0);
      uint32_t a_i0 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c1, res_i1);
      uint32_t a_i1 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c1, res_i2);
      uint32_t a_i2 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c1, res_i);
    }
    {
      uint32_t a_i = aM[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c1, res_i0);
      uint32_t a_i0 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c1, res_i1);
      uint32_t a_i1 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c1, res_i2);
      uint32_t a_i2 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c1, res_i);
    }
    uint32_t r = c1;
    c[(uint32_t)8U + (uint32_t)1U] = r;
  }
  {
    uint32_t bj = bM[2U];
    uint32_t *res_j = c + (uint32_t)2U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = aM[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c1, res_i0);
      uint32_t a_i0 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c1, res_i1);
      uint32_t a_i1 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c1, res_i2);
      uint32_t a_i2 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c1, res_i);
    }
    {
      uint32_t a_i = aM[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c1, res_i0);
      uint32_t a_i0 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c1, res_i1);
      uint32_t a_i1 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c1, res_i2);
      uint32_t a_i2 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c1, res_i);
    }
    uint32_t r = c1;
    c[(uint32_t)8U + (uint32_t)2U] = r;
  }
  {
    uint32_t bj = bM[3U];
    uint32_t *res_j = c + (uint32_t)3U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = aM[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c1, res_i0);
      uint32_t a_i0 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c1, res_i1);
      uint32_t a_i1 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c1, res_i2);
      uint32_t a_i2 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c1, res_i);
    }
    {
      uint32_t a_i = aM[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c1, res_i0);
      uint32_t a_i0 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c1, res_i1);
      uint32_t a_i1 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c1, res_i2);
      uint32_t a_i2 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c1, res_i);
    }
    uint32_t r = c1;
    c[(uint32_t)8U + (uint32_t)3U] = r;
  }
  {
    uint32_t bj = bM[4U];
    uint32_t *res_j = c + (uint32_t)4U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = aM[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c1, res_i0);
      uint32_t a_i0 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c1, res_i1);
      uint32_t a_i1 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c1, res_i2);
      uint32_t a_i2 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c1, res_i);
    }
    {
      uint32_t a_i = aM[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c1, res_i0);
      uint32_t a_i0 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c1, res_i1);
      uint32_t a_i1 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c1, res_i2);
      uint32_t a_i2 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c1, res_i);
    }
    uint32_t r = c1;
    c[(uint32_t)8U + (uint32_t)4U] = r;
  }
  {
    uint32_t bj = bM[5U];
    uint32_t *res_j = c + (uint32_t)5U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = aM[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c1, res_i0);
      uint32_t a_i0 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c1, res_i1);
      uint32_t a_i1 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c1, res_i2);
      uint32_t a_i2 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c1, res_i);
    }
    {
      uint32_t a_i = aM[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c1, res_i0);
      uint32_t a_i0 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c1, res_i1);
      uint32_t a_i1 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c1, res_i2);
      uint32_t a_i2 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c1, res_i);
    }
    uint32_t r = c1;
    c[(uint32_t)8U + (uint32_t)5U] = r;
  }
  {
    uint32_t bj = bM[6U];
    uint32_t *res_j = c + (uint32_t)6U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = aM[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c1, res_i0);
      uint32_t a_i0 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c1, res_i1);
      uint32_t a_i1 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c1, res_i2);
      uint32_t a_i2 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c1, res_i);
    }
    {
      uint32_t a_i = aM[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c1, res_i0);
      uint32_t a_i0 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c1, res_i1);
      uint32_t a_i1 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c1, res_i2);
      uint32_t a_i2 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c1, res_i);
    }
    uint32_t r = c1;
    c[(uint32_t)8U + (uint32_t)6U] = r;
  }
  {
    uint32_t bj = bM[7U];
    uint32_t *res_j = c + (uint32_t)7U;
    uint32_t c1 = (uint32_t)0U;
    {
      uint32_t a_i = aM[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c1, res_i0);
      uint32_t a_i0 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c1, res_i1);
      uint32_t a_i1 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c1, res_i2);
      uint32_t a_i2 = aM[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c1, res_i);
    }
    {
      uint32_t a_i = aM[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c1, res_i0);
      uint32_t a_i0 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c1, res_i1);
      uint32_t a_i1 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c1, res_i2);
      uint32_t a_i2 = aM[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c1, res_i);
    }
    uint32_t r = c1;
    c[(uint32_t)8U + (uint32_t)7U] = r;
  }
  areduction(n, nInv_u64, c, resM);
}

static inline void amont_sqr(uint32_t *n, uint32_t nInv_u64, uint32_t *aM, uint32_t *resM)
{
  uint32_t c[16U] = { 0U };
  memset(c, 0U, (uint32_t)16U * sizeof (uint32_t));
  {
    uint32_t *ab = aM;
    uint32_t a_j = aM[0U];
    uint32_t *res_j = c;
    uint32_t c1 = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)0U / (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c1, res_i0);
      uint32_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c1, res_i1);
      uint32_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c1, res_i2);
      uint32_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c1, res_i);
    }
    for (uint32_t i = (uint32_t)0U / (uint32_t)4U * (uint32_t)4U; i < (uint32_t)0U; i++)
    {
      uint32_t a_i = ab[i];
      uint32_t *res_i = res_j + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c1, res_i);
    }
    uint32_t r = c1;
    c[(uint32_t)0U + (uint32_t)0U] = r;
  }
  {
    uint32_t *ab = aM;
    uint32_t a_j = aM[1U];
    uint32_t *res_j = c + (uint32_t)1U;
    uint32_t c1 = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U / (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c1, res_i0);
      uint32_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c1, res_i1);
      uint32_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c1, res_i2);
      uint32_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c1, res_i);
    }
    for (uint32_t i = (uint32_t)1U / (uint32_t)4U * (uint32_t)4U; i < (uint32_t)1U; i++)
    {
      uint32_t a_i = ab[i];
      uint32_t *res_i = res_j + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c1, res_i);
    }
    uint32_t r = c1;
    c[(uint32_t)1U + (uint32_t)1U] = r;
  }
  {
    uint32_t *ab = aM;
    uint32_t a_j = aM[2U];
    uint32_t *res_j = c + (uint32_t)2U;
    uint32_t c1 = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)2U / (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c1, res_i0);
      uint32_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c1, res_i1);
      uint32_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c1, res_i2);
      uint32_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c1, res_i);
    }
    for (uint32_t i = (uint32_t)2U / (uint32_t)4U * (uint32_t)4U; i < (uint32_t)2U; i++)
    {
      uint32_t a_i = ab[i];
      uint32_t *res_i = res_j + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c1, res_i);
    }
    uint32_t r = c1;
    c[(uint32_t)2U + (uint32_t)2U] = r;
  }
  {
    uint32_t *ab = aM;
    uint32_t a_j = aM[3U];
    uint32_t *res_j = c + (uint32_t)3U;
    uint32_t c1 = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)3U / (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c1, res_i0);
      uint32_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c1, res_i1);
      uint32_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c1, res_i2);
      uint32_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c1, res_i);
    }
    for (uint32_t i = (uint32_t)3U / (uint32_t)4U * (uint32_t)4U; i < (uint32_t)3U; i++)
    {
      uint32_t a_i = ab[i];
      uint32_t *res_i = res_j + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c1, res_i);
    }
    uint32_t r = c1;
    c[(uint32_t)3U + (uint32_t)3U] = r;
  }
  {
    uint32_t *ab = aM;
    uint32_t a_j = aM[4U];
    uint32_t *res_j = c + (uint32_t)4U;
    uint32_t c1 = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c1, res_i0);
      uint32_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c1, res_i1);
      uint32_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c1, res_i2);
      uint32_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c1, res_i);
    }
    for (uint32_t i = (uint32_t)4U / (uint32_t)4U * (uint32_t)4U; i < (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[i];
      uint32_t *res_i = res_j + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c1, res_i);
    }
    uint32_t r = c1;
    c[(uint32_t)4U + (uint32_t)4U] = r;
  }
  {
    uint32_t *ab = aM;
    uint32_t a_j = aM[5U];
    uint32_t *res_j = c + (uint32_t)5U;
    uint32_t c1 = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)5U / (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c1, res_i0);
      uint32_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c1, res_i1);
      uint32_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c1, res_i2);
      uint32_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c1, res_i);
    }
    for (uint32_t i = (uint32_t)5U / (uint32_t)4U * (uint32_t)4U; i < (uint32_t)5U; i++)
    {
      uint32_t a_i = ab[i];
      uint32_t *res_i = res_j + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c1, res_i);
    }
    uint32_t r = c1;
    c[(uint32_t)5U + (uint32_t)5U] = r;
  }
  {
    uint32_t *ab = aM;
    uint32_t a_j = aM[6U];
    uint32_t *res_j = c + (uint32_t)6U;
    uint32_t c1 = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)6U / (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c1, res_i0);
      uint32_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c1, res_i1);
      uint32_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c1, res_i2);
      uint32_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c1, res_i);
    }
    for (uint32_t i = (uint32_t)6U / (uint32_t)4U * (uint32_t)4U; i < (uint32_t)6U; i++)
    {
      uint32_t a_i = ab[i];
      uint32_t *res_i = res_j + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c1, res_i);
    }
    uint32_t r = c1;
    c[(uint32_t)6U + (uint32_t)6U] = r;
  }
  {
    uint32_t *ab = aM;
    uint32_t a_j = aM[7U];
    uint32_t *res_j = c + (uint32_t)7U;
    uint32_t c1 = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)7U / (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c1, res_i0);
      uint32_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c1, res_i1);
      uint32_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c1, res_i2);
      uint32_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c1, res_i);
    }
    for (uint32_t i = (uint32_t)7U / (uint32_t)4U * (uint32_t)4U; i < (uint32_t)7U; i++)
    {
      uint32_t a_i = ab[i];
      uint32_t *res_i = res_j + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c1, res_i);
    }
    uint32_t r = c1;
    c[(uint32_t)7U + (uint32_t)7U] = r;
  }
  uint32_t c0 = Hacl_Bignum_Addition_bn_add_eq_len_u32((uint32_t)16U, c, c, c);
  uint32_t tmp[16U] = { 0U };
  {
    uint64_t res = (uint64_t)aM[0U] * (uint64_t)aM[0U];
    uint32_t hi = (uint32_t)(res >> (uint32_t)32U);
    uint32_t lo = (uint32_t)res;
    tmp[(uint32_t)2U * (uint32_t)0U] = lo;
    tmp[(uint32_t)2U * (uint32_t)0U + (uint32_t)1U] = hi;
  }
  {
    uint64_t res = (uint64_t)aM[1U] * (uint64_t)aM[1U];
    uint32_t hi = (uint32_t)(res >> (uint32_t)32U);
    uint32_t lo = (uint32_t)res;
    tmp[(uint32_t)2U * (uint32_t)1U] = lo;
    tmp[(uint32_t)2U * (uint32_t)1U + (uint32_t)1U] = hi;
  }
  {
    uint64_t res = (uint64_t)aM[2U] * (uint64_t)aM[2U];
    uint32_t hi = (uint32_t)(res >> (uint32_t)32U);
    uint32_t lo = (uint32_t)res;
    tmp[(uint32_t)2U * (uint32_t)2U] = lo;
    tmp[(uint32_t)2U * (uint32_t)2U + (uint32_t)1U] = hi;
  }
  {
    uint64_t res = (uint64_t)aM[3U] * (uint64_t)aM[3U];
    uint32_t hi = (uint32_t)(res >> (uint32_t)32U);
    uint32_t lo = (uint32_t)res;
    tmp[(uint32_t)2U * (uint32_t)3U] = lo;
    tmp[(uint32_t)2U * (uint32_t)3U + (uint32_t)1U] = hi;
  }
  {
    uint64_t res = (uint64_t)aM[4U] * (uint64_t)aM[4U];
    uint32_t hi = (uint32_t)(res >> (uint32_t)32U);
    uint32_t lo = (uint32_t)res;
    tmp[(uint32_t)2U * (uint32_t)4U] = lo;
    tmp[(uint32_t)2U * (uint32_t)4U + (uint32_t)1U] = hi;
  }
  {
    uint64_t res = (uint64_t)aM[5U] * (uint64_t)aM[5U];
    uint32_t hi = (uint32_t)(res >> (uint32_t)32U);
    uint32_t lo = (uint32_t)res;
    tmp[(uint32_t)2U * (uint32_t)5U] = lo;
    tmp[(uint32_t)2U * (uint32_t)5U + (uint32_t)1U] = hi;
  }
  {
    uint64_t res = (uint64_t)aM[6U] * (uint64_t)aM[6U];
    uint32_t hi = (uint32_t)(res >> (uint32_t)32U);
    uint32_t lo = (uint32_t)res;
    tmp[(uint32_t)2U * (uint32_t)6U] = lo;
    tmp[(uint32_t)2U * (uint32_t)6U + (uint32_t)1U] = hi;
  }
  {
    uint64_t res = (uint64_t)aM[7U] * (uint64_t)aM[7U];
    uint32_t hi = (uint32_t)(res >> (uint32_t)32U);
    uint32_t lo = (uint32_t)res;
    tmp[(uint32_t)2U * (uint32_t)7U] = lo;
    tmp[(uint32_t)2U * (uint32_t)7U + (uint32_t)1U] = hi;
  }
  uint32_t c1 = Hacl_Bignum_Addition_bn_add_eq_len_u32((uint32_t)16U, c, tmp, c);
  areduction(n, nInv_u64, c, resM);
}

static inline void
bn_slow_precomp(uint32_t *n, uint32_t mu, uint32_t *r2, uint32_t *a, uint32_t *res)
{
  uint32_t a_mod[8U] = { 0U };
  uint32_t a1[16U] = { 0U };
  memcpy(a1, a, (uint32_t)16U * sizeof (uint32_t));
  uint32_t c0 = (uint32_t)0U;
  {
    uint32_t qj = mu * a1[0U];
    uint32_t *res_j0 = a1;
    uint32_t c = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c, res_i);
    }
    uint32_t r = c;
    uint32_t c1 = r;
    uint32_t *resb = a1 + (uint32_t)8U + (uint32_t)0U;
    uint32_t res_j = a1[(uint32_t)8U + (uint32_t)0U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c1, res_j, resb);
  }
  {
    uint32_t qj = mu * a1[1U];
    uint32_t *res_j0 = a1 + (uint32_t)1U;
    uint32_t c = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c, res_i);
    }
    uint32_t r = c;
    uint32_t c1 = r;
    uint32_t *resb = a1 + (uint32_t)8U + (uint32_t)1U;
    uint32_t res_j = a1[(uint32_t)8U + (uint32_t)1U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c1, res_j, resb);
  }
  {
    uint32_t qj = mu * a1[2U];
    uint32_t *res_j0 = a1 + (uint32_t)2U;
    uint32_t c = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c, res_i);
    }
    uint32_t r = c;
    uint32_t c1 = r;
    uint32_t *resb = a1 + (uint32_t)8U + (uint32_t)2U;
    uint32_t res_j = a1[(uint32_t)8U + (uint32_t)2U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c1, res_j, resb);
  }
  {
    uint32_t qj = mu * a1[3U];
    uint32_t *res_j0 = a1 + (uint32_t)3U;
    uint32_t c = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c, res_i);
    }
    uint32_t r = c;
    uint32_t c1 = r;
    uint32_t *resb = a1 + (uint32_t)8U + (uint32_t)3U;
    uint32_t res_j = a1[(uint32_t)8U + (uint32_t)3U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c1, res_j, resb);
  }
  {
    uint32_t qj = mu * a1[4U];
    uint32_t *res_j0 = a1 + (uint32_t)4U;
    uint32_t c = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c, res_i);
    }
    uint32_t r = c;
    uint32_t c1 = r;
    uint32_t *resb = a1 + (uint32_t)8U + (uint32_t)4U;
    uint32_t res_j = a1[(uint32_t)8U + (uint32_t)4U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c1, res_j, resb);
  }
  {
    uint32_t qj = mu * a1[5U];
    uint32_t *res_j0 = a1 + (uint32_t)5U;
    uint32_t c = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c, res_i);
    }
    uint32_t r = c;
    uint32_t c1 = r;
    uint32_t *resb = a1 + (uint32_t)8U + (uint32_t)5U;
    uint32_t res_j = a1[(uint32_t)8U + (uint32_t)5U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c1, res_j, resb);
  }
  {
    uint32_t qj = mu * a1[6U];
    uint32_t *res_j0 = a1 + (uint32_t)6U;
    uint32_t c = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c, res_i);
    }
    uint32_t r = c;
    uint32_t c1 = r;
    uint32_t *resb = a1 + (uint32_t)8U + (uint32_t)6U;
    uint32_t res_j = a1[(uint32_t)8U + (uint32_t)6U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c1, res_j, resb);
  }
  {
    uint32_t qj = mu * a1[7U];
    uint32_t *res_j0 = a1 + (uint32_t)7U;
    uint32_t c = (uint32_t)0U;
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c, res_i);
    }
    {
      uint32_t a_i = n[(uint32_t)4U * (uint32_t)1U];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * (uint32_t)1U + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)1U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c, res_i);
    }
    uint32_t r = c;
    uint32_t c1 = r;
    uint32_t *resb = a1 + (uint32_t)8U + (uint32_t)7U;
    uint32_t res_j = a1[(uint32_t)8U + (uint32_t)7U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c1, res_j, resb);
  }
  memcpy(a_mod, a1 + (uint32_t)8U, (uint32_t)8U * sizeof (uint32_t));
  uint32_t c00 = c0;
  uint32_t tmp[8U] = { 0U };
  uint32_t c1 = Hacl_Bignum256_32_sub(a_mod, n, tmp);
  uint32_t m = (uint32_t)0U - c00;
  {
    uint32_t *os = a_mod;
    uint32_t x = (m & tmp[0U]) | (~m & a_mod[0U]);
    os[0U] = x;
  }
  {
    uint32_t *os = a_mod;
    uint32_t x = (m & tmp[1U]) | (~m & a_mod[1U]);
    os[1U] = x;
  }
  {
    uint32_t *os = a_mod;
    uint32_t x = (m & tmp[2U]) | (~m & a_mod[2U]);
    os[2U] = x;
  }
  {
    uint32_t *os = a_mod;
    uint32_t x = (m & tmp[3U]) | (~m & a_mod[3U]);
    os[3U] = x;
  }
  {
    uint32_t *os = a_mod;
    uint32_t x = (m & tmp[4U]) | (~m & a_mod[4U]);
    os[4U] = x;
  }
  {
    uint32_t *os = a_mod;
    uint32_t x = (m & tmp[5U]) | (~m & a_mod[5U]);
    os[5U] = x;
  }
  {
    uint32_t *os = a_mod;
    uint32_t x = (m & tmp[6U]) | (~m & a_mod[6U]);
    os[6U] = x;
  }
  {
    uint32_t *os = a_mod;
    uint32_t x = (m & tmp[7U]) | (~m & a_mod[7U]);
    os[7U] = x;
  }
  uint32_t c[16U] = { 0U };
  Hacl_Bignum256_32_mul(a_mod, r2, c);
  reduction(n, mu, c, res);
}

/*
Write `a mod n` in `res`.

  The argument a is meant to be a 512-bit bignum, i.e. uint32_t[16].
  The argument n and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • 1 < n
   • n % 2 = 1
*/
bool Hacl_Bignum256_32_mod(uint32_t *n, uint32_t *a, uint32_t *res)
{
  uint32_t one[8U] = { 0U };
  memset(one, 0U, (uint32_t)8U * sizeof (uint32_t));
  one[0U] = (uint32_t)1U;
  uint32_t bit0 = n[0U] & (uint32_t)1U;
  uint32_t m0 = (uint32_t)0U - bit0;
  uint32_t acc = (uint32_t)0U;
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[0U], n[0U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[0U], n[0U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[1U], n[1U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[1U], n[1U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[2U], n[2U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[2U], n[2U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[3U], n[3U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[3U], n[3U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[4U], n[4U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[4U], n[4U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[5U], n[5U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[5U], n[5U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[6U], n[6U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[6U], n[6U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[7U], n[7U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[7U], n[7U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  uint32_t m1 = acc;
  uint32_t is_valid_m = m0 & m1;
  uint32_t nBits = (uint32_t)32U * Hacl_Bignum_Lib_bn_get_top_index_u32((uint32_t)8U, n);
  if (is_valid_m == (uint32_t)0xFFFFFFFFU)
  {
    uint32_t r2[8U] = { 0U };
    precompr2(nBits, n, r2);
    uint32_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint32(n[0U]);
    bn_slow_precomp(n, mu, r2, a, res);
  }
  else
  {
    memset(res, 0U, (uint32_t)8U * sizeof (uint32_t));
  }
  return is_valid_m == (uint32_t)0xFFFFFFFFU;
}

static uint32_t exp_check(uint32_t *n, uint32_t *a, uint32_t bBits, uint32_t *b)
{
  uint32_t one[8U] = { 0U };
  memset(one, 0U, (uint32_t)8U * sizeof (uint32_t));
  one[0U] = (uint32_t)1U;
  uint32_t bit0 = n[0U] & (uint32_t)1U;
  uint32_t m0 = (uint32_t)0U - bit0;
  uint32_t acc0 = (uint32_t)0U;
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[0U], n[0U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[0U], n[0U]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[1U], n[1U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[1U], n[1U]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[2U], n[2U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[2U], n[2U]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[3U], n[3U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[3U], n[3U]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[4U], n[4U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[4U], n[4U]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[5U], n[5U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[5U], n[5U]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[6U], n[6U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[6U], n[6U]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[7U], n[7U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[7U], n[7U]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  uint32_t m10 = acc0;
  uint32_t m00 = m0 & m10;
  uint32_t bLen;
  if (bBits == (uint32_t)0U)
  {
    bLen = (uint32_t)1U;
  }
  else
  {
    bLen = (bBits - (uint32_t)1U) / (uint32_t)32U + (uint32_t)1U;
  }
  uint32_t m1;
  if (bBits < (uint32_t)32U * bLen)
  {
    KRML_CHECK_SIZE(sizeof (uint32_t), bLen);
    uint32_t b2[bLen];
    memset(b2, 0U, bLen * sizeof (uint32_t));
    uint32_t i0 = bBits / (uint32_t)32U;
    uint32_t j = bBits % (uint32_t)32U;
    b2[i0] = b2[i0] | (uint32_t)1U << j;
    uint32_t acc = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < bLen; i++)
    {
      uint32_t beq = FStar_UInt32_eq_mask(b[i], b2[i]);
      uint32_t blt = ~FStar_UInt32_gte_mask(b[i], b2[i]);
      acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
    }
    uint32_t res = acc;
    m1 = res;
  }
  else
  {
    m1 = (uint32_t)0xFFFFFFFFU;
  }
  uint32_t acc = (uint32_t)0U;
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[0U], n[0U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[0U], n[0U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[1U], n[1U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[1U], n[1U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[2U], n[2U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[2U], n[2U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[3U], n[3U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[3U], n[3U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[4U], n[4U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[4U], n[4U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[5U], n[5U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[5U], n[5U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[6U], n[6U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[6U], n[6U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[7U], n[7U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[7U], n[7U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  uint32_t m2 = acc;
  uint32_t m = m1 & m2;
  return m00 & m;
}

static inline void
exp_vartime_precomp(
  uint32_t *n,
  uint32_t mu,
  uint32_t *r2,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  if (bBits < (uint32_t)200U)
  {
    uint32_t aM[8U] = { 0U };
    uint32_t c[16U] = { 0U };
    Hacl_Bignum256_32_mul(a, r2, c);
    reduction(n, mu, c, aM);
    uint32_t resM[8U] = { 0U };
    uint32_t tmp0[16U] = { 0U };
    memcpy(tmp0, r2, (uint32_t)8U * sizeof (uint32_t));
    reduction(n, mu, tmp0, resM);
    for (uint32_t i = (uint32_t)0U; i < bBits; i++)
    {
      uint32_t i1 = i / (uint32_t)32U;
      uint32_t j = i % (uint32_t)32U;
      uint32_t tmp = b[i1];
      uint32_t bit = tmp >> j & (uint32_t)1U;
      if (!(bit == (uint32_t)0U))
      {
        amont_mul(n, mu, resM, aM, resM);
      }
      amont_sqr(n, mu, aM, aM);
    }
    uint32_t tmp[16U] = { 0U };
    memcpy(tmp, resM, (uint32_t)8U * sizeof (uint32_t));
    reduction(n, mu, tmp, res);
    return;
  }
  uint32_t aM[8U] = { 0U };
  uint32_t c[16U] = { 0U };
  Hacl_Bignum256_32_mul(a, r2, c);
  reduction(n, mu, c, aM);
  uint32_t resM[8U] = { 0U };
  uint32_t bLen;
  if (bBits == (uint32_t)0U)
  {
    bLen = (uint32_t)1U;
  }
  else
  {
    bLen = (bBits - (uint32_t)1U) / (uint32_t)32U + (uint32_t)1U;
  }
  uint32_t tmp[16U] = { 0U };
  memcpy(tmp, r2, (uint32_t)8U * sizeof (uint32_t));
  reduction(n, mu, tmp, resM);
  uint32_t table[128U] = { 0U };
  memcpy(table, resM, (uint32_t)8U * sizeof (uint32_t));
  uint32_t *t1 = table + (uint32_t)8U;
  memcpy(t1, aM, (uint32_t)8U * sizeof (uint32_t));
  {
    uint32_t *t11 = table + (uint32_t)0U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)0U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)1U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)1U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)2U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)2U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)3U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)3U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)4U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)4U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)5U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)5U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)6U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)6U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)7U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)7U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)8U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)8U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)9U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)9U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)10U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)10U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)11U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)11U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)12U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)12U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)13U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)13U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)14U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)14U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  if (bBits % (uint32_t)4U != (uint32_t)0U)
  {
    uint32_t mask_l = (uint32_t)16U - (uint32_t)1U;
    uint32_t i = bBits / (uint32_t)4U * (uint32_t)4U / (uint32_t)32U;
    uint32_t j = bBits / (uint32_t)4U * (uint32_t)4U % (uint32_t)32U;
    uint32_t p1 = b[i] >> j;
    uint32_t ite;
    if (i + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i + (uint32_t)1U] << ((uint32_t)32U - j);
    }
    else
    {
      ite = p1;
    }
    uint32_t bits_c = ite & mask_l;
    uint32_t bits_l32 = bits_c;
    uint32_t *a_bits_l = table + bits_l32 * (uint32_t)8U;
    memcpy(resM, a_bits_l, (uint32_t)8U * sizeof (uint32_t));
  }
  for (uint32_t i = (uint32_t)0U; i < bBits / (uint32_t)4U; i++)
  {
    {
      amont_sqr(n, mu, resM, resM);
    }
    {
      amont_sqr(n, mu, resM, resM);
    }
    {
      amont_sqr(n, mu, resM, resM);
    }
    {
      amont_sqr(n, mu, resM, resM);
    }
    uint32_t bk = bBits - bBits % (uint32_t)4U;
    uint32_t mask_l = (uint32_t)16U - (uint32_t)1U;
    uint32_t i1 = (bk - (uint32_t)4U * i - (uint32_t)4U) / (uint32_t)32U;
    uint32_t j = (bk - (uint32_t)4U * i - (uint32_t)4U) % (uint32_t)32U;
    uint32_t p1 = b[i1] >> j;
    uint32_t ite;
    if (i1 + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i1 + (uint32_t)1U] << ((uint32_t)32U - j);
    }
    else
    {
      ite = p1;
    }
    uint32_t bits_l = ite & mask_l;
    uint32_t a_bits_l[8U] = { 0U };
    uint32_t bits_l32 = bits_l;
    uint32_t *a_bits_l1 = table + bits_l32 * (uint32_t)8U;
    memcpy(a_bits_l, a_bits_l1, (uint32_t)8U * sizeof (uint32_t));
    amont_mul(n, mu, resM, a_bits_l, resM);
  }
  uint32_t tmp0[16U] = { 0U };
  memcpy(tmp0, resM, (uint32_t)8U * sizeof (uint32_t));
  reduction(n, mu, tmp0, res);
}

static inline void
exp_consttime_precomp(
  uint32_t *n,
  uint32_t mu,
  uint32_t *r2,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  if (bBits < (uint32_t)200U)
  {
    uint32_t aM[8U] = { 0U };
    uint32_t c[16U] = { 0U };
    Hacl_Bignum256_32_mul(a, r2, c);
    reduction(n, mu, c, aM);
    uint32_t resM[8U] = { 0U };
    uint32_t tmp0[16U] = { 0U };
    memcpy(tmp0, r2, (uint32_t)8U * sizeof (uint32_t));
    reduction(n, mu, tmp0, resM);
    uint32_t sw = (uint32_t)0U;
    for (uint32_t i0 = (uint32_t)0U; i0 < bBits; i0++)
    {
      uint32_t i1 = (bBits - i0 - (uint32_t)1U) / (uint32_t)32U;
      uint32_t j = (bBits - i0 - (uint32_t)1U) % (uint32_t)32U;
      uint32_t tmp = b[i1];
      uint32_t bit = tmp >> j & (uint32_t)1U;
      uint32_t sw1 = bit ^ sw;
      {
        uint32_t dummy = ((uint32_t)0U - sw1) & (resM[0U] ^ aM[0U]);
        resM[0U] = resM[0U] ^ dummy;
        aM[0U] = aM[0U] ^ dummy;
      }
      {
        uint32_t dummy = ((uint32_t)0U - sw1) & (resM[1U] ^ aM[1U]);
        resM[1U] = resM[1U] ^ dummy;
        aM[1U] = aM[1U] ^ dummy;
      }
      {
        uint32_t dummy = ((uint32_t)0U - sw1) & (resM[2U] ^ aM[2U]);
        resM[2U] = resM[2U] ^ dummy;
        aM[2U] = aM[2U] ^ dummy;
      }
      {
        uint32_t dummy = ((uint32_t)0U - sw1) & (resM[3U] ^ aM[3U]);
        resM[3U] = resM[3U] ^ dummy;
        aM[3U] = aM[3U] ^ dummy;
      }
      {
        uint32_t dummy = ((uint32_t)0U - sw1) & (resM[4U] ^ aM[4U]);
        resM[4U] = resM[4U] ^ dummy;
        aM[4U] = aM[4U] ^ dummy;
      }
      {
        uint32_t dummy = ((uint32_t)0U - sw1) & (resM[5U] ^ aM[5U]);
        resM[5U] = resM[5U] ^ dummy;
        aM[5U] = aM[5U] ^ dummy;
      }
      {
        uint32_t dummy = ((uint32_t)0U - sw1) & (resM[6U] ^ aM[6U]);
        resM[6U] = resM[6U] ^ dummy;
        aM[6U] = aM[6U] ^ dummy;
      }
      {
        uint32_t dummy = ((uint32_t)0U - sw1) & (resM[7U] ^ aM[7U]);
        resM[7U] = resM[7U] ^ dummy;
        aM[7U] = aM[7U] ^ dummy;
      }
      amont_mul(n, mu, aM, resM, aM);
      amont_sqr(n, mu, resM, resM);
      sw = bit;
    }
    uint32_t sw0 = sw;
    {
      uint32_t dummy = ((uint32_t)0U - sw0) & (resM[0U] ^ aM[0U]);
      resM[0U] = resM[0U] ^ dummy;
      aM[0U] = aM[0U] ^ dummy;
    }
    {
      uint32_t dummy = ((uint32_t)0U - sw0) & (resM[1U] ^ aM[1U]);
      resM[1U] = resM[1U] ^ dummy;
      aM[1U] = aM[1U] ^ dummy;
    }
    {
      uint32_t dummy = ((uint32_t)0U - sw0) & (resM[2U] ^ aM[2U]);
      resM[2U] = resM[2U] ^ dummy;
      aM[2U] = aM[2U] ^ dummy;
    }
    {
      uint32_t dummy = ((uint32_t)0U - sw0) & (resM[3U] ^ aM[3U]);
      resM[3U] = resM[3U] ^ dummy;
      aM[3U] = aM[3U] ^ dummy;
    }
    {
      uint32_t dummy = ((uint32_t)0U - sw0) & (resM[4U] ^ aM[4U]);
      resM[4U] = resM[4U] ^ dummy;
      aM[4U] = aM[4U] ^ dummy;
    }
    {
      uint32_t dummy = ((uint32_t)0U - sw0) & (resM[5U] ^ aM[5U]);
      resM[5U] = resM[5U] ^ dummy;
      aM[5U] = aM[5U] ^ dummy;
    }
    {
      uint32_t dummy = ((uint32_t)0U - sw0) & (resM[6U] ^ aM[6U]);
      resM[6U] = resM[6U] ^ dummy;
      aM[6U] = aM[6U] ^ dummy;
    }
    {
      uint32_t dummy = ((uint32_t)0U - sw0) & (resM[7U] ^ aM[7U]);
      resM[7U] = resM[7U] ^ dummy;
      aM[7U] = aM[7U] ^ dummy;
    }
    uint32_t tmp[16U] = { 0U };
    memcpy(tmp, resM, (uint32_t)8U * sizeof (uint32_t));
    reduction(n, mu, tmp, res);
    return;
  }
  uint32_t aM[8U] = { 0U };
  uint32_t c0[16U] = { 0U };
  Hacl_Bignum256_32_mul(a, r2, c0);
  reduction(n, mu, c0, aM);
  uint32_t resM[8U] = { 0U };
  uint32_t bLen;
  if (bBits == (uint32_t)0U)
  {
    bLen = (uint32_t)1U;
  }
  else
  {
    bLen = (bBits - (uint32_t)1U) / (uint32_t)32U + (uint32_t)1U;
  }
  uint32_t tmp[16U] = { 0U };
  memcpy(tmp, r2, (uint32_t)8U * sizeof (uint32_t));
  reduction(n, mu, tmp, resM);
  uint32_t table[128U] = { 0U };
  memcpy(table, resM, (uint32_t)8U * sizeof (uint32_t));
  uint32_t *t1 = table + (uint32_t)8U;
  memcpy(t1, aM, (uint32_t)8U * sizeof (uint32_t));
  {
    uint32_t *t11 = table + (uint32_t)0U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)0U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)1U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)1U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)2U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)2U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)3U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)3U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)4U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)4U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)5U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)5U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)6U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)6U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)7U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)7U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)8U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)8U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)9U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)9U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)10U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)10U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)11U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)11U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)12U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)12U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)13U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)13U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  {
    uint32_t *t11 = table + (uint32_t)14U * (uint32_t)8U;
    uint32_t *t2 = table + (uint32_t)14U * (uint32_t)8U + (uint32_t)8U;
    amont_mul(n, mu, aM, t11, t2);
  }
  if (bBits % (uint32_t)4U != (uint32_t)0U)
  {
    uint32_t mask_l = (uint32_t)16U - (uint32_t)1U;
    uint32_t i0 = bBits / (uint32_t)4U * (uint32_t)4U / (uint32_t)32U;
    uint32_t j = bBits / (uint32_t)4U * (uint32_t)4U % (uint32_t)32U;
    uint32_t p1 = b[i0] >> j;
    uint32_t ite;
    if (i0 + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i0 + (uint32_t)1U] << ((uint32_t)32U - j);
    }
    else
    {
      ite = p1;
    }
    uint32_t bits_c = ite & mask_l;
    memcpy(resM, table, (uint32_t)8U * sizeof (uint32_t));
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_c, (uint32_t)0U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)0U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[0U]) | (~c & resM[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[1U]) | (~c & resM[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[2U]) | (~c & resM[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[3U]) | (~c & resM[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[4U]) | (~c & resM[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[5U]) | (~c & resM[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[6U]) | (~c & resM[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[7U]) | (~c & resM[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_c, (uint32_t)1U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)1U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[0U]) | (~c & resM[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[1U]) | (~c & resM[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[2U]) | (~c & resM[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[3U]) | (~c & resM[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[4U]) | (~c & resM[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[5U]) | (~c & resM[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[6U]) | (~c & resM[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[7U]) | (~c & resM[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_c, (uint32_t)2U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)2U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[0U]) | (~c & resM[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[1U]) | (~c & resM[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[2U]) | (~c & resM[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[3U]) | (~c & resM[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[4U]) | (~c & resM[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[5U]) | (~c & resM[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[6U]) | (~c & resM[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[7U]) | (~c & resM[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_c, (uint32_t)3U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)3U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[0U]) | (~c & resM[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[1U]) | (~c & resM[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[2U]) | (~c & resM[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[3U]) | (~c & resM[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[4U]) | (~c & resM[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[5U]) | (~c & resM[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[6U]) | (~c & resM[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[7U]) | (~c & resM[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_c, (uint32_t)4U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)4U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[0U]) | (~c & resM[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[1U]) | (~c & resM[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[2U]) | (~c & resM[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[3U]) | (~c & resM[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[4U]) | (~c & resM[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[5U]) | (~c & resM[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[6U]) | (~c & resM[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[7U]) | (~c & resM[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_c, (uint32_t)5U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)5U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[0U]) | (~c & resM[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[1U]) | (~c & resM[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[2U]) | (~c & resM[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[3U]) | (~c & resM[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[4U]) | (~c & resM[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[5U]) | (~c & resM[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[6U]) | (~c & resM[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[7U]) | (~c & resM[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_c, (uint32_t)6U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)6U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[0U]) | (~c & resM[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[1U]) | (~c & resM[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[2U]) | (~c & resM[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[3U]) | (~c & resM[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[4U]) | (~c & resM[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[5U]) | (~c & resM[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[6U]) | (~c & resM[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[7U]) | (~c & resM[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_c, (uint32_t)7U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)7U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[0U]) | (~c & resM[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[1U]) | (~c & resM[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[2U]) | (~c & resM[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[3U]) | (~c & resM[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[4U]) | (~c & resM[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[5U]) | (~c & resM[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[6U]) | (~c & resM[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[7U]) | (~c & resM[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_c, (uint32_t)8U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)8U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[0U]) | (~c & resM[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[1U]) | (~c & resM[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[2U]) | (~c & resM[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[3U]) | (~c & resM[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[4U]) | (~c & resM[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[5U]) | (~c & resM[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[6U]) | (~c & resM[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[7U]) | (~c & resM[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_c, (uint32_t)9U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)9U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[0U]) | (~c & resM[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[1U]) | (~c & resM[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[2U]) | (~c & resM[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[3U]) | (~c & resM[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[4U]) | (~c & resM[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[5U]) | (~c & resM[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[6U]) | (~c & resM[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[7U]) | (~c & resM[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_c, (uint32_t)10U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)10U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[0U]) | (~c & resM[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[1U]) | (~c & resM[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[2U]) | (~c & resM[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[3U]) | (~c & resM[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[4U]) | (~c & resM[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[5U]) | (~c & resM[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[6U]) | (~c & resM[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[7U]) | (~c & resM[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_c, (uint32_t)11U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)11U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[0U]) | (~c & resM[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[1U]) | (~c & resM[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[2U]) | (~c & resM[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[3U]) | (~c & resM[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[4U]) | (~c & resM[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[5U]) | (~c & resM[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[6U]) | (~c & resM[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[7U]) | (~c & resM[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_c, (uint32_t)12U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)12U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[0U]) | (~c & resM[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[1U]) | (~c & resM[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[2U]) | (~c & resM[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[3U]) | (~c & resM[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[4U]) | (~c & resM[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[5U]) | (~c & resM[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[6U]) | (~c & resM[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[7U]) | (~c & resM[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_c, (uint32_t)13U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)13U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[0U]) | (~c & resM[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[1U]) | (~c & resM[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[2U]) | (~c & resM[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[3U]) | (~c & resM[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[4U]) | (~c & resM[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[5U]) | (~c & resM[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[6U]) | (~c & resM[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[7U]) | (~c & resM[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_c, (uint32_t)14U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)14U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[0U]) | (~c & resM[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[1U]) | (~c & resM[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[2U]) | (~c & resM[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[3U]) | (~c & resM[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[4U]) | (~c & resM[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[5U]) | (~c & resM[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[6U]) | (~c & resM[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[7U]) | (~c & resM[7U]);
        os[7U] = x;
      }
    }
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < bBits / (uint32_t)4U; i0++)
  {
    {
      amont_sqr(n, mu, resM, resM);
    }
    {
      amont_sqr(n, mu, resM, resM);
    }
    {
      amont_sqr(n, mu, resM, resM);
    }
    {
      amont_sqr(n, mu, resM, resM);
    }
    uint32_t bk = bBits - bBits % (uint32_t)4U;
    uint32_t mask_l = (uint32_t)16U - (uint32_t)1U;
    uint32_t i1 = (bk - (uint32_t)4U * i0 - (uint32_t)4U) / (uint32_t)32U;
    uint32_t j = (bk - (uint32_t)4U * i0 - (uint32_t)4U) % (uint32_t)32U;
    uint32_t p1 = b[i1] >> j;
    uint32_t ite;
    if (i1 + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i1 + (uint32_t)1U] << ((uint32_t)32U - j);
    }
    else
    {
      ite = p1;
    }
    uint32_t bits_l = ite & mask_l;
    uint32_t a_bits_l[8U] = { 0U };
    memcpy(a_bits_l, table, (uint32_t)8U * sizeof (uint32_t));
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_l, (uint32_t)0U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)0U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[0U]) | (~c & a_bits_l[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[1U]) | (~c & a_bits_l[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[2U]) | (~c & a_bits_l[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[3U]) | (~c & a_bits_l[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[4U]) | (~c & a_bits_l[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[5U]) | (~c & a_bits_l[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[6U]) | (~c & a_bits_l[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[7U]) | (~c & a_bits_l[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_l, (uint32_t)1U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)1U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[0U]) | (~c & a_bits_l[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[1U]) | (~c & a_bits_l[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[2U]) | (~c & a_bits_l[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[3U]) | (~c & a_bits_l[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[4U]) | (~c & a_bits_l[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[5U]) | (~c & a_bits_l[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[6U]) | (~c & a_bits_l[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[7U]) | (~c & a_bits_l[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_l, (uint32_t)2U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)2U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[0U]) | (~c & a_bits_l[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[1U]) | (~c & a_bits_l[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[2U]) | (~c & a_bits_l[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[3U]) | (~c & a_bits_l[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[4U]) | (~c & a_bits_l[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[5U]) | (~c & a_bits_l[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[6U]) | (~c & a_bits_l[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[7U]) | (~c & a_bits_l[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_l, (uint32_t)3U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)3U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[0U]) | (~c & a_bits_l[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[1U]) | (~c & a_bits_l[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[2U]) | (~c & a_bits_l[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[3U]) | (~c & a_bits_l[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[4U]) | (~c & a_bits_l[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[5U]) | (~c & a_bits_l[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[6U]) | (~c & a_bits_l[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[7U]) | (~c & a_bits_l[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_l, (uint32_t)4U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)4U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[0U]) | (~c & a_bits_l[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[1U]) | (~c & a_bits_l[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[2U]) | (~c & a_bits_l[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[3U]) | (~c & a_bits_l[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[4U]) | (~c & a_bits_l[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[5U]) | (~c & a_bits_l[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[6U]) | (~c & a_bits_l[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[7U]) | (~c & a_bits_l[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_l, (uint32_t)5U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)5U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[0U]) | (~c & a_bits_l[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[1U]) | (~c & a_bits_l[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[2U]) | (~c & a_bits_l[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[3U]) | (~c & a_bits_l[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[4U]) | (~c & a_bits_l[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[5U]) | (~c & a_bits_l[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[6U]) | (~c & a_bits_l[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[7U]) | (~c & a_bits_l[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_l, (uint32_t)6U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)6U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[0U]) | (~c & a_bits_l[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[1U]) | (~c & a_bits_l[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[2U]) | (~c & a_bits_l[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[3U]) | (~c & a_bits_l[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[4U]) | (~c & a_bits_l[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[5U]) | (~c & a_bits_l[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[6U]) | (~c & a_bits_l[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[7U]) | (~c & a_bits_l[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_l, (uint32_t)7U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)7U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[0U]) | (~c & a_bits_l[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[1U]) | (~c & a_bits_l[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[2U]) | (~c & a_bits_l[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[3U]) | (~c & a_bits_l[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[4U]) | (~c & a_bits_l[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[5U]) | (~c & a_bits_l[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[6U]) | (~c & a_bits_l[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[7U]) | (~c & a_bits_l[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_l, (uint32_t)8U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)8U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[0U]) | (~c & a_bits_l[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[1U]) | (~c & a_bits_l[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[2U]) | (~c & a_bits_l[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[3U]) | (~c & a_bits_l[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[4U]) | (~c & a_bits_l[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[5U]) | (~c & a_bits_l[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[6U]) | (~c & a_bits_l[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[7U]) | (~c & a_bits_l[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_l, (uint32_t)9U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)9U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[0U]) | (~c & a_bits_l[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[1U]) | (~c & a_bits_l[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[2U]) | (~c & a_bits_l[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[3U]) | (~c & a_bits_l[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[4U]) | (~c & a_bits_l[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[5U]) | (~c & a_bits_l[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[6U]) | (~c & a_bits_l[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[7U]) | (~c & a_bits_l[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_l, (uint32_t)10U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)10U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[0U]) | (~c & a_bits_l[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[1U]) | (~c & a_bits_l[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[2U]) | (~c & a_bits_l[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[3U]) | (~c & a_bits_l[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[4U]) | (~c & a_bits_l[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[5U]) | (~c & a_bits_l[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[6U]) | (~c & a_bits_l[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[7U]) | (~c & a_bits_l[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_l, (uint32_t)11U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)11U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[0U]) | (~c & a_bits_l[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[1U]) | (~c & a_bits_l[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[2U]) | (~c & a_bits_l[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[3U]) | (~c & a_bits_l[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[4U]) | (~c & a_bits_l[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[5U]) | (~c & a_bits_l[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[6U]) | (~c & a_bits_l[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[7U]) | (~c & a_bits_l[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_l, (uint32_t)12U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)12U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[0U]) | (~c & a_bits_l[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[1U]) | (~c & a_bits_l[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[2U]) | (~c & a_bits_l[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[3U]) | (~c & a_bits_l[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[4U]) | (~c & a_bits_l[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[5U]) | (~c & a_bits_l[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[6U]) | (~c & a_bits_l[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[7U]) | (~c & a_bits_l[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_l, (uint32_t)13U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)13U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[0U]) | (~c & a_bits_l[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[1U]) | (~c & a_bits_l[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[2U]) | (~c & a_bits_l[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[3U]) | (~c & a_bits_l[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[4U]) | (~c & a_bits_l[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[5U]) | (~c & a_bits_l[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[6U]) | (~c & a_bits_l[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[7U]) | (~c & a_bits_l[7U]);
        os[7U] = x;
      }
    }
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_l, (uint32_t)14U + (uint32_t)1U);
      uint32_t *res_j = table + ((uint32_t)14U + (uint32_t)1U) * (uint32_t)8U;
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[0U]) | (~c & a_bits_l[0U]);
        os[0U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[1U]) | (~c & a_bits_l[1U]);
        os[1U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[2U]) | (~c & a_bits_l[2U]);
        os[2U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[3U]) | (~c & a_bits_l[3U]);
        os[3U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[4U]) | (~c & a_bits_l[4U]);
        os[4U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[5U]) | (~c & a_bits_l[5U]);
        os[5U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[6U]) | (~c & a_bits_l[6U]);
        os[6U] = x;
      }
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[7U]) | (~c & a_bits_l[7U]);
        os[7U] = x;
      }
    }
    amont_mul(n, mu, resM, a_bits_l, resM);
  }
  uint32_t tmp0[16U] = { 0U };
  memcpy(tmp0, resM, (uint32_t)8U * sizeof (uint32_t));
  reduction(n, mu, tmp0, res);
}

static inline void
exp_vartime(
  uint32_t nBits,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  uint32_t r2[8U] = { 0U };
  precompr2(nBits, n, r2);
  uint32_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint32(n[0U]);
  exp_vartime_precomp(n, mu, r2, a, bBits, b, res);
}

static inline void
exp_consttime(
  uint32_t nBits,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  uint32_t r2[8U] = { 0U };
  precompr2(nBits, n, r2);
  uint32_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint32(n[0U]);
  exp_consttime_precomp(n, mu, r2, a, bBits, b, res);
}

/*
Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_consttime_* functions for constant-time variants.

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • n % 2 = 1
   • 1 < n
   • b < pow2 bBits
   • a < n
*/
bool
Hacl_Bignum256_32_mod_exp_vartime(
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  uint32_t is_valid_m = exp_check(n, a, bBits, b);
  uint32_t nBits = (uint32_t)32U * Hacl_Bignum_Lib_bn_get_top_index_u32((uint32_t)8U, n);
  if (is_valid_m == (uint32_t)0xFFFFFFFFU)
  {
    exp_vartime(nBits, n, a, bBits, b, res);
  }
  else
  {
    memset(res, 0U, (uint32_t)8U * sizeof (uint32_t));
  }
  return is_valid_m == (uint32_t)0xFFFFFFFFU;
}

/*
Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_vartime.

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • n % 2 = 1
   • 1 < n
   • b < pow2 bBits
   • a < n
*/
bool
Hacl_Bignum256_32_mod_exp_consttime(
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  uint32_t is_valid_m = exp_check(n, a, bBits, b);
  uint32_t nBits = (uint32_t)32U * Hacl_Bignum_Lib_bn_get_top_index_u32((uint32_t)8U, n);
  if (is_valid_m == (uint32_t)0xFFFFFFFFU)
  {
    exp_consttime(nBits, n, a, bBits, b, res);
  }
  else
  {
    memset(res, 0U, (uint32_t)8U * sizeof (uint32_t));
  }
  return is_valid_m == (uint32_t)0xFFFFFFFFU;
}

/*
Write `a ^ (-1) mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime

  The function returns false if any of the following preconditions are violated, true otherwise.
  • n % 2 = 1
  • 1 < n
  • 0 < a
  • a < n
*/
bool Hacl_Bignum256_32_mod_inv_prime_vartime(uint32_t *n, uint32_t *a, uint32_t *res)
{
  uint32_t one[8U] = { 0U };
  memset(one, 0U, (uint32_t)8U * sizeof (uint32_t));
  one[0U] = (uint32_t)1U;
  uint32_t bit0 = n[0U] & (uint32_t)1U;
  uint32_t m0 = (uint32_t)0U - bit0;
  uint32_t acc0 = (uint32_t)0U;
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[0U], n[0U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[0U], n[0U]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[1U], n[1U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[1U], n[1U]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[2U], n[2U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[2U], n[2U]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[3U], n[3U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[3U], n[3U]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[4U], n[4U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[4U], n[4U]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[5U], n[5U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[5U], n[5U]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[6U], n[6U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[6U], n[6U]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[7U], n[7U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[7U], n[7U]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  uint32_t m1 = acc0;
  uint32_t m00 = m0 & m1;
  uint32_t bn_zero[8U] = { 0U };
  uint32_t mask = (uint32_t)0xFFFFFFFFU;
  {
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[0U], bn_zero[0U]);
    mask = uu____0 & mask;
  }
  {
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[1U], bn_zero[1U]);
    mask = uu____0 & mask;
  }
  {
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[2U], bn_zero[2U]);
    mask = uu____0 & mask;
  }
  {
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[3U], bn_zero[3U]);
    mask = uu____0 & mask;
  }
  {
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[4U], bn_zero[4U]);
    mask = uu____0 & mask;
  }
  {
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[5U], bn_zero[5U]);
    mask = uu____0 & mask;
  }
  {
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[6U], bn_zero[6U]);
    mask = uu____0 & mask;
  }
  {
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[7U], bn_zero[7U]);
    mask = uu____0 & mask;
  }
  uint32_t mask1 = mask;
  uint32_t res10 = mask1;
  uint32_t m10 = res10;
  uint32_t acc = (uint32_t)0U;
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[0U], n[0U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[0U], n[0U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[1U], n[1U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[1U], n[1U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[2U], n[2U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[2U], n[2U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[3U], n[3U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[3U], n[3U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[4U], n[4U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[4U], n[4U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[5U], n[5U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[5U], n[5U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[6U], n[6U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[6U], n[6U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[7U], n[7U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[7U], n[7U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  uint32_t m2 = acc;
  uint32_t is_valid_m = (m00 & ~m10) & m2;
  uint32_t nBits = (uint32_t)32U * Hacl_Bignum_Lib_bn_get_top_index_u32((uint32_t)8U, n);
  if (is_valid_m == (uint32_t)0xFFFFFFFFU)
  {
    uint32_t n2[8U] = { 0U };
    uint32_t c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32((uint32_t)0U, n[0U], (uint32_t)2U, n2);
    uint32_t c1;
    if ((uint32_t)1U < (uint32_t)8U)
    {
      uint32_t rLen = (uint32_t)7U;
      uint32_t *a1 = n + (uint32_t)1U;
      uint32_t *res1 = n2 + (uint32_t)1U;
      uint32_t c = c0;
      for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U; i++)
      {
        uint32_t t1 = a1[(uint32_t)4U * i];
        uint32_t *res_i0 = res1 + (uint32_t)4U * i;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, (uint32_t)0U, res_i0);
        uint32_t t10 = a1[(uint32_t)4U * i + (uint32_t)1U];
        uint32_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t10, (uint32_t)0U, res_i1);
        uint32_t t11 = a1[(uint32_t)4U * i + (uint32_t)2U];
        uint32_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t11, (uint32_t)0U, res_i2);
        uint32_t t12 = a1[(uint32_t)4U * i + (uint32_t)3U];
        uint32_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t12, (uint32_t)0U, res_i);
      }
      for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
      {
        uint32_t t1 = a1[i];
        uint32_t *res_i = res1 + i;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, (uint32_t)0U, res_i);
      }
      uint32_t c10 = c;
      c1 = c10;
    }
    else
    {
      c1 = c0;
    }
    exp_vartime(nBits, n, a, (uint32_t)256U, n2, res);
  }
  else
  {
    memset(res, 0U, (uint32_t)8U * sizeof (uint32_t));
  }
  return is_valid_m == (uint32_t)0xFFFFFFFFU;
}


/**********************************************/
/* Arithmetic functions with precomputations. */
/**********************************************/


/*
Heap-allocate and initialize a montgomery context.

  The argument n is meant to be a 256-bit bignum, i.e. uint32_t[8].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n % 2 = 1
  • 1 < n

  The caller will need to call Hacl_Bignum256_mont_ctx_free on the return value
  to avoid memory leaks.
*/
Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *Hacl_Bignum256_32_mont_ctx_init(uint32_t *n)
{
  uint32_t *r2 = KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint32_t));
  uint32_t *n1 = KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint32_t));
  uint32_t *r21 = r2;
  uint32_t *n11 = n1;
  memcpy(n11, n, (uint32_t)8U * sizeof (uint32_t));
  uint32_t nBits = (uint32_t)32U * Hacl_Bignum_Lib_bn_get_top_index_u32((uint32_t)8U, n);
  precompr2(nBits, n, r21);
  uint32_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint32(n[0U]);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32
  res = { .len = (uint32_t)8U, .n = n11, .mu = mu, .r2 = r21 };
  KRML_CHECK_SIZE(sizeof (Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32), (uint32_t)1U);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32
  *buf = KRML_HOST_MALLOC(sizeof (Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32));
  buf[0U] = res;
  return buf;
}

/*
Deallocate the memory previously allocated by Hacl_Bignum256_mont_ctx_init.

  The argument k is a montgomery context obtained through Hacl_Bignum256_mont_ctx_init.
*/
void Hacl_Bignum256_32_mont_ctx_free(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 k1 = *k;
  uint32_t *n = k1.n;
  uint32_t *r2 = k1.r2;
  KRML_HOST_FREE(n);
  KRML_HOST_FREE(r2);
  KRML_HOST_FREE(k);
}

/*
Write `a mod n` in `res`.

  The argument a is meant to be a 512-bit bignum, i.e. uint32_t[16].
  The outparam res is meant to be a 256-bit bignum, i.e. uint32_t[8].
  The argument k is a montgomery context obtained through Hacl_Bignum256_mont_ctx_init.
*/
void
Hacl_Bignum256_32_mod_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 k1 = *k;
  bn_slow_precomp(k1.n, k1.mu, k1.r2, a, res);
}

/*
Write `a ^ b mod n` in `res`.

  The arguments a and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].
  The argument k is a montgomery context obtained through Hacl_Bignum256_mont_ctx_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_consttime_* functions for constant-time variants.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • b < pow2 bBits
  • a < n
*/
void
Hacl_Bignum256_32_mod_exp_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 k1 = *k;
  exp_vartime_precomp(k1.n, k1.mu, k1.r2, a, bBits, b, res);
}

/*
Write `a ^ b mod n` in `res`.

  The arguments a and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].
  The argument k is a montgomery context obtained through Hacl_Bignum256_mont_ctx_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_vartime_*.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • b < pow2 bBits
  • a < n
*/
void
Hacl_Bignum256_32_mod_exp_consttime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 k1 = *k;
  exp_consttime_precomp(k1.n, k1.mu, k1.r2, a, bBits, b, res);
}

/*
Write `a ^ (-1) mod n` in `res`.

  The argument a and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].
  The argument k is a montgomery context obtained through Hacl_Bignum256_mont_ctx_init.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime
  • 0 < a
  • a < n
*/
void
Hacl_Bignum256_32_mod_inv_prime_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 k1 = *k;
  uint32_t n2[8U] = { 0U };
  uint32_t c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32((uint32_t)0U, k1.n[0U], (uint32_t)2U, n2);
  uint32_t c1;
  if ((uint32_t)1U < (uint32_t)8U)
  {
    uint32_t rLen = (uint32_t)7U;
    uint32_t *a1 = k1.n + (uint32_t)1U;
    uint32_t *res1 = n2 + (uint32_t)1U;
    uint32_t c = c0;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U; i++)
    {
      uint32_t t1 = a1[(uint32_t)4U * i];
      uint32_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, (uint32_t)0U, res_i0);
      uint32_t t10 = a1[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t10, (uint32_t)0U, res_i1);
      uint32_t t11 = a1[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t11, (uint32_t)0U, res_i2);
      uint32_t t12 = a1[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t12, (uint32_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint32_t t1 = a1[i];
      uint32_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, (uint32_t)0U, res_i);
    }
    uint32_t c10 = c;
    c1 = c10;
  }
  else
  {
    c1 = c0;
  }
  exp_vartime_precomp(k1.n, k1.mu, k1.r2, a, (uint32_t)256U, n2, res);
}


/********************/
/* Loads and stores */
/********************/


/*
Load a bid-endian bignum from memory.

  The argument b points to len bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
   result of loading b, or NULL if either the allocation failed, or the amount of
    required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
uint32_t *Hacl_Bignum256_32_new_bn_from_bytes_be(uint32_t len, uint8_t *b)
{
  if
  (
    len
    == (uint32_t)0U
    || !((len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U <= (uint32_t)1073741823U)
  )
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), (len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U);
  uint32_t
  *res = KRML_HOST_CALLOC((len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U, sizeof (uint32_t));
  if (res == NULL)
  {
    return res;
  }
  uint32_t *res1 = res;
  uint32_t *res2 = res1;
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)4U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t tmp[tmpLen];
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp + tmpLen - len, b, len * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    uint32_t *os = res2;
    uint32_t u = load32_be(tmp + (bnLen - i - (uint32_t)1U) * (uint32_t)4U);
    uint32_t x = u;
    os[i] = x;
  }
  return res2;
}

/*
Load a little-endian bignum from memory.

  The argument b points to len bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
   result of loading b, or NULL if either the allocation failed, or the amount of
    required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
uint32_t *Hacl_Bignum256_32_new_bn_from_bytes_le(uint32_t len, uint8_t *b)
{
  if
  (
    len
    == (uint32_t)0U
    || !((len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U <= (uint32_t)1073741823U)
  )
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), (len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U);
  uint32_t
  *res = KRML_HOST_CALLOC((len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U, sizeof (uint32_t));
  if (res == NULL)
  {
    return res;
  }
  uint32_t *res1 = res;
  uint32_t *res2 = res1;
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)4U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t tmp[tmpLen];
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp, b, len * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < (len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U; i++)
  {
    uint32_t *os = res2;
    uint8_t *bj = tmp + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r1 = u;
    uint32_t x = r1;
    os[i] = x;
  }
  return res2;
}

/*
Serialize a bignum into big-endian memory.

  The argument b points to a 256-bit bignum.
  The outparam res points to 32 bytes of valid memory.
*/
void Hacl_Bignum256_32_bn_to_bytes_be(uint32_t *b, uint8_t *res)
{
  uint32_t bnLen = ((uint32_t)32U - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)4U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t tmp[tmpLen];
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  uint32_t numb = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    store32_be(tmp + i * numb, b[bnLen - i - (uint32_t)1U]);
  }
  memcpy(res, tmp + tmpLen - (uint32_t)32U, (uint32_t)32U * sizeof (uint8_t));
}

/*
Serialize a bignum into little-endian memory.

  The argument b points to a 256-bit bignum.
  The outparam res points to 32 bytes of valid memory.
*/
void Hacl_Bignum256_32_bn_to_bytes_le(uint32_t *b, uint8_t *res)
{
  uint32_t bnLen = ((uint32_t)32U - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)4U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t tmp[tmpLen];
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    store32_le(tmp + i * (uint32_t)4U, b[i]);
  }
  memcpy(res, tmp, (uint32_t)32U * sizeof (uint8_t));
}


/***************/
/* Comparisons */
/***************/


/*
Returns 2^32 - 1 if a < b, otherwise returns 0.

 The arguments a and b are meant to be 256-bit bignums, i.e. uint32_t[8].
*/
uint32_t Hacl_Bignum256_32_lt_mask(uint32_t *a, uint32_t *b)
{
  uint32_t acc = (uint32_t)0U;
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[0U], b[0U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[0U], b[0U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[1U], b[1U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[1U], b[1U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[2U], b[2U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[2U], b[2U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[3U], b[3U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[3U], b[3U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[4U], b[4U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[4U], b[4U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[5U], b[5U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[5U], b[5U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[6U], b[6U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[6U], b[6U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[7U], b[7U]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[7U], b[7U]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  return acc;
}

/*
Returns 2^32 - 1 if a = b, otherwise returns 0.

 The arguments a and b are meant to be 256-bit bignums, i.e. uint32_t[8].
*/
uint32_t Hacl_Bignum256_32_eq_mask(uint32_t *a, uint32_t *b)
{
  uint32_t mask = (uint32_t)0xFFFFFFFFU;
  {
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[0U], b[0U]);
    mask = uu____0 & mask;
  }
  {
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[1U], b[1U]);
    mask = uu____0 & mask;
  }
  {
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[2U], b[2U]);
    mask = uu____0 & mask;
  }
  {
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[3U], b[3U]);
    mask = uu____0 & mask;
  }
  {
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[4U], b[4U]);
    mask = uu____0 & mask;
  }
  {
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[5U], b[5U]);
    mask = uu____0 & mask;
  }
  {
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[6U], b[6U]);
    mask = uu____0 & mask;
  }
  {
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[7U], b[7U]);
    mask = uu____0 & mask;
  }
  uint32_t mask1 = mask;
  return mask1;
}

