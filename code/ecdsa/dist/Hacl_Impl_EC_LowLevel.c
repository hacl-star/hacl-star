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


#include "Hacl_Impl_EC_LowLevel.h"

void Hacl_Impl_EC_LowLevel_mul_p256(uint64_t *f, uint64_t *r, uint64_t *out)
{
  uint32_t resLen = (uint32_t)8U;
  memset(out, 0U, resLen * sizeof (uint64_t));
  uint64_t bj = r[0U];
  uint64_t *res_j0 = out;
  uint64_t c0 = (uint64_t)0U;
  uint64_t a_i0 = f[0U];
  uint64_t *res_i0 = res_j0;
  c0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c0, res_i0);
  uint64_t a_i1 = f[1U];
  uint64_t *res_i1 = res_j0 + (uint32_t)1U;
  c0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c0, res_i1);
  uint64_t a_i2 = f[2U];
  uint64_t *res_i2 = res_j0 + (uint32_t)2U;
  c0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c0, res_i2);
  uint64_t a_i3 = f[3U];
  uint64_t *res_i3 = res_j0 + (uint32_t)3U;
  c0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i3, bj, c0, res_i3);
  uint64_t r1 = c0;
  out[4U] = r1;
  uint64_t bj0 = r[1U];
  uint64_t *res_j1 = out + (uint32_t)1U;
  uint64_t c1 = (uint64_t)0U;
  uint64_t a_i4 = f[0U];
  uint64_t *res_i4 = res_j1;
  c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i4, bj0, c1, res_i4);
  uint64_t a_i5 = f[1U];
  uint64_t *res_i5 = res_j1 + (uint32_t)1U;
  c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i5, bj0, c1, res_i5);
  uint64_t a_i6 = f[2U];
  uint64_t *res_i6 = res_j1 + (uint32_t)2U;
  c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i6, bj0, c1, res_i6);
  uint64_t a_i7 = f[3U];
  uint64_t *res_i7 = res_j1 + (uint32_t)3U;
  c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i7, bj0, c1, res_i7);
  uint64_t r10 = c1;
  out[5U] = r10;
  uint64_t bj1 = r[2U];
  uint64_t *res_j2 = out + (uint32_t)2U;
  uint64_t c2 = (uint64_t)0U;
  uint64_t a_i8 = f[0U];
  uint64_t *res_i8 = res_j2;
  c2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i8, bj1, c2, res_i8);
  uint64_t a_i9 = f[1U];
  uint64_t *res_i9 = res_j2 + (uint32_t)1U;
  c2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i9, bj1, c2, res_i9);
  uint64_t a_i10 = f[2U];
  uint64_t *res_i10 = res_j2 + (uint32_t)2U;
  c2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i10, bj1, c2, res_i10);
  uint64_t a_i11 = f[3U];
  uint64_t *res_i11 = res_j2 + (uint32_t)3U;
  c2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i11, bj1, c2, res_i11);
  uint64_t r11 = c2;
  out[6U] = r11;
  uint64_t bj2 = r[3U];
  uint64_t *res_j = out + (uint32_t)3U;
  uint64_t c = (uint64_t)0U;
  uint64_t a_i = f[0U];
  uint64_t *res_i12 = res_j;
  c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj2, c, res_i12);
  uint64_t a_i12 = f[1U];
  uint64_t *res_i13 = res_j + (uint32_t)1U;
  c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i12, bj2, c, res_i13);
  uint64_t a_i13 = f[2U];
  uint64_t *res_i14 = res_j + (uint32_t)2U;
  c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i13, bj2, c, res_i14);
  uint64_t a_i14 = f[3U];
  uint64_t *res_i = res_j + (uint32_t)3U;
  c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i14, bj2, c, res_i);
  uint64_t r12 = c;
  out[7U] = r12;
}

