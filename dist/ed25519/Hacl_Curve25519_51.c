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


#include "Hacl_Curve25519_51.h"

void
Hacl_Curve25519_51_fsquare_times(
  uint64_t *o,
  uint64_t *inp,
  FStar_UInt128_uint128 *tmp,
  uint32_t n
)
{
  Hacl_Impl_Curve25519_Field51_fsqr(o, inp, tmp);
  for (uint32_t i = (uint32_t)0U; i < n - (uint32_t)1U; i++)
  {
    Hacl_Impl_Curve25519_Field51_fsqr(o, o, tmp);
  }
}

void Hacl_Curve25519_51_finv(uint64_t *o, uint64_t *i, FStar_UInt128_uint128 *tmp)
{
  uint64_t t1[20U] = { 0U };
  uint64_t *a1 = t1;
  uint64_t *b1 = t1 + (uint32_t)5U;
  uint64_t *t010 = t1 + (uint32_t)15U;
  FStar_UInt128_uint128 *tmp10 = tmp;
  Hacl_Curve25519_51_fsquare_times(a1, i, tmp10, (uint32_t)1U);
  Hacl_Curve25519_51_fsquare_times(t010, a1, tmp10, (uint32_t)2U);
  Hacl_Impl_Curve25519_Field51_fmul(b1, t010, i, tmp);
  Hacl_Impl_Curve25519_Field51_fmul(a1, b1, a1, tmp);
  Hacl_Curve25519_51_fsquare_times(t010, a1, tmp10, (uint32_t)1U);
  Hacl_Impl_Curve25519_Field51_fmul(b1, t010, b1, tmp);
  Hacl_Curve25519_51_fsquare_times(t010, b1, tmp10, (uint32_t)5U);
  Hacl_Impl_Curve25519_Field51_fmul(b1, t010, b1, tmp);
  uint64_t *b10 = t1 + (uint32_t)5U;
  uint64_t *c10 = t1 + (uint32_t)10U;
  uint64_t *t011 = t1 + (uint32_t)15U;
  FStar_UInt128_uint128 *tmp11 = tmp;
  Hacl_Curve25519_51_fsquare_times(t011, b10, tmp11, (uint32_t)10U);
  Hacl_Impl_Curve25519_Field51_fmul(c10, t011, b10, tmp);
  Hacl_Curve25519_51_fsquare_times(t011, c10, tmp11, (uint32_t)20U);
  Hacl_Impl_Curve25519_Field51_fmul(t011, t011, c10, tmp);
  Hacl_Curve25519_51_fsquare_times(t011, t011, tmp11, (uint32_t)10U);
  Hacl_Impl_Curve25519_Field51_fmul(b10, t011, b10, tmp);
  Hacl_Curve25519_51_fsquare_times(t011, b10, tmp11, (uint32_t)50U);
  Hacl_Impl_Curve25519_Field51_fmul(c10, t011, b10, tmp);
  uint64_t *b11 = t1 + (uint32_t)5U;
  uint64_t *c1 = t1 + (uint32_t)10U;
  uint64_t *t01 = t1 + (uint32_t)15U;
  FStar_UInt128_uint128 *tmp1 = tmp;
  Hacl_Curve25519_51_fsquare_times(t01, c1, tmp1, (uint32_t)100U);
  Hacl_Impl_Curve25519_Field51_fmul(t01, t01, c1, tmp);
  Hacl_Curve25519_51_fsquare_times(t01, t01, tmp1, (uint32_t)50U);
  Hacl_Impl_Curve25519_Field51_fmul(t01, t01, b11, tmp);
  Hacl_Curve25519_51_fsquare_times(t01, t01, tmp1, (uint32_t)5U);
  uint64_t *a = t1;
  uint64_t *t0 = t1 + (uint32_t)15U;
  Hacl_Impl_Curve25519_Field51_fmul(o, t0, a, tmp);
}

