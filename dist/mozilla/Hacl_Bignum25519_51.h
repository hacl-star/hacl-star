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


#ifndef __Hacl_Bignum25519_51_H
#define __Hacl_Bignum25519_51_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include <stdbool.h>


#include "Hacl_Kremlib.h"

static inline void Hacl_Impl_Curve25519_Field51_fadd(uint64_t *out, uint64_t *f1, uint64_t *f2)
{
  uint64_t f10 = f1[0U];
  uint64_t f20 = f2[0U];
  uint64_t f11 = f1[1U];
  uint64_t f21 = f2[1U];
  uint64_t f12 = f1[2U];
  uint64_t f22 = f2[2U];
  uint64_t f13 = f1[3U];
  uint64_t f23 = f2[3U];
  uint64_t f14 = f1[4U];
  uint64_t f24 = f2[4U];
  out[0U] = f10 + f20;
  out[1U] = f11 + f21;
  out[2U] = f12 + f22;
  out[3U] = f13 + f23;
  out[4U] = f14 + f24;
}

static inline void Hacl_Impl_Curve25519_Field51_fsub(uint64_t *out, uint64_t *f1, uint64_t *f2)
{
  uint64_t f10 = f1[0U];
  uint64_t f20 = f2[0U];
  uint64_t f11 = f1[1U];
  uint64_t f21 = f2[1U];
  uint64_t f12 = f1[2U];
  uint64_t f22 = f2[2U];
  uint64_t f13 = f1[3U];
  uint64_t f23 = f2[3U];
  uint64_t f14 = f1[4U];
  uint64_t f24 = f2[4U];
  out[0U] = f10 + (uint64_t)0x3fffffffffff68U - f20;
  out[1U] = f11 + (uint64_t)0x3ffffffffffff8U - f21;
  out[2U] = f12 + (uint64_t)0x3ffffffffffff8U - f22;
  out[3U] = f13 + (uint64_t)0x3ffffffffffff8U - f23;
  out[4U] = f14 + (uint64_t)0x3ffffffffffff8U - f24;
}

static inline void
Hacl_Impl_Curve25519_Field51_fmul(
  uint64_t *out,
  uint64_t *f1,
  uint64_t *f2,
  FStar_UInt128_uint128 *uu___
)
{
  uint64_t f10 = f1[0U];
  uint64_t f11 = f1[1U];
  uint64_t f12 = f1[2U];
  uint64_t f13 = f1[3U];
  uint64_t f14 = f1[4U];
  uint64_t f20 = f2[0U];
  uint64_t f21 = f2[1U];
  uint64_t f22 = f2[2U];
  uint64_t f23 = f2[3U];
  uint64_t f24 = f2[4U];
  uint64_t tmp1 = f21 * (uint64_t)19U;
  uint64_t tmp2 = f22 * (uint64_t)19U;
  uint64_t tmp3 = f23 * (uint64_t)19U;
  uint64_t tmp4 = f24 * (uint64_t)19U;
  FStar_UInt128_uint128 o00 = FStar_UInt128_mul_wide(f10, f20);
  FStar_UInt128_uint128 o10 = FStar_UInt128_mul_wide(f10, f21);
  FStar_UInt128_uint128 o20 = FStar_UInt128_mul_wide(f10, f22);
  FStar_UInt128_uint128 o30 = FStar_UInt128_mul_wide(f10, f23);
  FStar_UInt128_uint128 o40 = FStar_UInt128_mul_wide(f10, f24);
  FStar_UInt128_uint128 o01 = FStar_UInt128_add(o00, FStar_UInt128_mul_wide(f11, tmp4));
  FStar_UInt128_uint128 o11 = FStar_UInt128_add(o10, FStar_UInt128_mul_wide(f11, f20));
  FStar_UInt128_uint128 o21 = FStar_UInt128_add(o20, FStar_UInt128_mul_wide(f11, f21));
  FStar_UInt128_uint128 o31 = FStar_UInt128_add(o30, FStar_UInt128_mul_wide(f11, f22));
  FStar_UInt128_uint128 o41 = FStar_UInt128_add(o40, FStar_UInt128_mul_wide(f11, f23));
  FStar_UInt128_uint128 o02 = FStar_UInt128_add(o01, FStar_UInt128_mul_wide(f12, tmp3));
  FStar_UInt128_uint128 o12 = FStar_UInt128_add(o11, FStar_UInt128_mul_wide(f12, tmp4));
  FStar_UInt128_uint128 o22 = FStar_UInt128_add(o21, FStar_UInt128_mul_wide(f12, f20));
  FStar_UInt128_uint128 o32 = FStar_UInt128_add(o31, FStar_UInt128_mul_wide(f12, f21));
  FStar_UInt128_uint128 o42 = FStar_UInt128_add(o41, FStar_UInt128_mul_wide(f12, f22));
  FStar_UInt128_uint128 o03 = FStar_UInt128_add(o02, FStar_UInt128_mul_wide(f13, tmp2));
  FStar_UInt128_uint128 o13 = FStar_UInt128_add(o12, FStar_UInt128_mul_wide(f13, tmp3));
  FStar_UInt128_uint128 o23 = FStar_UInt128_add(o22, FStar_UInt128_mul_wide(f13, tmp4));
  FStar_UInt128_uint128 o33 = FStar_UInt128_add(o32, FStar_UInt128_mul_wide(f13, f20));
  FStar_UInt128_uint128 o43 = FStar_UInt128_add(o42, FStar_UInt128_mul_wide(f13, f21));
  FStar_UInt128_uint128 o04 = FStar_UInt128_add(o03, FStar_UInt128_mul_wide(f14, tmp1));
  FStar_UInt128_uint128 o14 = FStar_UInt128_add(o13, FStar_UInt128_mul_wide(f14, tmp2));
  FStar_UInt128_uint128 o24 = FStar_UInt128_add(o23, FStar_UInt128_mul_wide(f14, tmp3));
  FStar_UInt128_uint128 o34 = FStar_UInt128_add(o33, FStar_UInt128_mul_wide(f14, tmp4));
  FStar_UInt128_uint128 o44 = FStar_UInt128_add(o43, FStar_UInt128_mul_wide(f14, f20));
  FStar_UInt128_uint128 tmp_w0 = o04;
  FStar_UInt128_uint128 tmp_w1 = o14;
  FStar_UInt128_uint128 tmp_w2 = o24;
  FStar_UInt128_uint128 tmp_w3 = o34;
  FStar_UInt128_uint128 tmp_w4 = o44;
  FStar_UInt128_uint128
  l_ = FStar_UInt128_add(tmp_w0, FStar_UInt128_uint64_to_uint128((uint64_t)0U));
  uint64_t tmp01 = FStar_UInt128_uint128_to_uint64(l_) & (uint64_t)0x7ffffffffffffU;
  uint64_t c0 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(l_, (uint32_t)51U));
  FStar_UInt128_uint128 l_0 = FStar_UInt128_add(tmp_w1, FStar_UInt128_uint64_to_uint128(c0));
  uint64_t tmp11 = FStar_UInt128_uint128_to_uint64(l_0) & (uint64_t)0x7ffffffffffffU;
  uint64_t c1 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(l_0, (uint32_t)51U));
  FStar_UInt128_uint128 l_1 = FStar_UInt128_add(tmp_w2, FStar_UInt128_uint64_to_uint128(c1));
  uint64_t tmp21 = FStar_UInt128_uint128_to_uint64(l_1) & (uint64_t)0x7ffffffffffffU;
  uint64_t c2 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(l_1, (uint32_t)51U));
  FStar_UInt128_uint128 l_2 = FStar_UInt128_add(tmp_w3, FStar_UInt128_uint64_to_uint128(c2));
  uint64_t tmp31 = FStar_UInt128_uint128_to_uint64(l_2) & (uint64_t)0x7ffffffffffffU;
  uint64_t c3 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(l_2, (uint32_t)51U));
  FStar_UInt128_uint128 l_3 = FStar_UInt128_add(tmp_w4, FStar_UInt128_uint64_to_uint128(c3));
  uint64_t tmp41 = FStar_UInt128_uint128_to_uint64(l_3) & (uint64_t)0x7ffffffffffffU;
  uint64_t c4 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(l_3, (uint32_t)51U));
  uint64_t l_4 = tmp01 + c4 * (uint64_t)19U;
  uint64_t tmp0_ = l_4 & (uint64_t)0x7ffffffffffffU;
  uint64_t c5 = l_4 >> (uint32_t)51U;
  uint64_t o0 = tmp0_;
  uint64_t o1 = tmp11 + c5;
  uint64_t o2 = tmp21;
  uint64_t o3 = tmp31;
  uint64_t o4 = tmp41;
  out[0U] = o0;
  out[1U] = o1;
  out[2U] = o2;
  out[3U] = o3;
  out[4U] = o4;
}

static inline void
Hacl_Impl_Curve25519_Field51_fsqr(uint64_t *out, uint64_t *f, FStar_UInt128_uint128 *uu___)
{
  uint64_t f0 = f[0U];
  uint64_t f1 = f[1U];
  uint64_t f2 = f[2U];
  uint64_t f3 = f[3U];
  uint64_t f4 = f[4U];
  uint64_t d0 = (uint64_t)2U * f0;
  uint64_t d1 = (uint64_t)2U * f1;
  uint64_t d2 = (uint64_t)38U * f2;
  uint64_t d3 = (uint64_t)19U * f3;
  uint64_t d419 = (uint64_t)19U * f4;
  uint64_t d4 = (uint64_t)2U * d419;
  FStar_UInt128_uint128
  s0 =
    FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(f0, f0),
        FStar_UInt128_mul_wide(d4, f1)),
      FStar_UInt128_mul_wide(d2, f3));
  FStar_UInt128_uint128
  s1 =
    FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(d0, f1),
        FStar_UInt128_mul_wide(d4, f2)),
      FStar_UInt128_mul_wide(d3, f3));
  FStar_UInt128_uint128
  s2 =
    FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(d0, f2),
        FStar_UInt128_mul_wide(f1, f1)),
      FStar_UInt128_mul_wide(d4, f3));
  FStar_UInt128_uint128
  s3 =
    FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(d0, f3),
        FStar_UInt128_mul_wide(d1, f2)),
      FStar_UInt128_mul_wide(f4, d419));
  FStar_UInt128_uint128
  s4 =
    FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(d0, f4),
        FStar_UInt128_mul_wide(d1, f3)),
      FStar_UInt128_mul_wide(f2, f2));
  FStar_UInt128_uint128 o00 = s0;
  FStar_UInt128_uint128 o10 = s1;
  FStar_UInt128_uint128 o20 = s2;
  FStar_UInt128_uint128 o30 = s3;
  FStar_UInt128_uint128 o40 = s4;
  FStar_UInt128_uint128
  l_ = FStar_UInt128_add(o00, FStar_UInt128_uint64_to_uint128((uint64_t)0U));
  uint64_t tmp0 = FStar_UInt128_uint128_to_uint64(l_) & (uint64_t)0x7ffffffffffffU;
  uint64_t c0 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(l_, (uint32_t)51U));
  FStar_UInt128_uint128 l_0 = FStar_UInt128_add(o10, FStar_UInt128_uint64_to_uint128(c0));
  uint64_t tmp1 = FStar_UInt128_uint128_to_uint64(l_0) & (uint64_t)0x7ffffffffffffU;
  uint64_t c1 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(l_0, (uint32_t)51U));
  FStar_UInt128_uint128 l_1 = FStar_UInt128_add(o20, FStar_UInt128_uint64_to_uint128(c1));
  uint64_t tmp2 = FStar_UInt128_uint128_to_uint64(l_1) & (uint64_t)0x7ffffffffffffU;
  uint64_t c2 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(l_1, (uint32_t)51U));
  FStar_UInt128_uint128 l_2 = FStar_UInt128_add(o30, FStar_UInt128_uint64_to_uint128(c2));
  uint64_t tmp3 = FStar_UInt128_uint128_to_uint64(l_2) & (uint64_t)0x7ffffffffffffU;
  uint64_t c3 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(l_2, (uint32_t)51U));
  FStar_UInt128_uint128 l_3 = FStar_UInt128_add(o40, FStar_UInt128_uint64_to_uint128(c3));
  uint64_t tmp4 = FStar_UInt128_uint128_to_uint64(l_3) & (uint64_t)0x7ffffffffffffU;
  uint64_t c4 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(l_3, (uint32_t)51U));
  uint64_t l_4 = tmp0 + c4 * (uint64_t)19U;
  uint64_t tmp0_ = l_4 & (uint64_t)0x7ffffffffffffU;
  uint64_t c5 = l_4 >> (uint32_t)51U;
  uint64_t o0 = tmp0_;
  uint64_t o1 = tmp1 + c5;
  uint64_t o2 = tmp2;
  uint64_t o3 = tmp3;
  uint64_t o4 = tmp4;
  out[0U] = o0;
  out[1U] = o1;
  out[2U] = o2;
  out[3U] = o3;
  out[4U] = o4;
}

static inline void Hacl_Impl_Curve25519_Field51_store_felem(uint64_t *u64s, uint64_t *f)
{
  uint64_t f0 = f[0U];
  uint64_t f1 = f[1U];
  uint64_t f2 = f[2U];
  uint64_t f3 = f[3U];
  uint64_t f4 = f[4U];
  uint64_t l_ = f0 + (uint64_t)0U;
  uint64_t tmp0 = l_ & (uint64_t)0x7ffffffffffffU;
  uint64_t c0 = l_ >> (uint32_t)51U;
  uint64_t l_0 = f1 + c0;
  uint64_t tmp1 = l_0 & (uint64_t)0x7ffffffffffffU;
  uint64_t c1 = l_0 >> (uint32_t)51U;
  uint64_t l_1 = f2 + c1;
  uint64_t tmp2 = l_1 & (uint64_t)0x7ffffffffffffU;
  uint64_t c2 = l_1 >> (uint32_t)51U;
  uint64_t l_2 = f3 + c2;
  uint64_t tmp3 = l_2 & (uint64_t)0x7ffffffffffffU;
  uint64_t c3 = l_2 >> (uint32_t)51U;
  uint64_t l_3 = f4 + c3;
  uint64_t tmp4 = l_3 & (uint64_t)0x7ffffffffffffU;
  uint64_t c4 = l_3 >> (uint32_t)51U;
  uint64_t l_4 = tmp0 + c4 * (uint64_t)19U;
  uint64_t tmp0_ = l_4 & (uint64_t)0x7ffffffffffffU;
  uint64_t c5 = l_4 >> (uint32_t)51U;
  uint64_t f01 = tmp0_;
  uint64_t f11 = tmp1 + c5;
  uint64_t f21 = tmp2;
  uint64_t f31 = tmp3;
  uint64_t f41 = tmp4;
  uint64_t m0 = FStar_UInt64_gte_mask(f01, (uint64_t)0x7ffffffffffedU);
  uint64_t m1 = FStar_UInt64_eq_mask(f11, (uint64_t)0x7ffffffffffffU);
  uint64_t m2 = FStar_UInt64_eq_mask(f21, (uint64_t)0x7ffffffffffffU);
  uint64_t m3 = FStar_UInt64_eq_mask(f31, (uint64_t)0x7ffffffffffffU);
  uint64_t m4 = FStar_UInt64_eq_mask(f41, (uint64_t)0x7ffffffffffffU);
  uint64_t mask = (((m0 & m1) & m2) & m3) & m4;
  uint64_t f0_ = f01 - (mask & (uint64_t)0x7ffffffffffedU);
  uint64_t f1_ = f11 - (mask & (uint64_t)0x7ffffffffffffU);
  uint64_t f2_ = f21 - (mask & (uint64_t)0x7ffffffffffffU);
  uint64_t f3_ = f31 - (mask & (uint64_t)0x7ffffffffffffU);
  uint64_t f4_ = f41 - (mask & (uint64_t)0x7ffffffffffffU);
  uint64_t f02 = f0_;
  uint64_t f12 = f1_;
  uint64_t f22 = f2_;
  uint64_t f32 = f3_;
  uint64_t f42 = f4_;
  uint64_t o00 = f02 | f12 << (uint32_t)51U;
  uint64_t o10 = f12 >> (uint32_t)13U | f22 << (uint32_t)38U;
  uint64_t o20 = f22 >> (uint32_t)26U | f32 << (uint32_t)25U;
  uint64_t o30 = f32 >> (uint32_t)39U | f42 << (uint32_t)12U;
  uint64_t o0 = o00;
  uint64_t o1 = o10;
  uint64_t o2 = o20;
  uint64_t o3 = o30;
  u64s[0U] = o0;
  u64s[1U] = o1;
  u64s[2U] = o2;
  u64s[3U] = o3;
}

#if defined(__cplusplus)
}
#endif

#define __Hacl_Bignum25519_51_H_DEFINED
#endif
