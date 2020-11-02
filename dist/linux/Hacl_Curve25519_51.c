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

inline void Hacl_Impl_Curve25519_Field51_fadd(u64 *out, u64 *f1, u64 *f2)
{
  u64 f10 = f1[0U];
  u64 f20 = f2[0U];
  u64 f11 = f1[1U];
  u64 f21 = f2[1U];
  u64 f12 = f1[2U];
  u64 f22 = f2[2U];
  u64 f13 = f1[3U];
  u64 f23 = f2[3U];
  u64 f14 = f1[4U];
  u64 f24 = f2[4U];
  out[0U] = f10 + f20;
  out[1U] = f11 + f21;
  out[2U] = f12 + f22;
  out[3U] = f13 + f23;
  out[4U] = f14 + f24;
}

inline void Hacl_Impl_Curve25519_Field51_fsub(u64 *out, u64 *f1, u64 *f2)
{
  u64 f10 = f1[0U];
  u64 f20 = f2[0U];
  u64 f11 = f1[1U];
  u64 f21 = f2[1U];
  u64 f12 = f1[2U];
  u64 f22 = f2[2U];
  u64 f13 = f1[3U];
  u64 f23 = f2[3U];
  u64 f14 = f1[4U];
  u64 f24 = f2[4U];
  out[0U] = f10 + (u64)0x3fffffffffff68U - f20;
  out[1U] = f11 + (u64)0x3ffffffffffff8U - f21;
  out[2U] = f12 + (u64)0x3ffffffffffff8U - f22;
  out[3U] = f13 + (u64)0x3ffffffffffff8U - f23;
  out[4U] = f14 + (u64)0x3ffffffffffff8U - f24;
}

inline void Hacl_Impl_Curve25519_Field51_fmul(u64 *out, u64 *f1, u64 *f2, uint128_t *uu___)
{
  u64 f10 = f1[0U];
  u64 f11 = f1[1U];
  u64 f12 = f1[2U];
  u64 f13 = f1[3U];
  u64 f14 = f1[4U];
  u64 f20 = f2[0U];
  u64 f21 = f2[1U];
  u64 f22 = f2[2U];
  u64 f23 = f2[3U];
  u64 f24 = f2[4U];
  u64 tmp1 = f21 * (u64)19U;
  u64 tmp2 = f22 * (u64)19U;
  u64 tmp3 = f23 * (u64)19U;
  u64 tmp4 = f24 * (u64)19U;
  uint128_t o00 = (uint128_t)f10 * f20;
  uint128_t o10 = (uint128_t)f10 * f21;
  uint128_t o20 = (uint128_t)f10 * f22;
  uint128_t o30 = (uint128_t)f10 * f23;
  uint128_t o40 = (uint128_t)f10 * f24;
  uint128_t o01 = o00 + (uint128_t)f11 * tmp4;
  uint128_t o11 = o10 + (uint128_t)f11 * f20;
  uint128_t o21 = o20 + (uint128_t)f11 * f21;
  uint128_t o31 = o30 + (uint128_t)f11 * f22;
  uint128_t o41 = o40 + (uint128_t)f11 * f23;
  uint128_t o02 = o01 + (uint128_t)f12 * tmp3;
  uint128_t o12 = o11 + (uint128_t)f12 * tmp4;
  uint128_t o22 = o21 + (uint128_t)f12 * f20;
  uint128_t o32 = o31 + (uint128_t)f12 * f21;
  uint128_t o42 = o41 + (uint128_t)f12 * f22;
  uint128_t o03 = o02 + (uint128_t)f13 * tmp2;
  uint128_t o13 = o12 + (uint128_t)f13 * tmp3;
  uint128_t o23 = o22 + (uint128_t)f13 * tmp4;
  uint128_t o33 = o32 + (uint128_t)f13 * f20;
  uint128_t o43 = o42 + (uint128_t)f13 * f21;
  uint128_t o04 = o03 + (uint128_t)f14 * tmp1;
  uint128_t o14 = o13 + (uint128_t)f14 * tmp2;
  uint128_t o24 = o23 + (uint128_t)f14 * tmp3;
  uint128_t o34 = o33 + (uint128_t)f14 * tmp4;
  uint128_t o44 = o43 + (uint128_t)f14 * f20;
  uint128_t tmp_w0 = o04;
  uint128_t tmp_w1 = o14;
  uint128_t tmp_w2 = o24;
  uint128_t tmp_w3 = o34;
  uint128_t tmp_w4 = o44;
  uint128_t l_ = tmp_w0 + (uint128_t)(u64)0U;
  u64 tmp01 = (uint64_t)l_ & (u64)0x7ffffffffffffU;
  u64 c0 = (uint64_t)(l_ >> (u32)51U);
  uint128_t l_0 = tmp_w1 + (uint128_t)c0;
  u64 tmp11 = (uint64_t)l_0 & (u64)0x7ffffffffffffU;
  u64 c1 = (uint64_t)(l_0 >> (u32)51U);
  uint128_t l_1 = tmp_w2 + (uint128_t)c1;
  u64 tmp21 = (uint64_t)l_1 & (u64)0x7ffffffffffffU;
  u64 c2 = (uint64_t)(l_1 >> (u32)51U);
  uint128_t l_2 = tmp_w3 + (uint128_t)c2;
  u64 tmp31 = (uint64_t)l_2 & (u64)0x7ffffffffffffU;
  u64 c3 = (uint64_t)(l_2 >> (u32)51U);
  uint128_t l_3 = tmp_w4 + (uint128_t)c3;
  u64 tmp41 = (uint64_t)l_3 & (u64)0x7ffffffffffffU;
  u64 c4 = (uint64_t)(l_3 >> (u32)51U);
  u64 l_4 = tmp01 + c4 * (u64)19U;
  u64 tmp0_ = l_4 & (u64)0x7ffffffffffffU;
  u64 c5 = l_4 >> (u32)51U;
  u64 o0 = tmp0_;
  u64 o1 = tmp11 + c5;
  u64 o2 = tmp21;
  u64 o3 = tmp31;
  u64 o4 = tmp41;
  out[0U] = o0;
  out[1U] = o1;
  out[2U] = o2;
  out[3U] = o3;
  out[4U] = o4;
}

static inline void fmul2(u64 *out, u64 *f1, u64 *f2)
{
  u64 f10 = f1[0U];
  u64 f11 = f1[1U];
  u64 f12 = f1[2U];
  u64 f13 = f1[3U];
  u64 f14 = f1[4U];
  u64 f20 = f2[0U];
  u64 f21 = f2[1U];
  u64 f22 = f2[2U];
  u64 f23 = f2[3U];
  u64 f24 = f2[4U];
  u64 f30 = f1[5U];
  u64 f31 = f1[6U];
  u64 f32 = f1[7U];
  u64 f33 = f1[8U];
  u64 f34 = f1[9U];
  u64 f40 = f2[5U];
  u64 f41 = f2[6U];
  u64 f42 = f2[7U];
  u64 f43 = f2[8U];
  u64 f44 = f2[9U];
  u64 tmp11 = f21 * (u64)19U;
  u64 tmp12 = f22 * (u64)19U;
  u64 tmp13 = f23 * (u64)19U;
  u64 tmp14 = f24 * (u64)19U;
  u64 tmp21 = f41 * (u64)19U;
  u64 tmp22 = f42 * (u64)19U;
  u64 tmp23 = f43 * (u64)19U;
  u64 tmp24 = f44 * (u64)19U;
  uint128_t o00 = (uint128_t)f10 * f20;
  uint128_t o15 = (uint128_t)f10 * f21;
  uint128_t o25 = (uint128_t)f10 * f22;
  uint128_t o30 = (uint128_t)f10 * f23;
  uint128_t o40 = (uint128_t)f10 * f24;
  uint128_t o010 = o00 + (uint128_t)f11 * tmp14;
  uint128_t o110 = o15 + (uint128_t)f11 * f20;
  uint128_t o210 = o25 + (uint128_t)f11 * f21;
  uint128_t o310 = o30 + (uint128_t)f11 * f22;
  uint128_t o410 = o40 + (uint128_t)f11 * f23;
  uint128_t o020 = o010 + (uint128_t)f12 * tmp13;
  uint128_t o120 = o110 + (uint128_t)f12 * tmp14;
  uint128_t o220 = o210 + (uint128_t)f12 * f20;
  uint128_t o320 = o310 + (uint128_t)f12 * f21;
  uint128_t o420 = o410 + (uint128_t)f12 * f22;
  uint128_t o030 = o020 + (uint128_t)f13 * tmp12;
  uint128_t o130 = o120 + (uint128_t)f13 * tmp13;
  uint128_t o230 = o220 + (uint128_t)f13 * tmp14;
  uint128_t o330 = o320 + (uint128_t)f13 * f20;
  uint128_t o430 = o420 + (uint128_t)f13 * f21;
  uint128_t o040 = o030 + (uint128_t)f14 * tmp11;
  uint128_t o140 = o130 + (uint128_t)f14 * tmp12;
  uint128_t o240 = o230 + (uint128_t)f14 * tmp13;
  uint128_t o340 = o330 + (uint128_t)f14 * tmp14;
  uint128_t o440 = o430 + (uint128_t)f14 * f20;
  uint128_t tmp_w10 = o040;
  uint128_t tmp_w11 = o140;
  uint128_t tmp_w12 = o240;
  uint128_t tmp_w13 = o340;
  uint128_t tmp_w14 = o440;
  uint128_t o0 = (uint128_t)f30 * f40;
  uint128_t o1 = (uint128_t)f30 * f41;
  uint128_t o2 = (uint128_t)f30 * f42;
  uint128_t o3 = (uint128_t)f30 * f43;
  uint128_t o4 = (uint128_t)f30 * f44;
  uint128_t o01 = o0 + (uint128_t)f31 * tmp24;
  uint128_t o111 = o1 + (uint128_t)f31 * f40;
  uint128_t o211 = o2 + (uint128_t)f31 * f41;
  uint128_t o31 = o3 + (uint128_t)f31 * f42;
  uint128_t o41 = o4 + (uint128_t)f31 * f43;
  uint128_t o02 = o01 + (uint128_t)f32 * tmp23;
  uint128_t o121 = o111 + (uint128_t)f32 * tmp24;
  uint128_t o221 = o211 + (uint128_t)f32 * f40;
  uint128_t o32 = o31 + (uint128_t)f32 * f41;
  uint128_t o42 = o41 + (uint128_t)f32 * f42;
  uint128_t o03 = o02 + (uint128_t)f33 * tmp22;
  uint128_t o131 = o121 + (uint128_t)f33 * tmp23;
  uint128_t o231 = o221 + (uint128_t)f33 * tmp24;
  uint128_t o33 = o32 + (uint128_t)f33 * f40;
  uint128_t o43 = o42 + (uint128_t)f33 * f41;
  uint128_t o04 = o03 + (uint128_t)f34 * tmp21;
  uint128_t o141 = o131 + (uint128_t)f34 * tmp22;
  uint128_t o241 = o231 + (uint128_t)f34 * tmp23;
  uint128_t o34 = o33 + (uint128_t)f34 * tmp24;
  uint128_t o44 = o43 + (uint128_t)f34 * f40;
  uint128_t tmp_w20 = o04;
  uint128_t tmp_w21 = o141;
  uint128_t tmp_w22 = o241;
  uint128_t tmp_w23 = o34;
  uint128_t tmp_w24 = o44;
  uint128_t l_ = tmp_w10 + (uint128_t)(u64)0U;
  u64 tmp00 = (uint64_t)l_ & (u64)0x7ffffffffffffU;
  u64 c00 = (uint64_t)(l_ >> (u32)51U);
  uint128_t l_0 = tmp_w11 + (uint128_t)c00;
  u64 tmp10 = (uint64_t)l_0 & (u64)0x7ffffffffffffU;
  u64 c10 = (uint64_t)(l_0 >> (u32)51U);
  uint128_t l_1 = tmp_w12 + (uint128_t)c10;
  u64 tmp20 = (uint64_t)l_1 & (u64)0x7ffffffffffffU;
  u64 c20 = (uint64_t)(l_1 >> (u32)51U);
  uint128_t l_2 = tmp_w13 + (uint128_t)c20;
  u64 tmp30 = (uint64_t)l_2 & (u64)0x7ffffffffffffU;
  u64 c30 = (uint64_t)(l_2 >> (u32)51U);
  uint128_t l_3 = tmp_w14 + (uint128_t)c30;
  u64 tmp40 = (uint64_t)l_3 & (u64)0x7ffffffffffffU;
  u64 c40 = (uint64_t)(l_3 >> (u32)51U);
  u64 l_4 = tmp00 + c40 * (u64)19U;
  u64 tmp0_ = l_4 & (u64)0x7ffffffffffffU;
  u64 c50 = l_4 >> (u32)51U;
  u64 o100 = tmp0_;
  u64 o112 = tmp10 + c50;
  u64 o122 = tmp20;
  u64 o132 = tmp30;
  u64 o142 = tmp40;
  uint128_t l_5 = tmp_w20 + (uint128_t)(u64)0U;
  u64 tmp0 = (uint64_t)l_5 & (u64)0x7ffffffffffffU;
  u64 c0 = (uint64_t)(l_5 >> (u32)51U);
  uint128_t l_6 = tmp_w21 + (uint128_t)c0;
  u64 tmp1 = (uint64_t)l_6 & (u64)0x7ffffffffffffU;
  u64 c1 = (uint64_t)(l_6 >> (u32)51U);
  uint128_t l_7 = tmp_w22 + (uint128_t)c1;
  u64 tmp2 = (uint64_t)l_7 & (u64)0x7ffffffffffffU;
  u64 c2 = (uint64_t)(l_7 >> (u32)51U);
  uint128_t l_8 = tmp_w23 + (uint128_t)c2;
  u64 tmp3 = (uint64_t)l_8 & (u64)0x7ffffffffffffU;
  u64 c3 = (uint64_t)(l_8 >> (u32)51U);
  uint128_t l_9 = tmp_w24 + (uint128_t)c3;
  u64 tmp4 = (uint64_t)l_9 & (u64)0x7ffffffffffffU;
  u64 c4 = (uint64_t)(l_9 >> (u32)51U);
  u64 l_10 = tmp0 + c4 * (u64)19U;
  u64 tmp0_0 = l_10 & (u64)0x7ffffffffffffU;
  u64 c5 = l_10 >> (u32)51U;
  u64 o200 = tmp0_0;
  u64 o212 = tmp1 + c5;
  u64 o222 = tmp2;
  u64 o232 = tmp3;
  u64 o242 = tmp4;
  u64 o10 = o100;
  u64 o11 = o112;
  u64 o12 = o122;
  u64 o13 = o132;
  u64 o14 = o142;
  u64 o20 = o200;
  u64 o21 = o212;
  u64 o22 = o222;
  u64 o23 = o232;
  u64 o24 = o242;
  out[0U] = o10;
  out[1U] = o11;
  out[2U] = o12;
  out[3U] = o13;
  out[4U] = o14;
  out[5U] = o20;
  out[6U] = o21;
  out[7U] = o22;
  out[8U] = o23;
  out[9U] = o24;
}

inline void Hacl_Impl_Curve25519_Field51_fmul1(u64 *out, u64 *f1, u64 f2)
{
  u64 f10 = f1[0U];
  u64 f11 = f1[1U];
  u64 f12 = f1[2U];
  u64 f13 = f1[3U];
  u64 f14 = f1[4U];
  uint128_t tmp_w0 = (uint128_t)f2 * f10;
  uint128_t tmp_w1 = (uint128_t)f2 * f11;
  uint128_t tmp_w2 = (uint128_t)f2 * f12;
  uint128_t tmp_w3 = (uint128_t)f2 * f13;
  uint128_t tmp_w4 = (uint128_t)f2 * f14;
  uint128_t l_ = tmp_w0 + (uint128_t)(u64)0U;
  u64 tmp0 = (uint64_t)l_ & (u64)0x7ffffffffffffU;
  u64 c0 = (uint64_t)(l_ >> (u32)51U);
  uint128_t l_0 = tmp_w1 + (uint128_t)c0;
  u64 tmp1 = (uint64_t)l_0 & (u64)0x7ffffffffffffU;
  u64 c1 = (uint64_t)(l_0 >> (u32)51U);
  uint128_t l_1 = tmp_w2 + (uint128_t)c1;
  u64 tmp2 = (uint64_t)l_1 & (u64)0x7ffffffffffffU;
  u64 c2 = (uint64_t)(l_1 >> (u32)51U);
  uint128_t l_2 = tmp_w3 + (uint128_t)c2;
  u64 tmp3 = (uint64_t)l_2 & (u64)0x7ffffffffffffU;
  u64 c3 = (uint64_t)(l_2 >> (u32)51U);
  uint128_t l_3 = tmp_w4 + (uint128_t)c3;
  u64 tmp4 = (uint64_t)l_3 & (u64)0x7ffffffffffffU;
  u64 c4 = (uint64_t)(l_3 >> (u32)51U);
  u64 l_4 = tmp0 + c4 * (u64)19U;
  u64 tmp0_ = l_4 & (u64)0x7ffffffffffffU;
  u64 c5 = l_4 >> (u32)51U;
  u64 o0 = tmp0_;
  u64 o1 = tmp1 + c5;
  u64 o2 = tmp2;
  u64 o3 = tmp3;
  u64 o4 = tmp4;
  out[0U] = o0;
  out[1U] = o1;
  out[2U] = o2;
  out[3U] = o3;
  out[4U] = o4;
}

inline void Hacl_Impl_Curve25519_Field51_fsqr(u64 *out, u64 *f, uint128_t *uu___)
{
  u64 f0 = f[0U];
  u64 f1 = f[1U];
  u64 f2 = f[2U];
  u64 f3 = f[3U];
  u64 f4 = f[4U];
  u64 d0 = (u64)2U * f0;
  u64 d1 = (u64)2U * f1;
  u64 d2 = (u64)38U * f2;
  u64 d3 = (u64)19U * f3;
  u64 d419 = (u64)19U * f4;
  u64 d4 = (u64)2U * d419;
  uint128_t s0 = (uint128_t)f0 * f0 + (uint128_t)d4 * f1 + (uint128_t)d2 * f3;
  uint128_t s1 = (uint128_t)d0 * f1 + (uint128_t)d4 * f2 + (uint128_t)d3 * f3;
  uint128_t s2 = (uint128_t)d0 * f2 + (uint128_t)f1 * f1 + (uint128_t)d4 * f3;
  uint128_t s3 = (uint128_t)d0 * f3 + (uint128_t)d1 * f2 + (uint128_t)f4 * d419;
  uint128_t s4 = (uint128_t)d0 * f4 + (uint128_t)d1 * f3 + (uint128_t)f2 * f2;
  uint128_t o00 = s0;
  uint128_t o10 = s1;
  uint128_t o20 = s2;
  uint128_t o30 = s3;
  uint128_t o40 = s4;
  uint128_t l_ = o00 + (uint128_t)(u64)0U;
  u64 tmp0 = (uint64_t)l_ & (u64)0x7ffffffffffffU;
  u64 c0 = (uint64_t)(l_ >> (u32)51U);
  uint128_t l_0 = o10 + (uint128_t)c0;
  u64 tmp1 = (uint64_t)l_0 & (u64)0x7ffffffffffffU;
  u64 c1 = (uint64_t)(l_0 >> (u32)51U);
  uint128_t l_1 = o20 + (uint128_t)c1;
  u64 tmp2 = (uint64_t)l_1 & (u64)0x7ffffffffffffU;
  u64 c2 = (uint64_t)(l_1 >> (u32)51U);
  uint128_t l_2 = o30 + (uint128_t)c2;
  u64 tmp3 = (uint64_t)l_2 & (u64)0x7ffffffffffffU;
  u64 c3 = (uint64_t)(l_2 >> (u32)51U);
  uint128_t l_3 = o40 + (uint128_t)c3;
  u64 tmp4 = (uint64_t)l_3 & (u64)0x7ffffffffffffU;
  u64 c4 = (uint64_t)(l_3 >> (u32)51U);
  u64 l_4 = tmp0 + c4 * (u64)19U;
  u64 tmp0_ = l_4 & (u64)0x7ffffffffffffU;
  u64 c5 = l_4 >> (u32)51U;
  u64 o0 = tmp0_;
  u64 o1 = tmp1 + c5;
  u64 o2 = tmp2;
  u64 o3 = tmp3;
  u64 o4 = tmp4;
  out[0U] = o0;
  out[1U] = o1;
  out[2U] = o2;
  out[3U] = o3;
  out[4U] = o4;
}

static inline void fsqr2(u64 *out, u64 *f)
{
  u64 f10 = f[0U];
  u64 f11 = f[1U];
  u64 f12 = f[2U];
  u64 f13 = f[3U];
  u64 f14 = f[4U];
  u64 f20 = f[5U];
  u64 f21 = f[6U];
  u64 f22 = f[7U];
  u64 f23 = f[8U];
  u64 f24 = f[9U];
  u64 d00 = (u64)2U * f10;
  u64 d10 = (u64)2U * f11;
  u64 d20 = (u64)38U * f12;
  u64 d30 = (u64)19U * f13;
  u64 d4190 = (u64)19U * f14;
  u64 d40 = (u64)2U * d4190;
  uint128_t s00 = (uint128_t)f10 * f10 + (uint128_t)d40 * f11 + (uint128_t)d20 * f13;
  uint128_t s10 = (uint128_t)d00 * f11 + (uint128_t)d40 * f12 + (uint128_t)d30 * f13;
  uint128_t s20 = (uint128_t)d00 * f12 + (uint128_t)f11 * f11 + (uint128_t)d40 * f13;
  uint128_t s30 = (uint128_t)d00 * f13 + (uint128_t)d10 * f12 + (uint128_t)f14 * d4190;
  uint128_t s40 = (uint128_t)d00 * f14 + (uint128_t)d10 * f13 + (uint128_t)f12 * f12;
  uint128_t o100 = s00;
  uint128_t o110 = s10;
  uint128_t o120 = s20;
  uint128_t o130 = s30;
  uint128_t o140 = s40;
  u64 d0 = (u64)2U * f20;
  u64 d1 = (u64)2U * f21;
  u64 d2 = (u64)38U * f22;
  u64 d3 = (u64)19U * f23;
  u64 d419 = (u64)19U * f24;
  u64 d4 = (u64)2U * d419;
  uint128_t s0 = (uint128_t)f20 * f20 + (uint128_t)d4 * f21 + (uint128_t)d2 * f23;
  uint128_t s1 = (uint128_t)d0 * f21 + (uint128_t)d4 * f22 + (uint128_t)d3 * f23;
  uint128_t s2 = (uint128_t)d0 * f22 + (uint128_t)f21 * f21 + (uint128_t)d4 * f23;
  uint128_t s3 = (uint128_t)d0 * f23 + (uint128_t)d1 * f22 + (uint128_t)f24 * d419;
  uint128_t s4 = (uint128_t)d0 * f24 + (uint128_t)d1 * f23 + (uint128_t)f22 * f22;
  uint128_t o200 = s0;
  uint128_t o210 = s1;
  uint128_t o220 = s2;
  uint128_t o230 = s3;
  uint128_t o240 = s4;
  uint128_t l_ = o100 + (uint128_t)(u64)0U;
  u64 tmp00 = (uint64_t)l_ & (u64)0x7ffffffffffffU;
  u64 c00 = (uint64_t)(l_ >> (u32)51U);
  uint128_t l_0 = o110 + (uint128_t)c00;
  u64 tmp10 = (uint64_t)l_0 & (u64)0x7ffffffffffffU;
  u64 c10 = (uint64_t)(l_0 >> (u32)51U);
  uint128_t l_1 = o120 + (uint128_t)c10;
  u64 tmp20 = (uint64_t)l_1 & (u64)0x7ffffffffffffU;
  u64 c20 = (uint64_t)(l_1 >> (u32)51U);
  uint128_t l_2 = o130 + (uint128_t)c20;
  u64 tmp30 = (uint64_t)l_2 & (u64)0x7ffffffffffffU;
  u64 c30 = (uint64_t)(l_2 >> (u32)51U);
  uint128_t l_3 = o140 + (uint128_t)c30;
  u64 tmp40 = (uint64_t)l_3 & (u64)0x7ffffffffffffU;
  u64 c40 = (uint64_t)(l_3 >> (u32)51U);
  u64 l_4 = tmp00 + c40 * (u64)19U;
  u64 tmp0_ = l_4 & (u64)0x7ffffffffffffU;
  u64 c50 = l_4 >> (u32)51U;
  u64 o101 = tmp0_;
  u64 o111 = tmp10 + c50;
  u64 o121 = tmp20;
  u64 o131 = tmp30;
  u64 o141 = tmp40;
  uint128_t l_5 = o200 + (uint128_t)(u64)0U;
  u64 tmp0 = (uint64_t)l_5 & (u64)0x7ffffffffffffU;
  u64 c0 = (uint64_t)(l_5 >> (u32)51U);
  uint128_t l_6 = o210 + (uint128_t)c0;
  u64 tmp1 = (uint64_t)l_6 & (u64)0x7ffffffffffffU;
  u64 c1 = (uint64_t)(l_6 >> (u32)51U);
  uint128_t l_7 = o220 + (uint128_t)c1;
  u64 tmp2 = (uint64_t)l_7 & (u64)0x7ffffffffffffU;
  u64 c2 = (uint64_t)(l_7 >> (u32)51U);
  uint128_t l_8 = o230 + (uint128_t)c2;
  u64 tmp3 = (uint64_t)l_8 & (u64)0x7ffffffffffffU;
  u64 c3 = (uint64_t)(l_8 >> (u32)51U);
  uint128_t l_9 = o240 + (uint128_t)c3;
  u64 tmp4 = (uint64_t)l_9 & (u64)0x7ffffffffffffU;
  u64 c4 = (uint64_t)(l_9 >> (u32)51U);
  u64 l_10 = tmp0 + c4 * (u64)19U;
  u64 tmp0_0 = l_10 & (u64)0x7ffffffffffffU;
  u64 c5 = l_10 >> (u32)51U;
  u64 o201 = tmp0_0;
  u64 o211 = tmp1 + c5;
  u64 o221 = tmp2;
  u64 o231 = tmp3;
  u64 o241 = tmp4;
  u64 o10 = o101;
  u64 o11 = o111;
  u64 o12 = o121;
  u64 o13 = o131;
  u64 o14 = o141;
  u64 o20 = o201;
  u64 o21 = o211;
  u64 o22 = o221;
  u64 o23 = o231;
  u64 o24 = o241;
  out[0U] = o10;
  out[1U] = o11;
  out[2U] = o12;
  out[3U] = o13;
  out[4U] = o14;
  out[5U] = o20;
  out[6U] = o21;
  out[7U] = o22;
  out[8U] = o23;
  out[9U] = o24;
}

static void store_felem(u64 *u64s, u64 *f)
{
  u64 f0 = f[0U];
  u64 f1 = f[1U];
  u64 f2 = f[2U];
  u64 f3 = f[3U];
  u64 f4 = f[4U];
  u64 l_ = f0 + (u64)0U;
  u64 tmp0 = l_ & (u64)0x7ffffffffffffU;
  u64 c0 = l_ >> (u32)51U;
  u64 l_0 = f1 + c0;
  u64 tmp1 = l_0 & (u64)0x7ffffffffffffU;
  u64 c1 = l_0 >> (u32)51U;
  u64 l_1 = f2 + c1;
  u64 tmp2 = l_1 & (u64)0x7ffffffffffffU;
  u64 c2 = l_1 >> (u32)51U;
  u64 l_2 = f3 + c2;
  u64 tmp3 = l_2 & (u64)0x7ffffffffffffU;
  u64 c3 = l_2 >> (u32)51U;
  u64 l_3 = f4 + c3;
  u64 tmp4 = l_3 & (u64)0x7ffffffffffffU;
  u64 c4 = l_3 >> (u32)51U;
  u64 l_4 = tmp0 + c4 * (u64)19U;
  u64 tmp0_ = l_4 & (u64)0x7ffffffffffffU;
  u64 c5 = l_4 >> (u32)51U;
  u64 f01 = tmp0_;
  u64 f11 = tmp1 + c5;
  u64 f21 = tmp2;
  u64 f31 = tmp3;
  u64 f41 = tmp4;
  u64 m0 = FStar_UInt64_gte_mask(f01, (u64)0x7ffffffffffedU);
  u64 m1 = FStar_UInt64_eq_mask(f11, (u64)0x7ffffffffffffU);
  u64 m2 = FStar_UInt64_eq_mask(f21, (u64)0x7ffffffffffffU);
  u64 m3 = FStar_UInt64_eq_mask(f31, (u64)0x7ffffffffffffU);
  u64 m4 = FStar_UInt64_eq_mask(f41, (u64)0x7ffffffffffffU);
  u64 mask = (((m0 & m1) & m2) & m3) & m4;
  u64 f0_ = f01 - (mask & (u64)0x7ffffffffffedU);
  u64 f1_ = f11 - (mask & (u64)0x7ffffffffffffU);
  u64 f2_ = f21 - (mask & (u64)0x7ffffffffffffU);
  u64 f3_ = f31 - (mask & (u64)0x7ffffffffffffU);
  u64 f4_ = f41 - (mask & (u64)0x7ffffffffffffU);
  u64 f02 = f0_;
  u64 f12 = f1_;
  u64 f22 = f2_;
  u64 f32 = f3_;
  u64 f42 = f4_;
  u64 o00 = f02 | f12 << (u32)51U;
  u64 o10 = f12 >> (u32)13U | f22 << (u32)38U;
  u64 o20 = f22 >> (u32)26U | f32 << (u32)25U;
  u64 o30 = f32 >> (u32)39U | f42 << (u32)12U;
  u64 o0 = o00;
  u64 o1 = o10;
  u64 o2 = o20;
  u64 o3 = o30;
  u64s[0U] = o0;
  u64s[1U] = o1;
  u64s[2U] = o2;
  u64s[3U] = o3;
}

static inline void cswap2(u64 bit, u64 *p1, u64 *p2)
{
  u64 mask = (u64)0U - bit;
  u32 i;
  for (i = (u32)0U; i < (u32)10U; i++)
  {
    u64 dummy = mask & (p1[i] ^ p2[i]);
    p1[i] = p1[i] ^ dummy;
    p2[i] = p2[i] ^ dummy;
  }
}

static const u8 g25519[32U] = { (u8)9U };

static void point_add_and_double(u64 *q, u64 *p01_tmp1, uint128_t *tmp2)
{
  u64 *nq = p01_tmp1;
  u64 *nq_p1 = p01_tmp1 + (u32)10U;
  u64 *tmp1 = p01_tmp1 + (u32)20U;
  u64 *x1 = q;
  u64 *x2 = nq;
  u64 *z2 = nq + (u32)5U;
  u64 *z3 = nq_p1 + (u32)5U;
  u64 *a = tmp1;
  u64 *b = tmp1 + (u32)5U;
  u64 *ab = tmp1;
  u64 *dc = tmp1 + (u32)10U;
  u64 *x3;
  u64 *z31;
  u64 *d0;
  u64 *c0;
  u64 *a1;
  u64 *b1;
  u64 *d;
  u64 *c;
  u64 *ab1;
  u64 *dc1;
  Hacl_Impl_Curve25519_Field51_fadd(a, x2, z2);
  Hacl_Impl_Curve25519_Field51_fsub(b, x2, z2);
  x3 = nq_p1;
  z31 = nq_p1 + (u32)5U;
  d0 = dc;
  c0 = dc + (u32)5U;
  Hacl_Impl_Curve25519_Field51_fadd(c0, x3, z31);
  Hacl_Impl_Curve25519_Field51_fsub(d0, x3, z31);
  fmul2(dc, dc, ab);
  Hacl_Impl_Curve25519_Field51_fadd(x3, d0, c0);
  Hacl_Impl_Curve25519_Field51_fsub(z31, d0, c0);
  a1 = tmp1;
  b1 = tmp1 + (u32)5U;
  d = tmp1 + (u32)10U;
  c = tmp1 + (u32)15U;
  ab1 = tmp1;
  dc1 = tmp1 + (u32)10U;
  fsqr2(dc1, ab1);
  fsqr2(nq_p1, nq_p1);
  a1[0U] = c[0U];
  a1[1U] = c[1U];
  a1[2U] = c[2U];
  a1[3U] = c[3U];
  a1[4U] = c[4U];
  Hacl_Impl_Curve25519_Field51_fsub(c, d, c);
  Hacl_Impl_Curve25519_Field51_fmul1(b1, c, (u64)121665U);
  Hacl_Impl_Curve25519_Field51_fadd(b1, b1, d);
  fmul2(nq, dc1, ab1);
  Hacl_Impl_Curve25519_Field51_fmul(z3, z3, x1, tmp2);
}

static void point_double(u64 *nq, u64 *tmp1, uint128_t *tmp2)
{
  u64 *x2 = nq;
  u64 *z2 = nq + (u32)5U;
  u64 *a = tmp1;
  u64 *b = tmp1 + (u32)5U;
  u64 *d = tmp1 + (u32)10U;
  u64 *c = tmp1 + (u32)15U;
  u64 *ab = tmp1;
  u64 *dc = tmp1 + (u32)10U;
  Hacl_Impl_Curve25519_Field51_fadd(a, x2, z2);
  Hacl_Impl_Curve25519_Field51_fsub(b, x2, z2);
  fsqr2(dc, ab);
  a[0U] = c[0U];
  a[1U] = c[1U];
  a[2U] = c[2U];
  a[3U] = c[3U];
  a[4U] = c[4U];
  Hacl_Impl_Curve25519_Field51_fsub(c, d, c);
  Hacl_Impl_Curve25519_Field51_fmul1(b, c, (u64)121665U);
  Hacl_Impl_Curve25519_Field51_fadd(b, b, d);
  fmul2(nq, dc, ab);
}

static void montgomery_ladder(u64 *out, u8 *key, u64 *init)
{
  uint128_t tmp2[10U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)10U; ++_i)
      tmp2[_i] = (uint128_t)(u64)0U;
  }
  {
    u64 p01_tmp1_swap[41U] = { 0U };
    u64 *p0 = p01_tmp1_swap;
    u64 *p01 = p01_tmp1_swap;
    u64 *p03 = p01;
    u64 *p11 = p01 + (u32)10U;
    u64 *x0;
    u64 *z0;
    u64 *p01_tmp1;
    u64 *p01_tmp11;
    u64 *nq10;
    u64 *nq_p11;
    u64 *swap;
    u64 sw0;
    u64 *nq1;
    u64 *tmp1;
    memcpy(p11, init, (u32)10U * sizeof (u64));
    x0 = p03;
    z0 = p03 + (u32)5U;
    x0[0U] = (u64)1U;
    x0[1U] = (u64)0U;
    x0[2U] = (u64)0U;
    x0[3U] = (u64)0U;
    x0[4U] = (u64)0U;
    z0[0U] = (u64)0U;
    z0[1U] = (u64)0U;
    z0[2U] = (u64)0U;
    z0[3U] = (u64)0U;
    z0[4U] = (u64)0U;
    p01_tmp1 = p01_tmp1_swap;
    p01_tmp11 = p01_tmp1_swap;
    nq10 = p01_tmp1_swap;
    nq_p11 = p01_tmp1_swap + (u32)10U;
    swap = p01_tmp1_swap + (u32)40U;
    cswap2((u64)1U, nq10, nq_p11);
    point_add_and_double(init, p01_tmp11, tmp2);
    swap[0U] = (u64)1U;
    {
      u32 i;
      for (i = (u32)0U; i < (u32)251U; i++)
      {
        u64 *p01_tmp12 = p01_tmp1_swap;
        u64 *swap1 = p01_tmp1_swap + (u32)40U;
        u64 *nq2 = p01_tmp12;
        u64 *nq_p12 = p01_tmp12 + (u32)10U;
        u64 bit = (u64)(key[((u32)253U - i) / (u32)8U] >> ((u32)253U - i) % (u32)8U & (u8)1U);
        u64 sw = swap1[0U] ^ bit;
        cswap2(sw, nq2, nq_p12);
        point_add_and_double(init, p01_tmp12, tmp2);
        swap1[0U] = bit;
      }
    }
    sw0 = swap[0U];
    cswap2(sw0, nq10, nq_p11);
    nq1 = p01_tmp1;
    tmp1 = p01_tmp1 + (u32)20U;
    point_double(nq1, tmp1, tmp2);
    point_double(nq1, tmp1, tmp2);
    point_double(nq1, tmp1, tmp2);
    memcpy(out, p0, (u32)10U * sizeof (u64));
  }
}

void Hacl_Curve25519_51_fsquare_times(u64 *o, u64 *inp, uint128_t *tmp, u32 n)
{
  u32 i;
  Hacl_Impl_Curve25519_Field51_fsqr(o, inp, tmp);
  for (i = (u32)0U; i < n - (u32)1U; i++)
    Hacl_Impl_Curve25519_Field51_fsqr(o, o, tmp);
}

void Hacl_Curve25519_51_finv(u64 *o, u64 *i, uint128_t *tmp)
{
  u64 t1[20U] = { 0U };
  u64 *a1 = t1;
  u64 *b10 = t1 + (u32)5U;
  u64 *t010 = t1 + (u32)15U;
  uint128_t *tmp10 = tmp;
  u64 *b11;
  u64 *c10;
  u64 *t011;
  uint128_t *tmp11;
  u64 *b1;
  u64 *c1;
  u64 *t01;
  uint128_t *tmp1;
  u64 *a;
  u64 *t0;
  Hacl_Curve25519_51_fsquare_times(a1, i, tmp10, (u32)1U);
  Hacl_Curve25519_51_fsquare_times(t010, a1, tmp10, (u32)2U);
  Hacl_Impl_Curve25519_Field51_fmul(b10, t010, i, tmp);
  Hacl_Impl_Curve25519_Field51_fmul(a1, b10, a1, tmp);
  Hacl_Curve25519_51_fsquare_times(t010, a1, tmp10, (u32)1U);
  Hacl_Impl_Curve25519_Field51_fmul(b10, t010, b10, tmp);
  Hacl_Curve25519_51_fsquare_times(t010, b10, tmp10, (u32)5U);
  Hacl_Impl_Curve25519_Field51_fmul(b10, t010, b10, tmp);
  b11 = t1 + (u32)5U;
  c10 = t1 + (u32)10U;
  t011 = t1 + (u32)15U;
  tmp11 = tmp;
  Hacl_Curve25519_51_fsquare_times(t011, b11, tmp11, (u32)10U);
  Hacl_Impl_Curve25519_Field51_fmul(c10, t011, b11, tmp);
  Hacl_Curve25519_51_fsquare_times(t011, c10, tmp11, (u32)20U);
  Hacl_Impl_Curve25519_Field51_fmul(t011, t011, c10, tmp);
  Hacl_Curve25519_51_fsquare_times(t011, t011, tmp11, (u32)10U);
  Hacl_Impl_Curve25519_Field51_fmul(b11, t011, b11, tmp);
  Hacl_Curve25519_51_fsquare_times(t011, b11, tmp11, (u32)50U);
  Hacl_Impl_Curve25519_Field51_fmul(c10, t011, b11, tmp);
  b1 = t1 + (u32)5U;
  c1 = t1 + (u32)10U;
  t01 = t1 + (u32)15U;
  tmp1 = tmp;
  Hacl_Curve25519_51_fsquare_times(t01, c1, tmp1, (u32)100U);
  Hacl_Impl_Curve25519_Field51_fmul(t01, t01, c1, tmp);
  Hacl_Curve25519_51_fsquare_times(t01, t01, tmp1, (u32)50U);
  Hacl_Impl_Curve25519_Field51_fmul(t01, t01, b1, tmp);
  Hacl_Curve25519_51_fsquare_times(t01, t01, tmp1, (u32)5U);
  a = t1;
  t0 = t1 + (u32)15U;
  Hacl_Impl_Curve25519_Field51_fmul(o, t0, a, tmp);
}

static void encode_point(u8 *o, u64 *i)
{
  u64 *x = i;
  u64 *z = i + (u32)5U;
  u64 tmp[5U] = { 0U };
  u64 u64s[4U] = { 0U };
  uint128_t tmp_w[10U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)10U; ++_i)
      tmp_w[_i] = (uint128_t)(u64)0U;
  }
  Hacl_Curve25519_51_finv(tmp, z, tmp_w);
  Hacl_Impl_Curve25519_Field51_fmul(tmp, tmp, x, tmp_w);
  store_felem(u64s, tmp);
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < (u32)4U; i0++)
      store64_le(o + i0 * (u32)8U, u64s[i0]);
  }
}

void Hacl_Curve25519_51_scalarmult(u8 *out, u8 *priv, u8 *pub)
{
  u64 init[10U] = { 0U };
  u64 tmp[4U] = { 0U };
  u64 tmp3;
  u64 *x;
  u64 *z;
  u64 f0l;
  u64 f0h;
  u64 f1l;
  u64 f1h;
  u64 f2l;
  u64 f2h;
  u64 f3l;
  u64 f3h;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)4U; i++)
    {
      u64 *os = tmp;
      u8 *bj = pub + i * (u32)8U;
      u64 u = load64_le(bj);
      u64 r = u;
      u64 x0 = r;
      os[i] = x0;
    }
  }
  tmp3 = tmp[3U];
  tmp[3U] = tmp3 & (u64)0x7fffffffffffffffU;
  x = init;
  z = init + (u32)5U;
  z[0U] = (u64)1U;
  z[1U] = (u64)0U;
  z[2U] = (u64)0U;
  z[3U] = (u64)0U;
  z[4U] = (u64)0U;
  f0l = tmp[0U] & (u64)0x7ffffffffffffU;
  f0h = tmp[0U] >> (u32)51U;
  f1l = (tmp[1U] & (u64)0x3fffffffffU) << (u32)13U;
  f1h = tmp[1U] >> (u32)38U;
  f2l = (tmp[2U] & (u64)0x1ffffffU) << (u32)26U;
  f2h = tmp[2U] >> (u32)25U;
  f3l = (tmp[3U] & (u64)0xfffU) << (u32)39U;
  f3h = tmp[3U] >> (u32)12U;
  x[0U] = f0l;
  x[1U] = f0h | f1l;
  x[2U] = f1h | f2l;
  x[3U] = f2h | f3l;
  x[4U] = f3h;
  montgomery_ladder(init, priv, init);
  encode_point(out, init);
}

void Hacl_Curve25519_51_secret_to_public(u8 *pub, u8 *priv)
{
  u8 basepoint[32U] = { 0U };
  {
    u32 i;
    for (i = (u32)0U; i < (u32)32U; i++)
    {
      u8 *os = basepoint;
      u8 x = g25519[i];
      os[i] = x;
    }
  }
  Hacl_Curve25519_51_scalarmult(pub, priv, basepoint);
}

bool Hacl_Curve25519_51_ecdh(u8 *out, u8 *priv, u8 *pub)
{
  u8 zeros[32U] = { 0U };
  Hacl_Curve25519_51_scalarmult(out, priv, pub);
  {
    u8 res = (u8)255U;
    u8 z;
    bool r;
    {
      u32 i;
      for (i = (u32)0U; i < (u32)32U; i++)
      {
        u8 uu____0 = FStar_UInt8_eq_mask(out[i], zeros[i]);
        res = uu____0 & res;
      }
    }
    z = res;
    r = z == (u8)255U;
    return !r;
  }
}

