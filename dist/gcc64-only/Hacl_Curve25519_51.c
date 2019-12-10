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

inline void Hacl_Impl_Curve25519_Field51_fadd(uint64_t *out, uint64_t *f1, uint64_t *f2)
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

inline void Hacl_Impl_Curve25519_Field51_fsub(uint64_t *out, uint64_t *f1, uint64_t *f2)
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

inline void
Hacl_Impl_Curve25519_Field51_fmul(
  uint64_t *out,
  uint64_t *f1,
  uint64_t *f2,
  uint128_t *uu____2959
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
  uint128_t l_ = tmp_w0 + (uint128_t)(uint64_t)0U;
  uint64_t tmp01 = (uint64_t)l_ & (uint64_t)0x7ffffffffffffU;
  uint64_t c0 = (uint64_t)(l_ >> (uint32_t)51U);
  uint128_t l_0 = tmp_w1 + (uint128_t)c0;
  uint64_t tmp11 = (uint64_t)l_0 & (uint64_t)0x7ffffffffffffU;
  uint64_t c1 = (uint64_t)(l_0 >> (uint32_t)51U);
  uint128_t l_1 = tmp_w2 + (uint128_t)c1;
  uint64_t tmp21 = (uint64_t)l_1 & (uint64_t)0x7ffffffffffffU;
  uint64_t c2 = (uint64_t)(l_1 >> (uint32_t)51U);
  uint128_t l_2 = tmp_w3 + (uint128_t)c2;
  uint64_t tmp31 = (uint64_t)l_2 & (uint64_t)0x7ffffffffffffU;
  uint64_t c3 = (uint64_t)(l_2 >> (uint32_t)51U);
  uint128_t l_3 = tmp_w4 + (uint128_t)c3;
  uint64_t tmp41 = (uint64_t)l_3 & (uint64_t)0x7ffffffffffffU;
  uint64_t c4 = (uint64_t)(l_3 >> (uint32_t)51U);
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

inline static void
Hacl_Impl_Curve25519_Field51_fmul2(
  uint64_t *out,
  uint64_t *f1,
  uint64_t *f2,
  uint128_t *uu____4281
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
  uint64_t f30 = f1[5U];
  uint64_t f31 = f1[6U];
  uint64_t f32 = f1[7U];
  uint64_t f33 = f1[8U];
  uint64_t f34 = f1[9U];
  uint64_t f40 = f2[5U];
  uint64_t f41 = f2[6U];
  uint64_t f42 = f2[7U];
  uint64_t f43 = f2[8U];
  uint64_t f44 = f2[9U];
  uint64_t tmp11 = f21 * (uint64_t)19U;
  uint64_t tmp12 = f22 * (uint64_t)19U;
  uint64_t tmp13 = f23 * (uint64_t)19U;
  uint64_t tmp14 = f24 * (uint64_t)19U;
  uint64_t tmp21 = f41 * (uint64_t)19U;
  uint64_t tmp22 = f42 * (uint64_t)19U;
  uint64_t tmp23 = f43 * (uint64_t)19U;
  uint64_t tmp24 = f44 * (uint64_t)19U;
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
  uint128_t l_ = tmp_w10 + (uint128_t)(uint64_t)0U;
  uint64_t tmp00 = (uint64_t)l_ & (uint64_t)0x7ffffffffffffU;
  uint64_t c00 = (uint64_t)(l_ >> (uint32_t)51U);
  uint128_t l_0 = tmp_w11 + (uint128_t)c00;
  uint64_t tmp10 = (uint64_t)l_0 & (uint64_t)0x7ffffffffffffU;
  uint64_t c10 = (uint64_t)(l_0 >> (uint32_t)51U);
  uint128_t l_1 = tmp_w12 + (uint128_t)c10;
  uint64_t tmp20 = (uint64_t)l_1 & (uint64_t)0x7ffffffffffffU;
  uint64_t c20 = (uint64_t)(l_1 >> (uint32_t)51U);
  uint128_t l_2 = tmp_w13 + (uint128_t)c20;
  uint64_t tmp30 = (uint64_t)l_2 & (uint64_t)0x7ffffffffffffU;
  uint64_t c30 = (uint64_t)(l_2 >> (uint32_t)51U);
  uint128_t l_3 = tmp_w14 + (uint128_t)c30;
  uint64_t tmp40 = (uint64_t)l_3 & (uint64_t)0x7ffffffffffffU;
  uint64_t c40 = (uint64_t)(l_3 >> (uint32_t)51U);
  uint64_t l_4 = tmp00 + c40 * (uint64_t)19U;
  uint64_t tmp0_ = l_4 & (uint64_t)0x7ffffffffffffU;
  uint64_t c50 = l_4 >> (uint32_t)51U;
  uint64_t o100 = tmp0_;
  uint64_t o112 = tmp10 + c50;
  uint64_t o122 = tmp20;
  uint64_t o132 = tmp30;
  uint64_t o142 = tmp40;
  uint128_t l_5 = tmp_w20 + (uint128_t)(uint64_t)0U;
  uint64_t tmp0 = (uint64_t)l_5 & (uint64_t)0x7ffffffffffffU;
  uint64_t c0 = (uint64_t)(l_5 >> (uint32_t)51U);
  uint128_t l_6 = tmp_w21 + (uint128_t)c0;
  uint64_t tmp1 = (uint64_t)l_6 & (uint64_t)0x7ffffffffffffU;
  uint64_t c1 = (uint64_t)(l_6 >> (uint32_t)51U);
  uint128_t l_7 = tmp_w22 + (uint128_t)c1;
  uint64_t tmp2 = (uint64_t)l_7 & (uint64_t)0x7ffffffffffffU;
  uint64_t c2 = (uint64_t)(l_7 >> (uint32_t)51U);
  uint128_t l_8 = tmp_w23 + (uint128_t)c2;
  uint64_t tmp3 = (uint64_t)l_8 & (uint64_t)0x7ffffffffffffU;
  uint64_t c3 = (uint64_t)(l_8 >> (uint32_t)51U);
  uint128_t l_9 = tmp_w24 + (uint128_t)c3;
  uint64_t tmp4 = (uint64_t)l_9 & (uint64_t)0x7ffffffffffffU;
  uint64_t c4 = (uint64_t)(l_9 >> (uint32_t)51U);
  uint64_t l_10 = tmp0 + c4 * (uint64_t)19U;
  uint64_t tmp0_0 = l_10 & (uint64_t)0x7ffffffffffffU;
  uint64_t c5 = l_10 >> (uint32_t)51U;
  uint64_t o200 = tmp0_0;
  uint64_t o212 = tmp1 + c5;
  uint64_t o222 = tmp2;
  uint64_t o232 = tmp3;
  uint64_t o242 = tmp4;
  uint64_t o10 = o100;
  uint64_t o11 = o112;
  uint64_t o12 = o122;
  uint64_t o13 = o132;
  uint64_t o14 = o142;
  uint64_t o20 = o200;
  uint64_t o21 = o212;
  uint64_t o22 = o222;
  uint64_t o23 = o232;
  uint64_t o24 = o242;
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

inline void Hacl_Impl_Curve25519_Field51_fmul1(uint64_t *out, uint64_t *f1, uint64_t f2)
{
  uint64_t f10 = f1[0U];
  uint64_t f11 = f1[1U];
  uint64_t f12 = f1[2U];
  uint64_t f13 = f1[3U];
  uint64_t f14 = f1[4U];
  uint128_t tmp_w0 = (uint128_t)f2 * f10;
  uint128_t tmp_w1 = (uint128_t)f2 * f11;
  uint128_t tmp_w2 = (uint128_t)f2 * f12;
  uint128_t tmp_w3 = (uint128_t)f2 * f13;
  uint128_t tmp_w4 = (uint128_t)f2 * f14;
  uint128_t l_ = tmp_w0 + (uint128_t)(uint64_t)0U;
  uint64_t tmp0 = (uint64_t)l_ & (uint64_t)0x7ffffffffffffU;
  uint64_t c0 = (uint64_t)(l_ >> (uint32_t)51U);
  uint128_t l_0 = tmp_w1 + (uint128_t)c0;
  uint64_t tmp1 = (uint64_t)l_0 & (uint64_t)0x7ffffffffffffU;
  uint64_t c1 = (uint64_t)(l_0 >> (uint32_t)51U);
  uint128_t l_1 = tmp_w2 + (uint128_t)c1;
  uint64_t tmp2 = (uint64_t)l_1 & (uint64_t)0x7ffffffffffffU;
  uint64_t c2 = (uint64_t)(l_1 >> (uint32_t)51U);
  uint128_t l_2 = tmp_w3 + (uint128_t)c2;
  uint64_t tmp3 = (uint64_t)l_2 & (uint64_t)0x7ffffffffffffU;
  uint64_t c3 = (uint64_t)(l_2 >> (uint32_t)51U);
  uint128_t l_3 = tmp_w4 + (uint128_t)c3;
  uint64_t tmp4 = (uint64_t)l_3 & (uint64_t)0x7ffffffffffffU;
  uint64_t c4 = (uint64_t)(l_3 >> (uint32_t)51U);
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

inline void
Hacl_Impl_Curve25519_Field51_fsqr(uint64_t *out, uint64_t *f, uint128_t *uu____6941)
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
  uint128_t l_ = o00 + (uint128_t)(uint64_t)0U;
  uint64_t tmp0 = (uint64_t)l_ & (uint64_t)0x7ffffffffffffU;
  uint64_t c0 = (uint64_t)(l_ >> (uint32_t)51U);
  uint128_t l_0 = o10 + (uint128_t)c0;
  uint64_t tmp1 = (uint64_t)l_0 & (uint64_t)0x7ffffffffffffU;
  uint64_t c1 = (uint64_t)(l_0 >> (uint32_t)51U);
  uint128_t l_1 = o20 + (uint128_t)c1;
  uint64_t tmp2 = (uint64_t)l_1 & (uint64_t)0x7ffffffffffffU;
  uint64_t c2 = (uint64_t)(l_1 >> (uint32_t)51U);
  uint128_t l_2 = o30 + (uint128_t)c2;
  uint64_t tmp3 = (uint64_t)l_2 & (uint64_t)0x7ffffffffffffU;
  uint64_t c3 = (uint64_t)(l_2 >> (uint32_t)51U);
  uint128_t l_3 = o40 + (uint128_t)c3;
  uint64_t tmp4 = (uint64_t)l_3 & (uint64_t)0x7ffffffffffffU;
  uint64_t c4 = (uint64_t)(l_3 >> (uint32_t)51U);
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

inline static void
Hacl_Impl_Curve25519_Field51_fsqr2(uint64_t *out, uint64_t *f, uint128_t *uu____7692)
{
  uint64_t f10 = f[0U];
  uint64_t f11 = f[1U];
  uint64_t f12 = f[2U];
  uint64_t f13 = f[3U];
  uint64_t f14 = f[4U];
  uint64_t f20 = f[5U];
  uint64_t f21 = f[6U];
  uint64_t f22 = f[7U];
  uint64_t f23 = f[8U];
  uint64_t f24 = f[9U];
  uint64_t d00 = (uint64_t)2U * f10;
  uint64_t d10 = (uint64_t)2U * f11;
  uint64_t d20 = (uint64_t)38U * f12;
  uint64_t d30 = (uint64_t)19U * f13;
  uint64_t d4190 = (uint64_t)19U * f14;
  uint64_t d40 = (uint64_t)2U * d4190;
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
  uint64_t d0 = (uint64_t)2U * f20;
  uint64_t d1 = (uint64_t)2U * f21;
  uint64_t d2 = (uint64_t)38U * f22;
  uint64_t d3 = (uint64_t)19U * f23;
  uint64_t d419 = (uint64_t)19U * f24;
  uint64_t d4 = (uint64_t)2U * d419;
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
  uint128_t l_ = o100 + (uint128_t)(uint64_t)0U;
  uint64_t tmp00 = (uint64_t)l_ & (uint64_t)0x7ffffffffffffU;
  uint64_t c00 = (uint64_t)(l_ >> (uint32_t)51U);
  uint128_t l_0 = o110 + (uint128_t)c00;
  uint64_t tmp10 = (uint64_t)l_0 & (uint64_t)0x7ffffffffffffU;
  uint64_t c10 = (uint64_t)(l_0 >> (uint32_t)51U);
  uint128_t l_1 = o120 + (uint128_t)c10;
  uint64_t tmp20 = (uint64_t)l_1 & (uint64_t)0x7ffffffffffffU;
  uint64_t c20 = (uint64_t)(l_1 >> (uint32_t)51U);
  uint128_t l_2 = o130 + (uint128_t)c20;
  uint64_t tmp30 = (uint64_t)l_2 & (uint64_t)0x7ffffffffffffU;
  uint64_t c30 = (uint64_t)(l_2 >> (uint32_t)51U);
  uint128_t l_3 = o140 + (uint128_t)c30;
  uint64_t tmp40 = (uint64_t)l_3 & (uint64_t)0x7ffffffffffffU;
  uint64_t c40 = (uint64_t)(l_3 >> (uint32_t)51U);
  uint64_t l_4 = tmp00 + c40 * (uint64_t)19U;
  uint64_t tmp0_ = l_4 & (uint64_t)0x7ffffffffffffU;
  uint64_t c50 = l_4 >> (uint32_t)51U;
  uint64_t o101 = tmp0_;
  uint64_t o111 = tmp10 + c50;
  uint64_t o121 = tmp20;
  uint64_t o131 = tmp30;
  uint64_t o141 = tmp40;
  uint128_t l_5 = o200 + (uint128_t)(uint64_t)0U;
  uint64_t tmp0 = (uint64_t)l_5 & (uint64_t)0x7ffffffffffffU;
  uint64_t c0 = (uint64_t)(l_5 >> (uint32_t)51U);
  uint128_t l_6 = o210 + (uint128_t)c0;
  uint64_t tmp1 = (uint64_t)l_6 & (uint64_t)0x7ffffffffffffU;
  uint64_t c1 = (uint64_t)(l_6 >> (uint32_t)51U);
  uint128_t l_7 = o220 + (uint128_t)c1;
  uint64_t tmp2 = (uint64_t)l_7 & (uint64_t)0x7ffffffffffffU;
  uint64_t c2 = (uint64_t)(l_7 >> (uint32_t)51U);
  uint128_t l_8 = o230 + (uint128_t)c2;
  uint64_t tmp3 = (uint64_t)l_8 & (uint64_t)0x7ffffffffffffU;
  uint64_t c3 = (uint64_t)(l_8 >> (uint32_t)51U);
  uint128_t l_9 = o240 + (uint128_t)c3;
  uint64_t tmp4 = (uint64_t)l_9 & (uint64_t)0x7ffffffffffffU;
  uint64_t c4 = (uint64_t)(l_9 >> (uint32_t)51U);
  uint64_t l_10 = tmp0 + c4 * (uint64_t)19U;
  uint64_t tmp0_0 = l_10 & (uint64_t)0x7ffffffffffffU;
  uint64_t c5 = l_10 >> (uint32_t)51U;
  uint64_t o201 = tmp0_0;
  uint64_t o211 = tmp1 + c5;
  uint64_t o221 = tmp2;
  uint64_t o231 = tmp3;
  uint64_t o241 = tmp4;
  uint64_t o10 = o101;
  uint64_t o11 = o111;
  uint64_t o12 = o121;
  uint64_t o13 = o131;
  uint64_t o14 = o141;
  uint64_t o20 = o201;
  uint64_t o21 = o211;
  uint64_t o22 = o221;
  uint64_t o23 = o231;
  uint64_t o24 = o241;
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

static void Hacl_Impl_Curve25519_Field51_store_felem(uint64_t *u64s, uint64_t *f)
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

inline static void
Hacl_Impl_Curve25519_Field51_cswap2(uint64_t bit, uint64_t *p1, uint64_t *p2)
{
  uint64_t mask = (uint64_t)0U - bit;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)10U; i = i + (uint32_t)1U)
  {
    uint64_t dummy = mask & (p1[i] ^ p2[i]);
    p1[i] = p1[i] ^ dummy;
    p2[i] = p2[i] ^ dummy;
  }
}

static uint8_t
Hacl_Curve25519_51_g25519[32U] =
  {
    (uint8_t)9U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U
  };

static void
Hacl_Curve25519_51_point_add_and_double(uint64_t *q, uint64_t *p01_tmp1, uint128_t *tmp2)
{
  uint64_t *nq = p01_tmp1;
  uint64_t *nq_p1 = p01_tmp1 + (uint32_t)10U;
  uint64_t *tmp1 = p01_tmp1 + (uint32_t)20U;
  uint64_t *x1 = q;
  uint64_t *x2 = nq;
  uint64_t *z2 = nq + (uint32_t)5U;
  uint64_t *z3 = nq_p1 + (uint32_t)5U;
  uint64_t *a = tmp1;
  uint64_t *b = tmp1 + (uint32_t)5U;
  uint64_t *ab = tmp1;
  uint64_t *dc = tmp1 + (uint32_t)10U;
  Hacl_Impl_Curve25519_Field51_fadd(a, x2, z2);
  Hacl_Impl_Curve25519_Field51_fsub(b, x2, z2);
  uint64_t *x3 = nq_p1;
  uint64_t *z31 = nq_p1 + (uint32_t)5U;
  uint64_t *d0 = dc;
  uint64_t *c0 = dc + (uint32_t)5U;
  Hacl_Impl_Curve25519_Field51_fadd(c0, x3, z31);
  Hacl_Impl_Curve25519_Field51_fsub(d0, x3, z31);
  Hacl_Impl_Curve25519_Field51_fmul2(dc, dc, ab, tmp2);
  Hacl_Impl_Curve25519_Field51_fadd(x3, d0, c0);
  Hacl_Impl_Curve25519_Field51_fsub(z31, d0, c0);
  uint64_t *a1 = tmp1;
  uint64_t *b1 = tmp1 + (uint32_t)5U;
  uint64_t *d = tmp1 + (uint32_t)10U;
  uint64_t *c = tmp1 + (uint32_t)15U;
  uint64_t *ab1 = tmp1;
  uint64_t *dc1 = tmp1 + (uint32_t)10U;
  Hacl_Impl_Curve25519_Field51_fsqr2(dc1, ab1, tmp2);
  Hacl_Impl_Curve25519_Field51_fsqr2(nq_p1, nq_p1, tmp2);
  a1[0U] = c[0U];
  a1[1U] = c[1U];
  a1[2U] = c[2U];
  a1[3U] = c[3U];
  a1[4U] = c[4U];
  Hacl_Impl_Curve25519_Field51_fsub(c, d, c);
  Hacl_Impl_Curve25519_Field51_fmul1(b1, c, (uint64_t)121665U);
  Hacl_Impl_Curve25519_Field51_fadd(b1, b1, d);
  Hacl_Impl_Curve25519_Field51_fmul2(nq, dc1, ab1, tmp2);
  Hacl_Impl_Curve25519_Field51_fmul(z3, z3, x1, tmp2);
}

static void Hacl_Curve25519_51_point_double(uint64_t *nq, uint64_t *tmp1, uint128_t *tmp2)
{
  uint64_t *x2 = nq;
  uint64_t *z2 = nq + (uint32_t)5U;
  uint64_t *a = tmp1;
  uint64_t *b = tmp1 + (uint32_t)5U;
  uint64_t *d = tmp1 + (uint32_t)10U;
  uint64_t *c = tmp1 + (uint32_t)15U;
  uint64_t *ab = tmp1;
  uint64_t *dc = tmp1 + (uint32_t)10U;
  Hacl_Impl_Curve25519_Field51_fadd(a, x2, z2);
  Hacl_Impl_Curve25519_Field51_fsub(b, x2, z2);
  Hacl_Impl_Curve25519_Field51_fsqr2(dc, ab, tmp2);
  a[0U] = c[0U];
  a[1U] = c[1U];
  a[2U] = c[2U];
  a[3U] = c[3U];
  a[4U] = c[4U];
  Hacl_Impl_Curve25519_Field51_fsub(c, d, c);
  Hacl_Impl_Curve25519_Field51_fmul1(b, c, (uint64_t)121665U);
  Hacl_Impl_Curve25519_Field51_fadd(b, b, d);
  Hacl_Impl_Curve25519_Field51_fmul2(nq, dc, ab, tmp2);
}

static void Hacl_Curve25519_51_montgomery_ladder(uint64_t *out, uint8_t *key, uint64_t *init1)
{
  uint128_t tmp2[10U];
  for (uint32_t _i = 0U; _i < (uint32_t)10U; ++_i)
    tmp2[_i] = (uint128_t)(uint64_t)0U;
  uint64_t p01_tmp1_swap[41U] = { 0U };
  uint64_t *p0 = p01_tmp1_swap;
  uint64_t *p01 = p01_tmp1_swap;
  uint64_t *p03 = p01;
  uint64_t *p11 = p01 + (uint32_t)10U;
  memcpy(p11, init1, (uint32_t)10U * sizeof init1[0U]);
  uint64_t *x0 = p03;
  uint64_t *z0 = p03 + (uint32_t)5U;
  x0[0U] = (uint64_t)1U;
  x0[1U] = (uint64_t)0U;
  x0[2U] = (uint64_t)0U;
  x0[3U] = (uint64_t)0U;
  x0[4U] = (uint64_t)0U;
  z0[0U] = (uint64_t)0U;
  z0[1U] = (uint64_t)0U;
  z0[2U] = (uint64_t)0U;
  z0[3U] = (uint64_t)0U;
  z0[4U] = (uint64_t)0U;
  uint64_t *p01_tmp1 = p01_tmp1_swap;
  uint64_t *p01_tmp11 = p01_tmp1_swap;
  uint64_t *nq1 = p01_tmp1_swap;
  uint64_t *nq_p11 = p01_tmp1_swap + (uint32_t)10U;
  uint64_t *swap1 = p01_tmp1_swap + (uint32_t)40U;
  Hacl_Impl_Curve25519_Field51_cswap2((uint64_t)1U, nq1, nq_p11);
  Hacl_Curve25519_51_point_add_and_double(init1, p01_tmp11, tmp2);
  swap1[0U] = (uint64_t)1U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)251U; i = i + (uint32_t)1U)
  {
    uint64_t *p01_tmp12 = p01_tmp1_swap;
    uint64_t *swap2 = p01_tmp1_swap + (uint32_t)40U;
    uint64_t *nq2 = p01_tmp12;
    uint64_t *nq_p12 = p01_tmp12 + (uint32_t)10U;
    uint64_t
    bit =
      (uint64_t)(key[((uint32_t)253U - i)
      / (uint32_t)8U]
      >> ((uint32_t)253U - i) % (uint32_t)8U
      & (uint8_t)1U);
    uint64_t sw = swap2[0U] ^ bit;
    Hacl_Impl_Curve25519_Field51_cswap2(sw, nq2, nq_p12);
    Hacl_Curve25519_51_point_add_and_double(init1, p01_tmp12, tmp2);
    swap2[0U] = bit;
  }
  uint64_t sw = swap1[0U];
  Hacl_Impl_Curve25519_Field51_cswap2(sw, nq1, nq_p11);
  uint64_t *nq10 = p01_tmp1;
  uint64_t *tmp1 = p01_tmp1 + (uint32_t)20U;
  Hacl_Curve25519_51_point_double(nq10, tmp1, tmp2);
  Hacl_Curve25519_51_point_double(nq10, tmp1, tmp2);
  Hacl_Curve25519_51_point_double(nq10, tmp1, tmp2);
  memcpy(out, p0, (uint32_t)10U * sizeof p0[0U]);
}

void Hacl_Curve25519_51_fsquare_times(uint64_t *o, uint64_t *inp, uint128_t *tmp, uint32_t n1)
{
  Hacl_Impl_Curve25519_Field51_fsqr(o, inp, tmp);
  for (uint32_t i = (uint32_t)0U; i < n1 - (uint32_t)1U; i = i + (uint32_t)1U)
  {
    Hacl_Impl_Curve25519_Field51_fsqr(o, o, tmp);
  }
}

void Hacl_Curve25519_51_finv(uint64_t *o, uint64_t *i, uint128_t *tmp)
{
  uint64_t t1[20U] = { 0U };
  uint64_t *a = t1;
  uint64_t *b = t1 + (uint32_t)5U;
  uint64_t *c = t1 + (uint32_t)10U;
  uint64_t *t00 = t1 + (uint32_t)15U;
  uint128_t *tmp1 = tmp;
  Hacl_Curve25519_51_fsquare_times(a, i, tmp1, (uint32_t)1U);
  Hacl_Curve25519_51_fsquare_times(t00, a, tmp1, (uint32_t)2U);
  Hacl_Impl_Curve25519_Field51_fmul(b, t00, i, tmp);
  Hacl_Impl_Curve25519_Field51_fmul(a, b, a, tmp);
  Hacl_Curve25519_51_fsquare_times(t00, a, tmp1, (uint32_t)1U);
  Hacl_Impl_Curve25519_Field51_fmul(b, t00, b, tmp);
  Hacl_Curve25519_51_fsquare_times(t00, b, tmp1, (uint32_t)5U);
  Hacl_Impl_Curve25519_Field51_fmul(b, t00, b, tmp);
  Hacl_Curve25519_51_fsquare_times(t00, b, tmp1, (uint32_t)10U);
  Hacl_Impl_Curve25519_Field51_fmul(c, t00, b, tmp);
  Hacl_Curve25519_51_fsquare_times(t00, c, tmp1, (uint32_t)20U);
  Hacl_Impl_Curve25519_Field51_fmul(t00, t00, c, tmp);
  Hacl_Curve25519_51_fsquare_times(t00, t00, tmp1, (uint32_t)10U);
  Hacl_Impl_Curve25519_Field51_fmul(b, t00, b, tmp);
  Hacl_Curve25519_51_fsquare_times(t00, b, tmp1, (uint32_t)50U);
  Hacl_Impl_Curve25519_Field51_fmul(c, t00, b, tmp);
  Hacl_Curve25519_51_fsquare_times(t00, c, tmp1, (uint32_t)100U);
  Hacl_Impl_Curve25519_Field51_fmul(t00, t00, c, tmp);
  Hacl_Curve25519_51_fsquare_times(t00, t00, tmp1, (uint32_t)50U);
  Hacl_Impl_Curve25519_Field51_fmul(t00, t00, b, tmp);
  Hacl_Curve25519_51_fsquare_times(t00, t00, tmp1, (uint32_t)5U);
  uint64_t *a0 = t1;
  uint64_t *t0 = t1 + (uint32_t)15U;
  Hacl_Impl_Curve25519_Field51_fmul(o, t0, a0, tmp);
}

static void Hacl_Curve25519_51_encode_point(uint8_t *o, uint64_t *i)
{
  uint64_t *x = i;
  uint64_t *z = i + (uint32_t)5U;
  uint64_t tmp[5U] = { 0U };
  uint64_t u64s[4U] = { 0U };
  uint128_t tmp_w[10U];
  for (uint32_t _i = 0U; _i < (uint32_t)10U; ++_i)
    tmp_w[_i] = (uint128_t)(uint64_t)0U;
  Hacl_Curve25519_51_finv(tmp, z, tmp_w);
  Hacl_Impl_Curve25519_Field51_fmul(tmp, tmp, x, tmp_w);
  Hacl_Impl_Curve25519_Field51_store_felem(u64s, tmp);
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0 = i0 + (uint32_t)1U)
  {
    store64_le(o + i0 * (uint32_t)8U, u64s[i0]);
  }
}

void Hacl_Curve25519_51_scalarmult(uint8_t *out, uint8_t *priv, uint8_t *pub)
{
  uint64_t init1[10U] = { 0U };
  uint64_t tmp[4U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i = i + (uint32_t)1U)
  {
    uint64_t *os = tmp;
    uint8_t *bj = pub + i * (uint32_t)8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;
  }
  uint64_t tmp3 = tmp[3U];
  tmp[3U] = tmp3 & (uint64_t)0x7fffffffffffffffU;
  uint64_t *x = init1;
  uint64_t *z = init1 + (uint32_t)5U;
  z[0U] = (uint64_t)1U;
  z[1U] = (uint64_t)0U;
  z[2U] = (uint64_t)0U;
  z[3U] = (uint64_t)0U;
  z[4U] = (uint64_t)0U;
  uint64_t f0l = tmp[0U] & (uint64_t)0x7ffffffffffffU;
  uint64_t f0h = tmp[0U] >> (uint32_t)51U;
  uint64_t f1l = (tmp[1U] & (uint64_t)0x3fffffffffU) << (uint32_t)13U;
  uint64_t f1h = tmp[1U] >> (uint32_t)38U;
  uint64_t f2l = (tmp[2U] & (uint64_t)0x1ffffffU) << (uint32_t)26U;
  uint64_t f2h = tmp[2U] >> (uint32_t)25U;
  uint64_t f3l = (tmp[3U] & (uint64_t)0xfffU) << (uint32_t)39U;
  uint64_t f3h = tmp[3U] >> (uint32_t)12U;
  x[0U] = f0l;
  x[1U] = f0h | f1l;
  x[2U] = f1h | f2l;
  x[3U] = f2h | f3l;
  x[4U] = f3h;
  Hacl_Curve25519_51_montgomery_ladder(init1, priv, init1);
  Hacl_Curve25519_51_encode_point(out, init1);
}

void Hacl_Curve25519_51_secret_to_public(uint8_t *pub, uint8_t *priv)
{
  uint8_t basepoint[32U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i = i + (uint32_t)1U)
  {
    uint8_t *os = basepoint;
    uint8_t x = Hacl_Curve25519_51_g25519[i];
    os[i] = x;
  }
  Hacl_Curve25519_51_scalarmult(pub, priv, basepoint);
}

bool Hacl_Curve25519_51_ecdh(uint8_t *out, uint8_t *priv, uint8_t *pub)
{
  uint8_t zeros1[32U] = { 0U };
  Hacl_Curve25519_51_scalarmult(out, priv, pub);
  uint8_t res = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i = i + (uint32_t)1U)
  {
    uint8_t uu____0 = FStar_UInt8_eq_mask(out[i], zeros1[i]);
    res = uu____0 & res;
  }
  uint8_t z = res;
  bool r = z == (uint8_t)255U;
  return !r;
}

