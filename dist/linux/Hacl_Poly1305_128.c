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


#include "Hacl_Poly1305_128.h"

void Hacl_Impl_Poly1305_Field32xN_128_load_acc2(Lib_IntVector_Intrinsics_vec128 *acc, u8 *b)
{
  Lib_IntVector_Intrinsics_vec128 e[5U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)5U; ++_i)
      e[_i] = Lib_IntVector_Intrinsics_vec128_zero;
  }
  {
    Lib_IntVector_Intrinsics_vec128 b10 = Lib_IntVector_Intrinsics_vec128_load_le(b);
    Lib_IntVector_Intrinsics_vec128 b2 = Lib_IntVector_Intrinsics_vec128_load_le(b + (u32)16U);
    Lib_IntVector_Intrinsics_vec128 lo = Lib_IntVector_Intrinsics_vec128_interleave_low64(b10, b2);
    Lib_IntVector_Intrinsics_vec128
    hi = Lib_IntVector_Intrinsics_vec128_interleave_high64(b10, b2);
    Lib_IntVector_Intrinsics_vec128
    f00 =
      Lib_IntVector_Intrinsics_vec128_and(lo,
        Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
    Lib_IntVector_Intrinsics_vec128
    f10 =
      Lib_IntVector_Intrinsics_vec128_and(Lib_IntVector_Intrinsics_vec128_shift_right64(lo,
          (u32)26U),
        Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
    Lib_IntVector_Intrinsics_vec128
    f20 =
      Lib_IntVector_Intrinsics_vec128_or(Lib_IntVector_Intrinsics_vec128_shift_right64(lo, (u32)52U),
        Lib_IntVector_Intrinsics_vec128_shift_left64(Lib_IntVector_Intrinsics_vec128_and(hi,
            Lib_IntVector_Intrinsics_vec128_load64((u64)0x3fffU)),
          (u32)12U));
    Lib_IntVector_Intrinsics_vec128
    f30 =
      Lib_IntVector_Intrinsics_vec128_and(Lib_IntVector_Intrinsics_vec128_shift_right64(hi,
          (u32)14U),
        Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
    Lib_IntVector_Intrinsics_vec128
    f40 = Lib_IntVector_Intrinsics_vec128_shift_right64(hi, (u32)40U);
    Lib_IntVector_Intrinsics_vec128 f02 = f00;
    Lib_IntVector_Intrinsics_vec128 f12 = f10;
    Lib_IntVector_Intrinsics_vec128 f22 = f20;
    Lib_IntVector_Intrinsics_vec128 f32 = f30;
    Lib_IntVector_Intrinsics_vec128 f42 = f40;
    u64 b1;
    Lib_IntVector_Intrinsics_vec128 mask;
    Lib_IntVector_Intrinsics_vec128 f43;
    Lib_IntVector_Intrinsics_vec128 acc0;
    Lib_IntVector_Intrinsics_vec128 acc1;
    Lib_IntVector_Intrinsics_vec128 acc2;
    Lib_IntVector_Intrinsics_vec128 acc3;
    Lib_IntVector_Intrinsics_vec128 acc4;
    Lib_IntVector_Intrinsics_vec128 e0;
    Lib_IntVector_Intrinsics_vec128 e1;
    Lib_IntVector_Intrinsics_vec128 e2;
    Lib_IntVector_Intrinsics_vec128 e3;
    Lib_IntVector_Intrinsics_vec128 e4;
    Lib_IntVector_Intrinsics_vec128 f0;
    Lib_IntVector_Intrinsics_vec128 f1;
    Lib_IntVector_Intrinsics_vec128 f2;
    Lib_IntVector_Intrinsics_vec128 f3;
    Lib_IntVector_Intrinsics_vec128 f4;
    Lib_IntVector_Intrinsics_vec128 f01;
    Lib_IntVector_Intrinsics_vec128 f11;
    Lib_IntVector_Intrinsics_vec128 f21;
    Lib_IntVector_Intrinsics_vec128 f31;
    Lib_IntVector_Intrinsics_vec128 f41;
    Lib_IntVector_Intrinsics_vec128 acc01;
    Lib_IntVector_Intrinsics_vec128 acc11;
    Lib_IntVector_Intrinsics_vec128 acc21;
    Lib_IntVector_Intrinsics_vec128 acc31;
    Lib_IntVector_Intrinsics_vec128 acc41;
    e[0U] = f02;
    e[1U] = f12;
    e[2U] = f22;
    e[3U] = f32;
    e[4U] = f42;
    b1 = (u64)0x1000000U;
    mask = Lib_IntVector_Intrinsics_vec128_load64(b1);
    f43 = e[4U];
    e[4U] = Lib_IntVector_Intrinsics_vec128_or(f43, mask);
    acc0 = acc[0U];
    acc1 = acc[1U];
    acc2 = acc[2U];
    acc3 = acc[3U];
    acc4 = acc[4U];
    e0 = e[0U];
    e1 = e[1U];
    e2 = e[2U];
    e3 = e[3U];
    e4 = e[4U];
    f0 = Lib_IntVector_Intrinsics_vec128_insert64(acc0, (u64)0U, (u32)1U);
    f1 = Lib_IntVector_Intrinsics_vec128_insert64(acc1, (u64)0U, (u32)1U);
    f2 = Lib_IntVector_Intrinsics_vec128_insert64(acc2, (u64)0U, (u32)1U);
    f3 = Lib_IntVector_Intrinsics_vec128_insert64(acc3, (u64)0U, (u32)1U);
    f4 = Lib_IntVector_Intrinsics_vec128_insert64(acc4, (u64)0U, (u32)1U);
    f01 = Lib_IntVector_Intrinsics_vec128_add64(f0, e0);
    f11 = Lib_IntVector_Intrinsics_vec128_add64(f1, e1);
    f21 = Lib_IntVector_Intrinsics_vec128_add64(f2, e2);
    f31 = Lib_IntVector_Intrinsics_vec128_add64(f3, e3);
    f41 = Lib_IntVector_Intrinsics_vec128_add64(f4, e4);
    acc01 = f01;
    acc11 = f11;
    acc21 = f21;
    acc31 = f31;
    acc41 = f41;
    acc[0U] = acc01;
    acc[1U] = acc11;
    acc[2U] = acc21;
    acc[3U] = acc31;
    acc[4U] = acc41;
  }
}

void
Hacl_Impl_Poly1305_Field32xN_128_fmul_r2_normalize(
  Lib_IntVector_Intrinsics_vec128 *out,
  Lib_IntVector_Intrinsics_vec128 *p
)
{
  Lib_IntVector_Intrinsics_vec128 *r = p;
  Lib_IntVector_Intrinsics_vec128 *r2 = p + (u32)10U;
  Lib_IntVector_Intrinsics_vec128 a0 = out[0U];
  Lib_IntVector_Intrinsics_vec128 a1 = out[1U];
  Lib_IntVector_Intrinsics_vec128 a2 = out[2U];
  Lib_IntVector_Intrinsics_vec128 a3 = out[3U];
  Lib_IntVector_Intrinsics_vec128 a4 = out[4U];
  Lib_IntVector_Intrinsics_vec128 r10 = r[0U];
  Lib_IntVector_Intrinsics_vec128 r11 = r[1U];
  Lib_IntVector_Intrinsics_vec128 r12 = r[2U];
  Lib_IntVector_Intrinsics_vec128 r13 = r[3U];
  Lib_IntVector_Intrinsics_vec128 r14 = r[4U];
  Lib_IntVector_Intrinsics_vec128 r20 = r2[0U];
  Lib_IntVector_Intrinsics_vec128 r21 = r2[1U];
  Lib_IntVector_Intrinsics_vec128 r22 = r2[2U];
  Lib_IntVector_Intrinsics_vec128 r23 = r2[3U];
  Lib_IntVector_Intrinsics_vec128 r24 = r2[4U];
  Lib_IntVector_Intrinsics_vec128
  r201 = Lib_IntVector_Intrinsics_vec128_interleave_low64(r20, r10);
  Lib_IntVector_Intrinsics_vec128
  r211 = Lib_IntVector_Intrinsics_vec128_interleave_low64(r21, r11);
  Lib_IntVector_Intrinsics_vec128
  r221 = Lib_IntVector_Intrinsics_vec128_interleave_low64(r22, r12);
  Lib_IntVector_Intrinsics_vec128
  r231 = Lib_IntVector_Intrinsics_vec128_interleave_low64(r23, r13);
  Lib_IntVector_Intrinsics_vec128
  r241 = Lib_IntVector_Intrinsics_vec128_interleave_low64(r24, r14);
  Lib_IntVector_Intrinsics_vec128 r251 = Lib_IntVector_Intrinsics_vec128_smul64(r211, (u64)5U);
  Lib_IntVector_Intrinsics_vec128 r252 = Lib_IntVector_Intrinsics_vec128_smul64(r221, (u64)5U);
  Lib_IntVector_Intrinsics_vec128 r253 = Lib_IntVector_Intrinsics_vec128_smul64(r231, (u64)5U);
  Lib_IntVector_Intrinsics_vec128 r254 = Lib_IntVector_Intrinsics_vec128_smul64(r241, (u64)5U);
  Lib_IntVector_Intrinsics_vec128 a01 = Lib_IntVector_Intrinsics_vec128_mul64(r201, a0);
  Lib_IntVector_Intrinsics_vec128 a11 = Lib_IntVector_Intrinsics_vec128_mul64(r211, a0);
  Lib_IntVector_Intrinsics_vec128 a21 = Lib_IntVector_Intrinsics_vec128_mul64(r221, a0);
  Lib_IntVector_Intrinsics_vec128 a31 = Lib_IntVector_Intrinsics_vec128_mul64(r231, a0);
  Lib_IntVector_Intrinsics_vec128 a41 = Lib_IntVector_Intrinsics_vec128_mul64(r241, a0);
  Lib_IntVector_Intrinsics_vec128
  a02 =
    Lib_IntVector_Intrinsics_vec128_add64(a01,
      Lib_IntVector_Intrinsics_vec128_mul64(r254, a1));
  Lib_IntVector_Intrinsics_vec128
  a12 =
    Lib_IntVector_Intrinsics_vec128_add64(a11,
      Lib_IntVector_Intrinsics_vec128_mul64(r201, a1));
  Lib_IntVector_Intrinsics_vec128
  a22 =
    Lib_IntVector_Intrinsics_vec128_add64(a21,
      Lib_IntVector_Intrinsics_vec128_mul64(r211, a1));
  Lib_IntVector_Intrinsics_vec128
  a32 =
    Lib_IntVector_Intrinsics_vec128_add64(a31,
      Lib_IntVector_Intrinsics_vec128_mul64(r221, a1));
  Lib_IntVector_Intrinsics_vec128
  a42 =
    Lib_IntVector_Intrinsics_vec128_add64(a41,
      Lib_IntVector_Intrinsics_vec128_mul64(r231, a1));
  Lib_IntVector_Intrinsics_vec128
  a03 =
    Lib_IntVector_Intrinsics_vec128_add64(a02,
      Lib_IntVector_Intrinsics_vec128_mul64(r253, a2));
  Lib_IntVector_Intrinsics_vec128
  a13 =
    Lib_IntVector_Intrinsics_vec128_add64(a12,
      Lib_IntVector_Intrinsics_vec128_mul64(r254, a2));
  Lib_IntVector_Intrinsics_vec128
  a23 =
    Lib_IntVector_Intrinsics_vec128_add64(a22,
      Lib_IntVector_Intrinsics_vec128_mul64(r201, a2));
  Lib_IntVector_Intrinsics_vec128
  a33 =
    Lib_IntVector_Intrinsics_vec128_add64(a32,
      Lib_IntVector_Intrinsics_vec128_mul64(r211, a2));
  Lib_IntVector_Intrinsics_vec128
  a43 =
    Lib_IntVector_Intrinsics_vec128_add64(a42,
      Lib_IntVector_Intrinsics_vec128_mul64(r221, a2));
  Lib_IntVector_Intrinsics_vec128
  a04 =
    Lib_IntVector_Intrinsics_vec128_add64(a03,
      Lib_IntVector_Intrinsics_vec128_mul64(r252, a3));
  Lib_IntVector_Intrinsics_vec128
  a14 =
    Lib_IntVector_Intrinsics_vec128_add64(a13,
      Lib_IntVector_Intrinsics_vec128_mul64(r253, a3));
  Lib_IntVector_Intrinsics_vec128
  a24 =
    Lib_IntVector_Intrinsics_vec128_add64(a23,
      Lib_IntVector_Intrinsics_vec128_mul64(r254, a3));
  Lib_IntVector_Intrinsics_vec128
  a34 =
    Lib_IntVector_Intrinsics_vec128_add64(a33,
      Lib_IntVector_Intrinsics_vec128_mul64(r201, a3));
  Lib_IntVector_Intrinsics_vec128
  a44 =
    Lib_IntVector_Intrinsics_vec128_add64(a43,
      Lib_IntVector_Intrinsics_vec128_mul64(r211, a3));
  Lib_IntVector_Intrinsics_vec128
  a05 =
    Lib_IntVector_Intrinsics_vec128_add64(a04,
      Lib_IntVector_Intrinsics_vec128_mul64(r251, a4));
  Lib_IntVector_Intrinsics_vec128
  a15 =
    Lib_IntVector_Intrinsics_vec128_add64(a14,
      Lib_IntVector_Intrinsics_vec128_mul64(r252, a4));
  Lib_IntVector_Intrinsics_vec128
  a25 =
    Lib_IntVector_Intrinsics_vec128_add64(a24,
      Lib_IntVector_Intrinsics_vec128_mul64(r253, a4));
  Lib_IntVector_Intrinsics_vec128
  a35 =
    Lib_IntVector_Intrinsics_vec128_add64(a34,
      Lib_IntVector_Intrinsics_vec128_mul64(r254, a4));
  Lib_IntVector_Intrinsics_vec128
  a45 =
    Lib_IntVector_Intrinsics_vec128_add64(a44,
      Lib_IntVector_Intrinsics_vec128_mul64(r201, a4));
  Lib_IntVector_Intrinsics_vec128 t0 = a05;
  Lib_IntVector_Intrinsics_vec128 t1 = a15;
  Lib_IntVector_Intrinsics_vec128 t2 = a25;
  Lib_IntVector_Intrinsics_vec128 t3 = a35;
  Lib_IntVector_Intrinsics_vec128 t4 = a45;
  Lib_IntVector_Intrinsics_vec128
  mask26 = Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU);
  Lib_IntVector_Intrinsics_vec128
  z0 = Lib_IntVector_Intrinsics_vec128_shift_right64(t0, (u32)26U);
  Lib_IntVector_Intrinsics_vec128
  z1 = Lib_IntVector_Intrinsics_vec128_shift_right64(t3, (u32)26U);
  Lib_IntVector_Intrinsics_vec128 x0 = Lib_IntVector_Intrinsics_vec128_and(t0, mask26);
  Lib_IntVector_Intrinsics_vec128 x3 = Lib_IntVector_Intrinsics_vec128_and(t3, mask26);
  Lib_IntVector_Intrinsics_vec128 x1 = Lib_IntVector_Intrinsics_vec128_add64(t1, z0);
  Lib_IntVector_Intrinsics_vec128 x4 = Lib_IntVector_Intrinsics_vec128_add64(t4, z1);
  Lib_IntVector_Intrinsics_vec128
  z01 = Lib_IntVector_Intrinsics_vec128_shift_right64(x1, (u32)26U);
  Lib_IntVector_Intrinsics_vec128
  z11 = Lib_IntVector_Intrinsics_vec128_shift_right64(x4, (u32)26U);
  Lib_IntVector_Intrinsics_vec128 t = Lib_IntVector_Intrinsics_vec128_shift_left64(z11, (u32)2U);
  Lib_IntVector_Intrinsics_vec128 z12 = Lib_IntVector_Intrinsics_vec128_add64(z11, t);
  Lib_IntVector_Intrinsics_vec128 x11 = Lib_IntVector_Intrinsics_vec128_and(x1, mask26);
  Lib_IntVector_Intrinsics_vec128 x41 = Lib_IntVector_Intrinsics_vec128_and(x4, mask26);
  Lib_IntVector_Intrinsics_vec128 x2 = Lib_IntVector_Intrinsics_vec128_add64(t2, z01);
  Lib_IntVector_Intrinsics_vec128 x01 = Lib_IntVector_Intrinsics_vec128_add64(x0, z12);
  Lib_IntVector_Intrinsics_vec128
  z02 = Lib_IntVector_Intrinsics_vec128_shift_right64(x2, (u32)26U);
  Lib_IntVector_Intrinsics_vec128
  z13 = Lib_IntVector_Intrinsics_vec128_shift_right64(x01, (u32)26U);
  Lib_IntVector_Intrinsics_vec128 x21 = Lib_IntVector_Intrinsics_vec128_and(x2, mask26);
  Lib_IntVector_Intrinsics_vec128 x02 = Lib_IntVector_Intrinsics_vec128_and(x01, mask26);
  Lib_IntVector_Intrinsics_vec128 x31 = Lib_IntVector_Intrinsics_vec128_add64(x3, z02);
  Lib_IntVector_Intrinsics_vec128 x12 = Lib_IntVector_Intrinsics_vec128_add64(x11, z13);
  Lib_IntVector_Intrinsics_vec128
  z03 = Lib_IntVector_Intrinsics_vec128_shift_right64(x31, (u32)26U);
  Lib_IntVector_Intrinsics_vec128 x32 = Lib_IntVector_Intrinsics_vec128_and(x31, mask26);
  Lib_IntVector_Intrinsics_vec128 x42 = Lib_IntVector_Intrinsics_vec128_add64(x41, z03);
  Lib_IntVector_Intrinsics_vec128 o0 = x02;
  Lib_IntVector_Intrinsics_vec128 o10 = x12;
  Lib_IntVector_Intrinsics_vec128 o20 = x21;
  Lib_IntVector_Intrinsics_vec128 o30 = x32;
  Lib_IntVector_Intrinsics_vec128 o40 = x42;
  Lib_IntVector_Intrinsics_vec128
  o01 =
    Lib_IntVector_Intrinsics_vec128_add64(o0,
      Lib_IntVector_Intrinsics_vec128_interleave_high64(o0, o0));
  Lib_IntVector_Intrinsics_vec128
  o11 =
    Lib_IntVector_Intrinsics_vec128_add64(o10,
      Lib_IntVector_Intrinsics_vec128_interleave_high64(o10, o10));
  Lib_IntVector_Intrinsics_vec128
  o21 =
    Lib_IntVector_Intrinsics_vec128_add64(o20,
      Lib_IntVector_Intrinsics_vec128_interleave_high64(o20, o20));
  Lib_IntVector_Intrinsics_vec128
  o31 =
    Lib_IntVector_Intrinsics_vec128_add64(o30,
      Lib_IntVector_Intrinsics_vec128_interleave_high64(o30, o30));
  Lib_IntVector_Intrinsics_vec128
  o41 =
    Lib_IntVector_Intrinsics_vec128_add64(o40,
      Lib_IntVector_Intrinsics_vec128_interleave_high64(o40, o40));
  Lib_IntVector_Intrinsics_vec128
  l = Lib_IntVector_Intrinsics_vec128_add64(o01, Lib_IntVector_Intrinsics_vec128_zero);
  Lib_IntVector_Intrinsics_vec128
  tmp0 =
    Lib_IntVector_Intrinsics_vec128_and(l,
      Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec128
  c0 = Lib_IntVector_Intrinsics_vec128_shift_right64(l, (u32)26U);
  Lib_IntVector_Intrinsics_vec128 l0 = Lib_IntVector_Intrinsics_vec128_add64(o11, c0);
  Lib_IntVector_Intrinsics_vec128
  tmp1 =
    Lib_IntVector_Intrinsics_vec128_and(l0,
      Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec128
  c1 = Lib_IntVector_Intrinsics_vec128_shift_right64(l0, (u32)26U);
  Lib_IntVector_Intrinsics_vec128 l1 = Lib_IntVector_Intrinsics_vec128_add64(o21, c1);
  Lib_IntVector_Intrinsics_vec128
  tmp2 =
    Lib_IntVector_Intrinsics_vec128_and(l1,
      Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec128
  c2 = Lib_IntVector_Intrinsics_vec128_shift_right64(l1, (u32)26U);
  Lib_IntVector_Intrinsics_vec128 l2 = Lib_IntVector_Intrinsics_vec128_add64(o31, c2);
  Lib_IntVector_Intrinsics_vec128
  tmp3 =
    Lib_IntVector_Intrinsics_vec128_and(l2,
      Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec128
  c3 = Lib_IntVector_Intrinsics_vec128_shift_right64(l2, (u32)26U);
  Lib_IntVector_Intrinsics_vec128 l3 = Lib_IntVector_Intrinsics_vec128_add64(o41, c3);
  Lib_IntVector_Intrinsics_vec128
  tmp4 =
    Lib_IntVector_Intrinsics_vec128_and(l3,
      Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec128
  c4 = Lib_IntVector_Intrinsics_vec128_shift_right64(l3, (u32)26U);
  Lib_IntVector_Intrinsics_vec128
  o00 =
    Lib_IntVector_Intrinsics_vec128_add64(tmp0,
      Lib_IntVector_Intrinsics_vec128_smul64(c4, (u64)5U));
  Lib_IntVector_Intrinsics_vec128 o1 = tmp1;
  Lib_IntVector_Intrinsics_vec128 o2 = tmp2;
  Lib_IntVector_Intrinsics_vec128 o3 = tmp3;
  Lib_IntVector_Intrinsics_vec128 o4 = tmp4;
  out[0U] = o00;
  out[1U] = o1;
  out[2U] = o2;
  out[3U] = o3;
  out[4U] = o4;
}

u32 Hacl_Poly1305_128_blocklen = (u32)16U;

void Hacl_Poly1305_128_poly1305_init(Lib_IntVector_Intrinsics_vec128 *ctx, u8 *key)
{
  Lib_IntVector_Intrinsics_vec128 *acc = ctx;
  Lib_IntVector_Intrinsics_vec128 *pre = ctx + (u32)5U;
  u8 *kr = key;
  u64 u0;
  u64 lo;
  u64 u;
  u64 hi;
  u64 mask0;
  u64 mask1;
  u64 lo1;
  u64 hi1;
  Lib_IntVector_Intrinsics_vec128 *r;
  Lib_IntVector_Intrinsics_vec128 *r5;
  Lib_IntVector_Intrinsics_vec128 *rn;
  Lib_IntVector_Intrinsics_vec128 *rn_5;
  Lib_IntVector_Intrinsics_vec128 r_vec0;
  Lib_IntVector_Intrinsics_vec128 r_vec1;
  Lib_IntVector_Intrinsics_vec128 f00;
  Lib_IntVector_Intrinsics_vec128 f15;
  Lib_IntVector_Intrinsics_vec128 f25;
  Lib_IntVector_Intrinsics_vec128 f30;
  Lib_IntVector_Intrinsics_vec128 f40;
  Lib_IntVector_Intrinsics_vec128 f0;
  Lib_IntVector_Intrinsics_vec128 f1;
  Lib_IntVector_Intrinsics_vec128 f2;
  Lib_IntVector_Intrinsics_vec128 f3;
  Lib_IntVector_Intrinsics_vec128 f4;
  Lib_IntVector_Intrinsics_vec128 f200;
  Lib_IntVector_Intrinsics_vec128 f210;
  Lib_IntVector_Intrinsics_vec128 f220;
  Lib_IntVector_Intrinsics_vec128 f230;
  Lib_IntVector_Intrinsics_vec128 f240;
  Lib_IntVector_Intrinsics_vec128 r0;
  Lib_IntVector_Intrinsics_vec128 r1;
  Lib_IntVector_Intrinsics_vec128 r2;
  Lib_IntVector_Intrinsics_vec128 r3;
  Lib_IntVector_Intrinsics_vec128 r4;
  Lib_IntVector_Intrinsics_vec128 r51;
  Lib_IntVector_Intrinsics_vec128 r52;
  Lib_IntVector_Intrinsics_vec128 r53;
  Lib_IntVector_Intrinsics_vec128 r54;
  Lib_IntVector_Intrinsics_vec128 f10;
  Lib_IntVector_Intrinsics_vec128 f11;
  Lib_IntVector_Intrinsics_vec128 f12;
  Lib_IntVector_Intrinsics_vec128 f13;
  Lib_IntVector_Intrinsics_vec128 f14;
  Lib_IntVector_Intrinsics_vec128 a0;
  Lib_IntVector_Intrinsics_vec128 a1;
  Lib_IntVector_Intrinsics_vec128 a2;
  Lib_IntVector_Intrinsics_vec128 a3;
  Lib_IntVector_Intrinsics_vec128 a4;
  Lib_IntVector_Intrinsics_vec128 a01;
  Lib_IntVector_Intrinsics_vec128 a11;
  Lib_IntVector_Intrinsics_vec128 a21;
  Lib_IntVector_Intrinsics_vec128 a31;
  Lib_IntVector_Intrinsics_vec128 a41;
  Lib_IntVector_Intrinsics_vec128 a02;
  Lib_IntVector_Intrinsics_vec128 a12;
  Lib_IntVector_Intrinsics_vec128 a22;
  Lib_IntVector_Intrinsics_vec128 a32;
  Lib_IntVector_Intrinsics_vec128 a42;
  Lib_IntVector_Intrinsics_vec128 a03;
  Lib_IntVector_Intrinsics_vec128 a13;
  Lib_IntVector_Intrinsics_vec128 a23;
  Lib_IntVector_Intrinsics_vec128 a33;
  Lib_IntVector_Intrinsics_vec128 a43;
  Lib_IntVector_Intrinsics_vec128 a04;
  Lib_IntVector_Intrinsics_vec128 a14;
  Lib_IntVector_Intrinsics_vec128 a24;
  Lib_IntVector_Intrinsics_vec128 a34;
  Lib_IntVector_Intrinsics_vec128 a44;
  Lib_IntVector_Intrinsics_vec128 t0;
  Lib_IntVector_Intrinsics_vec128 t1;
  Lib_IntVector_Intrinsics_vec128 t2;
  Lib_IntVector_Intrinsics_vec128 t3;
  Lib_IntVector_Intrinsics_vec128 t4;
  Lib_IntVector_Intrinsics_vec128 mask26;
  Lib_IntVector_Intrinsics_vec128 z0;
  Lib_IntVector_Intrinsics_vec128 z1;
  Lib_IntVector_Intrinsics_vec128 x0;
  Lib_IntVector_Intrinsics_vec128 x3;
  Lib_IntVector_Intrinsics_vec128 x1;
  Lib_IntVector_Intrinsics_vec128 x4;
  Lib_IntVector_Intrinsics_vec128 z01;
  Lib_IntVector_Intrinsics_vec128 z11;
  Lib_IntVector_Intrinsics_vec128 t;
  Lib_IntVector_Intrinsics_vec128 z12;
  Lib_IntVector_Intrinsics_vec128 x11;
  Lib_IntVector_Intrinsics_vec128 x41;
  Lib_IntVector_Intrinsics_vec128 x2;
  Lib_IntVector_Intrinsics_vec128 x01;
  Lib_IntVector_Intrinsics_vec128 z02;
  Lib_IntVector_Intrinsics_vec128 z13;
  Lib_IntVector_Intrinsics_vec128 x21;
  Lib_IntVector_Intrinsics_vec128 x02;
  Lib_IntVector_Intrinsics_vec128 x31;
  Lib_IntVector_Intrinsics_vec128 x12;
  Lib_IntVector_Intrinsics_vec128 z03;
  Lib_IntVector_Intrinsics_vec128 x32;
  Lib_IntVector_Intrinsics_vec128 x42;
  Lib_IntVector_Intrinsics_vec128 o0;
  Lib_IntVector_Intrinsics_vec128 o1;
  Lib_IntVector_Intrinsics_vec128 o2;
  Lib_IntVector_Intrinsics_vec128 o3;
  Lib_IntVector_Intrinsics_vec128 o4;
  Lib_IntVector_Intrinsics_vec128 f20;
  Lib_IntVector_Intrinsics_vec128 f21;
  Lib_IntVector_Intrinsics_vec128 f22;
  Lib_IntVector_Intrinsics_vec128 f23;
  Lib_IntVector_Intrinsics_vec128 f24;
  acc[0U] = Lib_IntVector_Intrinsics_vec128_zero;
  acc[1U] = Lib_IntVector_Intrinsics_vec128_zero;
  acc[2U] = Lib_IntVector_Intrinsics_vec128_zero;
  acc[3U] = Lib_IntVector_Intrinsics_vec128_zero;
  acc[4U] = Lib_IntVector_Intrinsics_vec128_zero;
  u0 = load64_le(kr);
  lo = u0;
  u = load64_le(kr + (u32)8U);
  hi = u;
  mask0 = (u64)0x0ffffffc0fffffffU;
  mask1 = (u64)0x0ffffffc0ffffffcU;
  lo1 = lo & mask0;
  hi1 = hi & mask1;
  r = pre;
  r5 = pre + (u32)5U;
  rn = pre + (u32)10U;
  rn_5 = pre + (u32)15U;
  r_vec0 = Lib_IntVector_Intrinsics_vec128_load64(lo1);
  r_vec1 = Lib_IntVector_Intrinsics_vec128_load64(hi1);
  f00 =
    Lib_IntVector_Intrinsics_vec128_and(r_vec0,
      Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
  f15 =
    Lib_IntVector_Intrinsics_vec128_and(Lib_IntVector_Intrinsics_vec128_shift_right64(r_vec0,
        (u32)26U),
      Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
  f25 =
    Lib_IntVector_Intrinsics_vec128_or(Lib_IntVector_Intrinsics_vec128_shift_right64(r_vec0,
        (u32)52U),
      Lib_IntVector_Intrinsics_vec128_shift_left64(Lib_IntVector_Intrinsics_vec128_and(r_vec1,
          Lib_IntVector_Intrinsics_vec128_load64((u64)0x3fffU)),
        (u32)12U));
  f30 =
    Lib_IntVector_Intrinsics_vec128_and(Lib_IntVector_Intrinsics_vec128_shift_right64(r_vec1,
        (u32)14U),
      Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
  f40 = Lib_IntVector_Intrinsics_vec128_shift_right64(r_vec1, (u32)40U);
  f0 = f00;
  f1 = f15;
  f2 = f25;
  f3 = f30;
  f4 = f40;
  r[0U] = f0;
  r[1U] = f1;
  r[2U] = f2;
  r[3U] = f3;
  r[4U] = f4;
  f200 = r[0U];
  f210 = r[1U];
  f220 = r[2U];
  f230 = r[3U];
  f240 = r[4U];
  r5[0U] = Lib_IntVector_Intrinsics_vec128_smul64(f200, (u64)5U);
  r5[1U] = Lib_IntVector_Intrinsics_vec128_smul64(f210, (u64)5U);
  r5[2U] = Lib_IntVector_Intrinsics_vec128_smul64(f220, (u64)5U);
  r5[3U] = Lib_IntVector_Intrinsics_vec128_smul64(f230, (u64)5U);
  r5[4U] = Lib_IntVector_Intrinsics_vec128_smul64(f240, (u64)5U);
  r0 = r[0U];
  r1 = r[1U];
  r2 = r[2U];
  r3 = r[3U];
  r4 = r[4U];
  r51 = r5[1U];
  r52 = r5[2U];
  r53 = r5[3U];
  r54 = r5[4U];
  f10 = r[0U];
  f11 = r[1U];
  f12 = r[2U];
  f13 = r[3U];
  f14 = r[4U];
  a0 = Lib_IntVector_Intrinsics_vec128_mul64(r0, f10);
  a1 = Lib_IntVector_Intrinsics_vec128_mul64(r1, f10);
  a2 = Lib_IntVector_Intrinsics_vec128_mul64(r2, f10);
  a3 = Lib_IntVector_Intrinsics_vec128_mul64(r3, f10);
  a4 = Lib_IntVector_Intrinsics_vec128_mul64(r4, f10);
  a01 =
    Lib_IntVector_Intrinsics_vec128_add64(a0,
      Lib_IntVector_Intrinsics_vec128_mul64(r54, f11));
  a11 = Lib_IntVector_Intrinsics_vec128_add64(a1, Lib_IntVector_Intrinsics_vec128_mul64(r0, f11));
  a21 = Lib_IntVector_Intrinsics_vec128_add64(a2, Lib_IntVector_Intrinsics_vec128_mul64(r1, f11));
  a31 = Lib_IntVector_Intrinsics_vec128_add64(a3, Lib_IntVector_Intrinsics_vec128_mul64(r2, f11));
  a41 = Lib_IntVector_Intrinsics_vec128_add64(a4, Lib_IntVector_Intrinsics_vec128_mul64(r3, f11));
  a02 =
    Lib_IntVector_Intrinsics_vec128_add64(a01,
      Lib_IntVector_Intrinsics_vec128_mul64(r53, f12));
  a12 =
    Lib_IntVector_Intrinsics_vec128_add64(a11,
      Lib_IntVector_Intrinsics_vec128_mul64(r54, f12));
  a22 =
    Lib_IntVector_Intrinsics_vec128_add64(a21,
      Lib_IntVector_Intrinsics_vec128_mul64(r0, f12));
  a32 =
    Lib_IntVector_Intrinsics_vec128_add64(a31,
      Lib_IntVector_Intrinsics_vec128_mul64(r1, f12));
  a42 =
    Lib_IntVector_Intrinsics_vec128_add64(a41,
      Lib_IntVector_Intrinsics_vec128_mul64(r2, f12));
  a03 =
    Lib_IntVector_Intrinsics_vec128_add64(a02,
      Lib_IntVector_Intrinsics_vec128_mul64(r52, f13));
  a13 =
    Lib_IntVector_Intrinsics_vec128_add64(a12,
      Lib_IntVector_Intrinsics_vec128_mul64(r53, f13));
  a23 =
    Lib_IntVector_Intrinsics_vec128_add64(a22,
      Lib_IntVector_Intrinsics_vec128_mul64(r54, f13));
  a33 =
    Lib_IntVector_Intrinsics_vec128_add64(a32,
      Lib_IntVector_Intrinsics_vec128_mul64(r0, f13));
  a43 =
    Lib_IntVector_Intrinsics_vec128_add64(a42,
      Lib_IntVector_Intrinsics_vec128_mul64(r1, f13));
  a04 =
    Lib_IntVector_Intrinsics_vec128_add64(a03,
      Lib_IntVector_Intrinsics_vec128_mul64(r51, f14));
  a14 =
    Lib_IntVector_Intrinsics_vec128_add64(a13,
      Lib_IntVector_Intrinsics_vec128_mul64(r52, f14));
  a24 =
    Lib_IntVector_Intrinsics_vec128_add64(a23,
      Lib_IntVector_Intrinsics_vec128_mul64(r53, f14));
  a34 =
    Lib_IntVector_Intrinsics_vec128_add64(a33,
      Lib_IntVector_Intrinsics_vec128_mul64(r54, f14));
  a44 =
    Lib_IntVector_Intrinsics_vec128_add64(a43,
      Lib_IntVector_Intrinsics_vec128_mul64(r0, f14));
  t0 = a04;
  t1 = a14;
  t2 = a24;
  t3 = a34;
  t4 = a44;
  mask26 = Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU);
  z0 = Lib_IntVector_Intrinsics_vec128_shift_right64(t0, (u32)26U);
  z1 = Lib_IntVector_Intrinsics_vec128_shift_right64(t3, (u32)26U);
  x0 = Lib_IntVector_Intrinsics_vec128_and(t0, mask26);
  x3 = Lib_IntVector_Intrinsics_vec128_and(t3, mask26);
  x1 = Lib_IntVector_Intrinsics_vec128_add64(t1, z0);
  x4 = Lib_IntVector_Intrinsics_vec128_add64(t4, z1);
  z01 = Lib_IntVector_Intrinsics_vec128_shift_right64(x1, (u32)26U);
  z11 = Lib_IntVector_Intrinsics_vec128_shift_right64(x4, (u32)26U);
  t = Lib_IntVector_Intrinsics_vec128_shift_left64(z11, (u32)2U);
  z12 = Lib_IntVector_Intrinsics_vec128_add64(z11, t);
  x11 = Lib_IntVector_Intrinsics_vec128_and(x1, mask26);
  x41 = Lib_IntVector_Intrinsics_vec128_and(x4, mask26);
  x2 = Lib_IntVector_Intrinsics_vec128_add64(t2, z01);
  x01 = Lib_IntVector_Intrinsics_vec128_add64(x0, z12);
  z02 = Lib_IntVector_Intrinsics_vec128_shift_right64(x2, (u32)26U);
  z13 = Lib_IntVector_Intrinsics_vec128_shift_right64(x01, (u32)26U);
  x21 = Lib_IntVector_Intrinsics_vec128_and(x2, mask26);
  x02 = Lib_IntVector_Intrinsics_vec128_and(x01, mask26);
  x31 = Lib_IntVector_Intrinsics_vec128_add64(x3, z02);
  x12 = Lib_IntVector_Intrinsics_vec128_add64(x11, z13);
  z03 = Lib_IntVector_Intrinsics_vec128_shift_right64(x31, (u32)26U);
  x32 = Lib_IntVector_Intrinsics_vec128_and(x31, mask26);
  x42 = Lib_IntVector_Intrinsics_vec128_add64(x41, z03);
  o0 = x02;
  o1 = x12;
  o2 = x21;
  o3 = x32;
  o4 = x42;
  rn[0U] = o0;
  rn[1U] = o1;
  rn[2U] = o2;
  rn[3U] = o3;
  rn[4U] = o4;
  f20 = rn[0U];
  f21 = rn[1U];
  f22 = rn[2U];
  f23 = rn[3U];
  f24 = rn[4U];
  rn_5[0U] = Lib_IntVector_Intrinsics_vec128_smul64(f20, (u64)5U);
  rn_5[1U] = Lib_IntVector_Intrinsics_vec128_smul64(f21, (u64)5U);
  rn_5[2U] = Lib_IntVector_Intrinsics_vec128_smul64(f22, (u64)5U);
  rn_5[3U] = Lib_IntVector_Intrinsics_vec128_smul64(f23, (u64)5U);
  rn_5[4U] = Lib_IntVector_Intrinsics_vec128_smul64(f24, (u64)5U);
}

void Hacl_Poly1305_128_poly1305_update1(Lib_IntVector_Intrinsics_vec128 *ctx, u8 *text)
{
  Lib_IntVector_Intrinsics_vec128 *pre = ctx + (u32)5U;
  Lib_IntVector_Intrinsics_vec128 *acc = ctx;
  Lib_IntVector_Intrinsics_vec128 e[5U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)5U; ++_i)
      e[_i] = Lib_IntVector_Intrinsics_vec128_zero;
  }
  {
    u64 u0 = load64_le(text);
    u64 lo = u0;
    u64 u = load64_le(text + (u32)8U);
    u64 hi = u;
    Lib_IntVector_Intrinsics_vec128 f0 = Lib_IntVector_Intrinsics_vec128_load64(lo);
    Lib_IntVector_Intrinsics_vec128 f1 = Lib_IntVector_Intrinsics_vec128_load64(hi);
    Lib_IntVector_Intrinsics_vec128
    f010 =
      Lib_IntVector_Intrinsics_vec128_and(f0,
        Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
    Lib_IntVector_Intrinsics_vec128
    f110 =
      Lib_IntVector_Intrinsics_vec128_and(Lib_IntVector_Intrinsics_vec128_shift_right64(f0,
          (u32)26U),
        Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
    Lib_IntVector_Intrinsics_vec128
    f20 =
      Lib_IntVector_Intrinsics_vec128_or(Lib_IntVector_Intrinsics_vec128_shift_right64(f0, (u32)52U),
        Lib_IntVector_Intrinsics_vec128_shift_left64(Lib_IntVector_Intrinsics_vec128_and(f1,
            Lib_IntVector_Intrinsics_vec128_load64((u64)0x3fffU)),
          (u32)12U));
    Lib_IntVector_Intrinsics_vec128
    f30 =
      Lib_IntVector_Intrinsics_vec128_and(Lib_IntVector_Intrinsics_vec128_shift_right64(f1,
          (u32)14U),
        Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
    Lib_IntVector_Intrinsics_vec128
    f40 = Lib_IntVector_Intrinsics_vec128_shift_right64(f1, (u32)40U);
    Lib_IntVector_Intrinsics_vec128 f01 = f010;
    Lib_IntVector_Intrinsics_vec128 f111 = f110;
    Lib_IntVector_Intrinsics_vec128 f2 = f20;
    Lib_IntVector_Intrinsics_vec128 f3 = f30;
    Lib_IntVector_Intrinsics_vec128 f41 = f40;
    u64 b;
    Lib_IntVector_Intrinsics_vec128 mask;
    Lib_IntVector_Intrinsics_vec128 f4;
    Lib_IntVector_Intrinsics_vec128 *r;
    Lib_IntVector_Intrinsics_vec128 *r5;
    Lib_IntVector_Intrinsics_vec128 r0;
    Lib_IntVector_Intrinsics_vec128 r1;
    Lib_IntVector_Intrinsics_vec128 r2;
    Lib_IntVector_Intrinsics_vec128 r3;
    Lib_IntVector_Intrinsics_vec128 r4;
    Lib_IntVector_Intrinsics_vec128 r51;
    Lib_IntVector_Intrinsics_vec128 r52;
    Lib_IntVector_Intrinsics_vec128 r53;
    Lib_IntVector_Intrinsics_vec128 r54;
    Lib_IntVector_Intrinsics_vec128 f10;
    Lib_IntVector_Intrinsics_vec128 f11;
    Lib_IntVector_Intrinsics_vec128 f12;
    Lib_IntVector_Intrinsics_vec128 f13;
    Lib_IntVector_Intrinsics_vec128 f14;
    Lib_IntVector_Intrinsics_vec128 a0;
    Lib_IntVector_Intrinsics_vec128 a1;
    Lib_IntVector_Intrinsics_vec128 a2;
    Lib_IntVector_Intrinsics_vec128 a3;
    Lib_IntVector_Intrinsics_vec128 a4;
    Lib_IntVector_Intrinsics_vec128 a01;
    Lib_IntVector_Intrinsics_vec128 a11;
    Lib_IntVector_Intrinsics_vec128 a21;
    Lib_IntVector_Intrinsics_vec128 a31;
    Lib_IntVector_Intrinsics_vec128 a41;
    Lib_IntVector_Intrinsics_vec128 a02;
    Lib_IntVector_Intrinsics_vec128 a12;
    Lib_IntVector_Intrinsics_vec128 a22;
    Lib_IntVector_Intrinsics_vec128 a32;
    Lib_IntVector_Intrinsics_vec128 a42;
    Lib_IntVector_Intrinsics_vec128 a03;
    Lib_IntVector_Intrinsics_vec128 a13;
    Lib_IntVector_Intrinsics_vec128 a23;
    Lib_IntVector_Intrinsics_vec128 a33;
    Lib_IntVector_Intrinsics_vec128 a43;
    Lib_IntVector_Intrinsics_vec128 a04;
    Lib_IntVector_Intrinsics_vec128 a14;
    Lib_IntVector_Intrinsics_vec128 a24;
    Lib_IntVector_Intrinsics_vec128 a34;
    Lib_IntVector_Intrinsics_vec128 a44;
    Lib_IntVector_Intrinsics_vec128 a05;
    Lib_IntVector_Intrinsics_vec128 a15;
    Lib_IntVector_Intrinsics_vec128 a25;
    Lib_IntVector_Intrinsics_vec128 a35;
    Lib_IntVector_Intrinsics_vec128 a45;
    Lib_IntVector_Intrinsics_vec128 a06;
    Lib_IntVector_Intrinsics_vec128 a16;
    Lib_IntVector_Intrinsics_vec128 a26;
    Lib_IntVector_Intrinsics_vec128 a36;
    Lib_IntVector_Intrinsics_vec128 a46;
    Lib_IntVector_Intrinsics_vec128 t0;
    Lib_IntVector_Intrinsics_vec128 t1;
    Lib_IntVector_Intrinsics_vec128 t2;
    Lib_IntVector_Intrinsics_vec128 t3;
    Lib_IntVector_Intrinsics_vec128 t4;
    Lib_IntVector_Intrinsics_vec128 mask26;
    Lib_IntVector_Intrinsics_vec128 z0;
    Lib_IntVector_Intrinsics_vec128 z1;
    Lib_IntVector_Intrinsics_vec128 x0;
    Lib_IntVector_Intrinsics_vec128 x3;
    Lib_IntVector_Intrinsics_vec128 x1;
    Lib_IntVector_Intrinsics_vec128 x4;
    Lib_IntVector_Intrinsics_vec128 z01;
    Lib_IntVector_Intrinsics_vec128 z11;
    Lib_IntVector_Intrinsics_vec128 t;
    Lib_IntVector_Intrinsics_vec128 z12;
    Lib_IntVector_Intrinsics_vec128 x11;
    Lib_IntVector_Intrinsics_vec128 x41;
    Lib_IntVector_Intrinsics_vec128 x2;
    Lib_IntVector_Intrinsics_vec128 x01;
    Lib_IntVector_Intrinsics_vec128 z02;
    Lib_IntVector_Intrinsics_vec128 z13;
    Lib_IntVector_Intrinsics_vec128 x21;
    Lib_IntVector_Intrinsics_vec128 x02;
    Lib_IntVector_Intrinsics_vec128 x31;
    Lib_IntVector_Intrinsics_vec128 x12;
    Lib_IntVector_Intrinsics_vec128 z03;
    Lib_IntVector_Intrinsics_vec128 x32;
    Lib_IntVector_Intrinsics_vec128 x42;
    Lib_IntVector_Intrinsics_vec128 o0;
    Lib_IntVector_Intrinsics_vec128 o1;
    Lib_IntVector_Intrinsics_vec128 o2;
    Lib_IntVector_Intrinsics_vec128 o3;
    Lib_IntVector_Intrinsics_vec128 o4;
    e[0U] = f01;
    e[1U] = f111;
    e[2U] = f2;
    e[3U] = f3;
    e[4U] = f41;
    b = (u64)0x1000000U;
    mask = Lib_IntVector_Intrinsics_vec128_load64(b);
    f4 = e[4U];
    e[4U] = Lib_IntVector_Intrinsics_vec128_or(f4, mask);
    r = pre;
    r5 = pre + (u32)5U;
    r0 = r[0U];
    r1 = r[1U];
    r2 = r[2U];
    r3 = r[3U];
    r4 = r[4U];
    r51 = r5[1U];
    r52 = r5[2U];
    r53 = r5[3U];
    r54 = r5[4U];
    f10 = e[0U];
    f11 = e[1U];
    f12 = e[2U];
    f13 = e[3U];
    f14 = e[4U];
    a0 = acc[0U];
    a1 = acc[1U];
    a2 = acc[2U];
    a3 = acc[3U];
    a4 = acc[4U];
    a01 = Lib_IntVector_Intrinsics_vec128_add64(a0, f10);
    a11 = Lib_IntVector_Intrinsics_vec128_add64(a1, f11);
    a21 = Lib_IntVector_Intrinsics_vec128_add64(a2, f12);
    a31 = Lib_IntVector_Intrinsics_vec128_add64(a3, f13);
    a41 = Lib_IntVector_Intrinsics_vec128_add64(a4, f14);
    a02 = Lib_IntVector_Intrinsics_vec128_mul64(r0, a01);
    a12 = Lib_IntVector_Intrinsics_vec128_mul64(r1, a01);
    a22 = Lib_IntVector_Intrinsics_vec128_mul64(r2, a01);
    a32 = Lib_IntVector_Intrinsics_vec128_mul64(r3, a01);
    a42 = Lib_IntVector_Intrinsics_vec128_mul64(r4, a01);
    a03 =
      Lib_IntVector_Intrinsics_vec128_add64(a02,
        Lib_IntVector_Intrinsics_vec128_mul64(r54, a11));
    a13 =
      Lib_IntVector_Intrinsics_vec128_add64(a12,
        Lib_IntVector_Intrinsics_vec128_mul64(r0, a11));
    a23 =
      Lib_IntVector_Intrinsics_vec128_add64(a22,
        Lib_IntVector_Intrinsics_vec128_mul64(r1, a11));
    a33 =
      Lib_IntVector_Intrinsics_vec128_add64(a32,
        Lib_IntVector_Intrinsics_vec128_mul64(r2, a11));
    a43 =
      Lib_IntVector_Intrinsics_vec128_add64(a42,
        Lib_IntVector_Intrinsics_vec128_mul64(r3, a11));
    a04 =
      Lib_IntVector_Intrinsics_vec128_add64(a03,
        Lib_IntVector_Intrinsics_vec128_mul64(r53, a21));
    a14 =
      Lib_IntVector_Intrinsics_vec128_add64(a13,
        Lib_IntVector_Intrinsics_vec128_mul64(r54, a21));
    a24 =
      Lib_IntVector_Intrinsics_vec128_add64(a23,
        Lib_IntVector_Intrinsics_vec128_mul64(r0, a21));
    a34 =
      Lib_IntVector_Intrinsics_vec128_add64(a33,
        Lib_IntVector_Intrinsics_vec128_mul64(r1, a21));
    a44 =
      Lib_IntVector_Intrinsics_vec128_add64(a43,
        Lib_IntVector_Intrinsics_vec128_mul64(r2, a21));
    a05 =
      Lib_IntVector_Intrinsics_vec128_add64(a04,
        Lib_IntVector_Intrinsics_vec128_mul64(r52, a31));
    a15 =
      Lib_IntVector_Intrinsics_vec128_add64(a14,
        Lib_IntVector_Intrinsics_vec128_mul64(r53, a31));
    a25 =
      Lib_IntVector_Intrinsics_vec128_add64(a24,
        Lib_IntVector_Intrinsics_vec128_mul64(r54, a31));
    a35 =
      Lib_IntVector_Intrinsics_vec128_add64(a34,
        Lib_IntVector_Intrinsics_vec128_mul64(r0, a31));
    a45 =
      Lib_IntVector_Intrinsics_vec128_add64(a44,
        Lib_IntVector_Intrinsics_vec128_mul64(r1, a31));
    a06 =
      Lib_IntVector_Intrinsics_vec128_add64(a05,
        Lib_IntVector_Intrinsics_vec128_mul64(r51, a41));
    a16 =
      Lib_IntVector_Intrinsics_vec128_add64(a15,
        Lib_IntVector_Intrinsics_vec128_mul64(r52, a41));
    a26 =
      Lib_IntVector_Intrinsics_vec128_add64(a25,
        Lib_IntVector_Intrinsics_vec128_mul64(r53, a41));
    a36 =
      Lib_IntVector_Intrinsics_vec128_add64(a35,
        Lib_IntVector_Intrinsics_vec128_mul64(r54, a41));
    a46 =
      Lib_IntVector_Intrinsics_vec128_add64(a45,
        Lib_IntVector_Intrinsics_vec128_mul64(r0, a41));
    t0 = a06;
    t1 = a16;
    t2 = a26;
    t3 = a36;
    t4 = a46;
    mask26 = Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU);
    z0 = Lib_IntVector_Intrinsics_vec128_shift_right64(t0, (u32)26U);
    z1 = Lib_IntVector_Intrinsics_vec128_shift_right64(t3, (u32)26U);
    x0 = Lib_IntVector_Intrinsics_vec128_and(t0, mask26);
    x3 = Lib_IntVector_Intrinsics_vec128_and(t3, mask26);
    x1 = Lib_IntVector_Intrinsics_vec128_add64(t1, z0);
    x4 = Lib_IntVector_Intrinsics_vec128_add64(t4, z1);
    z01 = Lib_IntVector_Intrinsics_vec128_shift_right64(x1, (u32)26U);
    z11 = Lib_IntVector_Intrinsics_vec128_shift_right64(x4, (u32)26U);
    t = Lib_IntVector_Intrinsics_vec128_shift_left64(z11, (u32)2U);
    z12 = Lib_IntVector_Intrinsics_vec128_add64(z11, t);
    x11 = Lib_IntVector_Intrinsics_vec128_and(x1, mask26);
    x41 = Lib_IntVector_Intrinsics_vec128_and(x4, mask26);
    x2 = Lib_IntVector_Intrinsics_vec128_add64(t2, z01);
    x01 = Lib_IntVector_Intrinsics_vec128_add64(x0, z12);
    z02 = Lib_IntVector_Intrinsics_vec128_shift_right64(x2, (u32)26U);
    z13 = Lib_IntVector_Intrinsics_vec128_shift_right64(x01, (u32)26U);
    x21 = Lib_IntVector_Intrinsics_vec128_and(x2, mask26);
    x02 = Lib_IntVector_Intrinsics_vec128_and(x01, mask26);
    x31 = Lib_IntVector_Intrinsics_vec128_add64(x3, z02);
    x12 = Lib_IntVector_Intrinsics_vec128_add64(x11, z13);
    z03 = Lib_IntVector_Intrinsics_vec128_shift_right64(x31, (u32)26U);
    x32 = Lib_IntVector_Intrinsics_vec128_and(x31, mask26);
    x42 = Lib_IntVector_Intrinsics_vec128_add64(x41, z03);
    o0 = x02;
    o1 = x12;
    o2 = x21;
    o3 = x32;
    o4 = x42;
    acc[0U] = o0;
    acc[1U] = o1;
    acc[2U] = o2;
    acc[3U] = o3;
    acc[4U] = o4;
  }
}

void Hacl_Poly1305_128_poly1305_update(Lib_IntVector_Intrinsics_vec128 *ctx, u32 len, u8 *text)
{
  Lib_IntVector_Intrinsics_vec128 *pre = ctx + (u32)5U;
  Lib_IntVector_Intrinsics_vec128 *acc = ctx;
  u32 sz_block = (u32)32U;
  u32 len0 = len / sz_block * sz_block;
  u8 *t0 = text;
  u32 len1;
  u8 *t10;
  u32 nb0;
  u32 rem;
  if (len0 > (u32)0U)
  {
    u32 bs = (u32)32U;
    u8 *text0 = t0;
    Hacl_Impl_Poly1305_Field32xN_128_load_acc2(acc, text0);
    {
      u32 len10 = len0 - bs;
      u8 *text1 = t0 + bs;
      u32 nb = len10 / bs;
      {
        u32 i;
        for (i = (u32)0U; i < nb; i++)
        {
          u8 *block = text1 + i * bs;
          Lib_IntVector_Intrinsics_vec128 e[5U];
          {
            u32 _i;
            for (_i = 0U; _i < (u32)5U; ++_i)
              e[_i] = Lib_IntVector_Intrinsics_vec128_zero;
          }
          {
            Lib_IntVector_Intrinsics_vec128 b1 = Lib_IntVector_Intrinsics_vec128_load_le(block);
            Lib_IntVector_Intrinsics_vec128
            b2 = Lib_IntVector_Intrinsics_vec128_load_le(block + (u32)16U);
            Lib_IntVector_Intrinsics_vec128
            lo = Lib_IntVector_Intrinsics_vec128_interleave_low64(b1, b2);
            Lib_IntVector_Intrinsics_vec128
            hi = Lib_IntVector_Intrinsics_vec128_interleave_high64(b1, b2);
            Lib_IntVector_Intrinsics_vec128
            f00 =
              Lib_IntVector_Intrinsics_vec128_and(lo,
                Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
            Lib_IntVector_Intrinsics_vec128
            f15 =
              Lib_IntVector_Intrinsics_vec128_and(Lib_IntVector_Intrinsics_vec128_shift_right64(lo,
                  (u32)26U),
                Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
            Lib_IntVector_Intrinsics_vec128
            f25 =
              Lib_IntVector_Intrinsics_vec128_or(Lib_IntVector_Intrinsics_vec128_shift_right64(lo,
                  (u32)52U),
                Lib_IntVector_Intrinsics_vec128_shift_left64(Lib_IntVector_Intrinsics_vec128_and(hi,
                    Lib_IntVector_Intrinsics_vec128_load64((u64)0x3fffU)),
                  (u32)12U));
            Lib_IntVector_Intrinsics_vec128
            f30 =
              Lib_IntVector_Intrinsics_vec128_and(Lib_IntVector_Intrinsics_vec128_shift_right64(hi,
                  (u32)14U),
                Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
            Lib_IntVector_Intrinsics_vec128
            f40 = Lib_IntVector_Intrinsics_vec128_shift_right64(hi, (u32)40U);
            Lib_IntVector_Intrinsics_vec128 f0 = f00;
            Lib_IntVector_Intrinsics_vec128 f1 = f15;
            Lib_IntVector_Intrinsics_vec128 f2 = f25;
            Lib_IntVector_Intrinsics_vec128 f3 = f30;
            Lib_IntVector_Intrinsics_vec128 f41 = f40;
            e[0U] = f0;
            e[1U] = f1;
            e[2U] = f2;
            e[3U] = f3;
            e[4U] = f41;
            {
              u64 b = (u64)0x1000000U;
              Lib_IntVector_Intrinsics_vec128 mask = Lib_IntVector_Intrinsics_vec128_load64(b);
              Lib_IntVector_Intrinsics_vec128 f4 = e[4U];
              e[4U] = Lib_IntVector_Intrinsics_vec128_or(f4, mask);
              {
                Lib_IntVector_Intrinsics_vec128 *rn = pre + (u32)10U;
                Lib_IntVector_Intrinsics_vec128 *rn5 = pre + (u32)15U;
                Lib_IntVector_Intrinsics_vec128 r0 = rn[0U];
                Lib_IntVector_Intrinsics_vec128 r1 = rn[1U];
                Lib_IntVector_Intrinsics_vec128 r2 = rn[2U];
                Lib_IntVector_Intrinsics_vec128 r3 = rn[3U];
                Lib_IntVector_Intrinsics_vec128 r4 = rn[4U];
                Lib_IntVector_Intrinsics_vec128 r51 = rn5[1U];
                Lib_IntVector_Intrinsics_vec128 r52 = rn5[2U];
                Lib_IntVector_Intrinsics_vec128 r53 = rn5[3U];
                Lib_IntVector_Intrinsics_vec128 r54 = rn5[4U];
                Lib_IntVector_Intrinsics_vec128 f10 = acc[0U];
                Lib_IntVector_Intrinsics_vec128 f110 = acc[1U];
                Lib_IntVector_Intrinsics_vec128 f120 = acc[2U];
                Lib_IntVector_Intrinsics_vec128 f130 = acc[3U];
                Lib_IntVector_Intrinsics_vec128 f140 = acc[4U];
                Lib_IntVector_Intrinsics_vec128 a0 = Lib_IntVector_Intrinsics_vec128_mul64(r0, f10);
                Lib_IntVector_Intrinsics_vec128 a1 = Lib_IntVector_Intrinsics_vec128_mul64(r1, f10);
                Lib_IntVector_Intrinsics_vec128 a2 = Lib_IntVector_Intrinsics_vec128_mul64(r2, f10);
                Lib_IntVector_Intrinsics_vec128 a3 = Lib_IntVector_Intrinsics_vec128_mul64(r3, f10);
                Lib_IntVector_Intrinsics_vec128 a4 = Lib_IntVector_Intrinsics_vec128_mul64(r4, f10);
                Lib_IntVector_Intrinsics_vec128
                a01 =
                  Lib_IntVector_Intrinsics_vec128_add64(a0,
                    Lib_IntVector_Intrinsics_vec128_mul64(r54, f110));
                Lib_IntVector_Intrinsics_vec128
                a11 =
                  Lib_IntVector_Intrinsics_vec128_add64(a1,
                    Lib_IntVector_Intrinsics_vec128_mul64(r0, f110));
                Lib_IntVector_Intrinsics_vec128
                a21 =
                  Lib_IntVector_Intrinsics_vec128_add64(a2,
                    Lib_IntVector_Intrinsics_vec128_mul64(r1, f110));
                Lib_IntVector_Intrinsics_vec128
                a31 =
                  Lib_IntVector_Intrinsics_vec128_add64(a3,
                    Lib_IntVector_Intrinsics_vec128_mul64(r2, f110));
                Lib_IntVector_Intrinsics_vec128
                a41 =
                  Lib_IntVector_Intrinsics_vec128_add64(a4,
                    Lib_IntVector_Intrinsics_vec128_mul64(r3, f110));
                Lib_IntVector_Intrinsics_vec128
                a02 =
                  Lib_IntVector_Intrinsics_vec128_add64(a01,
                    Lib_IntVector_Intrinsics_vec128_mul64(r53, f120));
                Lib_IntVector_Intrinsics_vec128
                a12 =
                  Lib_IntVector_Intrinsics_vec128_add64(a11,
                    Lib_IntVector_Intrinsics_vec128_mul64(r54, f120));
                Lib_IntVector_Intrinsics_vec128
                a22 =
                  Lib_IntVector_Intrinsics_vec128_add64(a21,
                    Lib_IntVector_Intrinsics_vec128_mul64(r0, f120));
                Lib_IntVector_Intrinsics_vec128
                a32 =
                  Lib_IntVector_Intrinsics_vec128_add64(a31,
                    Lib_IntVector_Intrinsics_vec128_mul64(r1, f120));
                Lib_IntVector_Intrinsics_vec128
                a42 =
                  Lib_IntVector_Intrinsics_vec128_add64(a41,
                    Lib_IntVector_Intrinsics_vec128_mul64(r2, f120));
                Lib_IntVector_Intrinsics_vec128
                a03 =
                  Lib_IntVector_Intrinsics_vec128_add64(a02,
                    Lib_IntVector_Intrinsics_vec128_mul64(r52, f130));
                Lib_IntVector_Intrinsics_vec128
                a13 =
                  Lib_IntVector_Intrinsics_vec128_add64(a12,
                    Lib_IntVector_Intrinsics_vec128_mul64(r53, f130));
                Lib_IntVector_Intrinsics_vec128
                a23 =
                  Lib_IntVector_Intrinsics_vec128_add64(a22,
                    Lib_IntVector_Intrinsics_vec128_mul64(r54, f130));
                Lib_IntVector_Intrinsics_vec128
                a33 =
                  Lib_IntVector_Intrinsics_vec128_add64(a32,
                    Lib_IntVector_Intrinsics_vec128_mul64(r0, f130));
                Lib_IntVector_Intrinsics_vec128
                a43 =
                  Lib_IntVector_Intrinsics_vec128_add64(a42,
                    Lib_IntVector_Intrinsics_vec128_mul64(r1, f130));
                Lib_IntVector_Intrinsics_vec128
                a04 =
                  Lib_IntVector_Intrinsics_vec128_add64(a03,
                    Lib_IntVector_Intrinsics_vec128_mul64(r51, f140));
                Lib_IntVector_Intrinsics_vec128
                a14 =
                  Lib_IntVector_Intrinsics_vec128_add64(a13,
                    Lib_IntVector_Intrinsics_vec128_mul64(r52, f140));
                Lib_IntVector_Intrinsics_vec128
                a24 =
                  Lib_IntVector_Intrinsics_vec128_add64(a23,
                    Lib_IntVector_Intrinsics_vec128_mul64(r53, f140));
                Lib_IntVector_Intrinsics_vec128
                a34 =
                  Lib_IntVector_Intrinsics_vec128_add64(a33,
                    Lib_IntVector_Intrinsics_vec128_mul64(r54, f140));
                Lib_IntVector_Intrinsics_vec128
                a44 =
                  Lib_IntVector_Intrinsics_vec128_add64(a43,
                    Lib_IntVector_Intrinsics_vec128_mul64(r0, f140));
                Lib_IntVector_Intrinsics_vec128 t01 = a04;
                Lib_IntVector_Intrinsics_vec128 t1 = a14;
                Lib_IntVector_Intrinsics_vec128 t2 = a24;
                Lib_IntVector_Intrinsics_vec128 t3 = a34;
                Lib_IntVector_Intrinsics_vec128 t4 = a44;
                Lib_IntVector_Intrinsics_vec128
                mask26 = Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU);
                Lib_IntVector_Intrinsics_vec128
                z0 = Lib_IntVector_Intrinsics_vec128_shift_right64(t01, (u32)26U);
                Lib_IntVector_Intrinsics_vec128
                z1 = Lib_IntVector_Intrinsics_vec128_shift_right64(t3, (u32)26U);
                Lib_IntVector_Intrinsics_vec128
                x0 = Lib_IntVector_Intrinsics_vec128_and(t01, mask26);
                Lib_IntVector_Intrinsics_vec128
                x3 = Lib_IntVector_Intrinsics_vec128_and(t3, mask26);
                Lib_IntVector_Intrinsics_vec128 x1 = Lib_IntVector_Intrinsics_vec128_add64(t1, z0);
                Lib_IntVector_Intrinsics_vec128 x4 = Lib_IntVector_Intrinsics_vec128_add64(t4, z1);
                Lib_IntVector_Intrinsics_vec128
                z01 = Lib_IntVector_Intrinsics_vec128_shift_right64(x1, (u32)26U);
                Lib_IntVector_Intrinsics_vec128
                z11 = Lib_IntVector_Intrinsics_vec128_shift_right64(x4, (u32)26U);
                Lib_IntVector_Intrinsics_vec128
                t = Lib_IntVector_Intrinsics_vec128_shift_left64(z11, (u32)2U);
                Lib_IntVector_Intrinsics_vec128 z12 = Lib_IntVector_Intrinsics_vec128_add64(z11, t);
                Lib_IntVector_Intrinsics_vec128
                x11 = Lib_IntVector_Intrinsics_vec128_and(x1, mask26);
                Lib_IntVector_Intrinsics_vec128
                x41 = Lib_IntVector_Intrinsics_vec128_and(x4, mask26);
                Lib_IntVector_Intrinsics_vec128 x2 = Lib_IntVector_Intrinsics_vec128_add64(t2, z01);
                Lib_IntVector_Intrinsics_vec128
                x01 = Lib_IntVector_Intrinsics_vec128_add64(x0, z12);
                Lib_IntVector_Intrinsics_vec128
                z02 = Lib_IntVector_Intrinsics_vec128_shift_right64(x2, (u32)26U);
                Lib_IntVector_Intrinsics_vec128
                z13 = Lib_IntVector_Intrinsics_vec128_shift_right64(x01, (u32)26U);
                Lib_IntVector_Intrinsics_vec128
                x21 = Lib_IntVector_Intrinsics_vec128_and(x2, mask26);
                Lib_IntVector_Intrinsics_vec128
                x02 = Lib_IntVector_Intrinsics_vec128_and(x01, mask26);
                Lib_IntVector_Intrinsics_vec128
                x31 = Lib_IntVector_Intrinsics_vec128_add64(x3, z02);
                Lib_IntVector_Intrinsics_vec128
                x12 = Lib_IntVector_Intrinsics_vec128_add64(x11, z13);
                Lib_IntVector_Intrinsics_vec128
                z03 = Lib_IntVector_Intrinsics_vec128_shift_right64(x31, (u32)26U);
                Lib_IntVector_Intrinsics_vec128
                x32 = Lib_IntVector_Intrinsics_vec128_and(x31, mask26);
                Lib_IntVector_Intrinsics_vec128
                x42 = Lib_IntVector_Intrinsics_vec128_add64(x41, z03);
                Lib_IntVector_Intrinsics_vec128 o00 = x02;
                Lib_IntVector_Intrinsics_vec128 o10 = x12;
                Lib_IntVector_Intrinsics_vec128 o20 = x21;
                Lib_IntVector_Intrinsics_vec128 o30 = x32;
                Lib_IntVector_Intrinsics_vec128 o40 = x42;
                acc[0U] = o00;
                acc[1U] = o10;
                acc[2U] = o20;
                acc[3U] = o30;
                acc[4U] = o40;
                {
                  Lib_IntVector_Intrinsics_vec128 f100 = acc[0U];
                  Lib_IntVector_Intrinsics_vec128 f11 = acc[1U];
                  Lib_IntVector_Intrinsics_vec128 f12 = acc[2U];
                  Lib_IntVector_Intrinsics_vec128 f13 = acc[3U];
                  Lib_IntVector_Intrinsics_vec128 f14 = acc[4U];
                  Lib_IntVector_Intrinsics_vec128 f20 = e[0U];
                  Lib_IntVector_Intrinsics_vec128 f21 = e[1U];
                  Lib_IntVector_Intrinsics_vec128 f22 = e[2U];
                  Lib_IntVector_Intrinsics_vec128 f23 = e[3U];
                  Lib_IntVector_Intrinsics_vec128 f24 = e[4U];
                  Lib_IntVector_Intrinsics_vec128
                  o0 = Lib_IntVector_Intrinsics_vec128_add64(f100, f20);
                  Lib_IntVector_Intrinsics_vec128
                  o1 = Lib_IntVector_Intrinsics_vec128_add64(f11, f21);
                  Lib_IntVector_Intrinsics_vec128
                  o2 = Lib_IntVector_Intrinsics_vec128_add64(f12, f22);
                  Lib_IntVector_Intrinsics_vec128
                  o3 = Lib_IntVector_Intrinsics_vec128_add64(f13, f23);
                  Lib_IntVector_Intrinsics_vec128
                  o4 = Lib_IntVector_Intrinsics_vec128_add64(f14, f24);
                  acc[0U] = o0;
                  acc[1U] = o1;
                  acc[2U] = o2;
                  acc[3U] = o3;
                  acc[4U] = o4;
                }
              }
            }
          }
        }
      }
      Hacl_Impl_Poly1305_Field32xN_128_fmul_r2_normalize(acc, pre);
    }
  }
  len1 = len - len0;
  t10 = text + len0;
  nb0 = len1 / (u32)16U;
  rem = len1 % (u32)16U;
  {
    u32 i;
    for (i = (u32)0U; i < nb0; i++)
    {
      u8 *block = t10 + i * (u32)16U;
      Lib_IntVector_Intrinsics_vec128 e[5U];
      {
        u32 _i;
        for (_i = 0U; _i < (u32)5U; ++_i)
          e[_i] = Lib_IntVector_Intrinsics_vec128_zero;
      }
      {
        u64 u0 = load64_le(block);
        u64 lo = u0;
        u64 u = load64_le(block + (u32)8U);
        u64 hi = u;
        Lib_IntVector_Intrinsics_vec128 f0 = Lib_IntVector_Intrinsics_vec128_load64(lo);
        Lib_IntVector_Intrinsics_vec128 f1 = Lib_IntVector_Intrinsics_vec128_load64(hi);
        Lib_IntVector_Intrinsics_vec128
        f010 =
          Lib_IntVector_Intrinsics_vec128_and(f0,
            Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
        Lib_IntVector_Intrinsics_vec128
        f110 =
          Lib_IntVector_Intrinsics_vec128_and(Lib_IntVector_Intrinsics_vec128_shift_right64(f0,
              (u32)26U),
            Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
        Lib_IntVector_Intrinsics_vec128
        f20 =
          Lib_IntVector_Intrinsics_vec128_or(Lib_IntVector_Intrinsics_vec128_shift_right64(f0,
              (u32)52U),
            Lib_IntVector_Intrinsics_vec128_shift_left64(Lib_IntVector_Intrinsics_vec128_and(f1,
                Lib_IntVector_Intrinsics_vec128_load64((u64)0x3fffU)),
              (u32)12U));
        Lib_IntVector_Intrinsics_vec128
        f30 =
          Lib_IntVector_Intrinsics_vec128_and(Lib_IntVector_Intrinsics_vec128_shift_right64(f1,
              (u32)14U),
            Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
        Lib_IntVector_Intrinsics_vec128
        f40 = Lib_IntVector_Intrinsics_vec128_shift_right64(f1, (u32)40U);
        Lib_IntVector_Intrinsics_vec128 f01 = f010;
        Lib_IntVector_Intrinsics_vec128 f111 = f110;
        Lib_IntVector_Intrinsics_vec128 f2 = f20;
        Lib_IntVector_Intrinsics_vec128 f3 = f30;
        Lib_IntVector_Intrinsics_vec128 f41 = f40;
        e[0U] = f01;
        e[1U] = f111;
        e[2U] = f2;
        e[3U] = f3;
        e[4U] = f41;
        {
          u64 b = (u64)0x1000000U;
          Lib_IntVector_Intrinsics_vec128 mask = Lib_IntVector_Intrinsics_vec128_load64(b);
          Lib_IntVector_Intrinsics_vec128 f4 = e[4U];
          e[4U] = Lib_IntVector_Intrinsics_vec128_or(f4, mask);
          {
            Lib_IntVector_Intrinsics_vec128 *r = pre;
            Lib_IntVector_Intrinsics_vec128 *r5 = pre + (u32)5U;
            Lib_IntVector_Intrinsics_vec128 r0 = r[0U];
            Lib_IntVector_Intrinsics_vec128 r1 = r[1U];
            Lib_IntVector_Intrinsics_vec128 r2 = r[2U];
            Lib_IntVector_Intrinsics_vec128 r3 = r[3U];
            Lib_IntVector_Intrinsics_vec128 r4 = r[4U];
            Lib_IntVector_Intrinsics_vec128 r51 = r5[1U];
            Lib_IntVector_Intrinsics_vec128 r52 = r5[2U];
            Lib_IntVector_Intrinsics_vec128 r53 = r5[3U];
            Lib_IntVector_Intrinsics_vec128 r54 = r5[4U];
            Lib_IntVector_Intrinsics_vec128 f10 = e[0U];
            Lib_IntVector_Intrinsics_vec128 f11 = e[1U];
            Lib_IntVector_Intrinsics_vec128 f12 = e[2U];
            Lib_IntVector_Intrinsics_vec128 f13 = e[3U];
            Lib_IntVector_Intrinsics_vec128 f14 = e[4U];
            Lib_IntVector_Intrinsics_vec128 a0 = acc[0U];
            Lib_IntVector_Intrinsics_vec128 a1 = acc[1U];
            Lib_IntVector_Intrinsics_vec128 a2 = acc[2U];
            Lib_IntVector_Intrinsics_vec128 a3 = acc[3U];
            Lib_IntVector_Intrinsics_vec128 a4 = acc[4U];
            Lib_IntVector_Intrinsics_vec128 a01 = Lib_IntVector_Intrinsics_vec128_add64(a0, f10);
            Lib_IntVector_Intrinsics_vec128 a11 = Lib_IntVector_Intrinsics_vec128_add64(a1, f11);
            Lib_IntVector_Intrinsics_vec128 a21 = Lib_IntVector_Intrinsics_vec128_add64(a2, f12);
            Lib_IntVector_Intrinsics_vec128 a31 = Lib_IntVector_Intrinsics_vec128_add64(a3, f13);
            Lib_IntVector_Intrinsics_vec128 a41 = Lib_IntVector_Intrinsics_vec128_add64(a4, f14);
            Lib_IntVector_Intrinsics_vec128 a02 = Lib_IntVector_Intrinsics_vec128_mul64(r0, a01);
            Lib_IntVector_Intrinsics_vec128 a12 = Lib_IntVector_Intrinsics_vec128_mul64(r1, a01);
            Lib_IntVector_Intrinsics_vec128 a22 = Lib_IntVector_Intrinsics_vec128_mul64(r2, a01);
            Lib_IntVector_Intrinsics_vec128 a32 = Lib_IntVector_Intrinsics_vec128_mul64(r3, a01);
            Lib_IntVector_Intrinsics_vec128 a42 = Lib_IntVector_Intrinsics_vec128_mul64(r4, a01);
            Lib_IntVector_Intrinsics_vec128
            a03 =
              Lib_IntVector_Intrinsics_vec128_add64(a02,
                Lib_IntVector_Intrinsics_vec128_mul64(r54, a11));
            Lib_IntVector_Intrinsics_vec128
            a13 =
              Lib_IntVector_Intrinsics_vec128_add64(a12,
                Lib_IntVector_Intrinsics_vec128_mul64(r0, a11));
            Lib_IntVector_Intrinsics_vec128
            a23 =
              Lib_IntVector_Intrinsics_vec128_add64(a22,
                Lib_IntVector_Intrinsics_vec128_mul64(r1, a11));
            Lib_IntVector_Intrinsics_vec128
            a33 =
              Lib_IntVector_Intrinsics_vec128_add64(a32,
                Lib_IntVector_Intrinsics_vec128_mul64(r2, a11));
            Lib_IntVector_Intrinsics_vec128
            a43 =
              Lib_IntVector_Intrinsics_vec128_add64(a42,
                Lib_IntVector_Intrinsics_vec128_mul64(r3, a11));
            Lib_IntVector_Intrinsics_vec128
            a04 =
              Lib_IntVector_Intrinsics_vec128_add64(a03,
                Lib_IntVector_Intrinsics_vec128_mul64(r53, a21));
            Lib_IntVector_Intrinsics_vec128
            a14 =
              Lib_IntVector_Intrinsics_vec128_add64(a13,
                Lib_IntVector_Intrinsics_vec128_mul64(r54, a21));
            Lib_IntVector_Intrinsics_vec128
            a24 =
              Lib_IntVector_Intrinsics_vec128_add64(a23,
                Lib_IntVector_Intrinsics_vec128_mul64(r0, a21));
            Lib_IntVector_Intrinsics_vec128
            a34 =
              Lib_IntVector_Intrinsics_vec128_add64(a33,
                Lib_IntVector_Intrinsics_vec128_mul64(r1, a21));
            Lib_IntVector_Intrinsics_vec128
            a44 =
              Lib_IntVector_Intrinsics_vec128_add64(a43,
                Lib_IntVector_Intrinsics_vec128_mul64(r2, a21));
            Lib_IntVector_Intrinsics_vec128
            a05 =
              Lib_IntVector_Intrinsics_vec128_add64(a04,
                Lib_IntVector_Intrinsics_vec128_mul64(r52, a31));
            Lib_IntVector_Intrinsics_vec128
            a15 =
              Lib_IntVector_Intrinsics_vec128_add64(a14,
                Lib_IntVector_Intrinsics_vec128_mul64(r53, a31));
            Lib_IntVector_Intrinsics_vec128
            a25 =
              Lib_IntVector_Intrinsics_vec128_add64(a24,
                Lib_IntVector_Intrinsics_vec128_mul64(r54, a31));
            Lib_IntVector_Intrinsics_vec128
            a35 =
              Lib_IntVector_Intrinsics_vec128_add64(a34,
                Lib_IntVector_Intrinsics_vec128_mul64(r0, a31));
            Lib_IntVector_Intrinsics_vec128
            a45 =
              Lib_IntVector_Intrinsics_vec128_add64(a44,
                Lib_IntVector_Intrinsics_vec128_mul64(r1, a31));
            Lib_IntVector_Intrinsics_vec128
            a06 =
              Lib_IntVector_Intrinsics_vec128_add64(a05,
                Lib_IntVector_Intrinsics_vec128_mul64(r51, a41));
            Lib_IntVector_Intrinsics_vec128
            a16 =
              Lib_IntVector_Intrinsics_vec128_add64(a15,
                Lib_IntVector_Intrinsics_vec128_mul64(r52, a41));
            Lib_IntVector_Intrinsics_vec128
            a26 =
              Lib_IntVector_Intrinsics_vec128_add64(a25,
                Lib_IntVector_Intrinsics_vec128_mul64(r53, a41));
            Lib_IntVector_Intrinsics_vec128
            a36 =
              Lib_IntVector_Intrinsics_vec128_add64(a35,
                Lib_IntVector_Intrinsics_vec128_mul64(r54, a41));
            Lib_IntVector_Intrinsics_vec128
            a46 =
              Lib_IntVector_Intrinsics_vec128_add64(a45,
                Lib_IntVector_Intrinsics_vec128_mul64(r0, a41));
            Lib_IntVector_Intrinsics_vec128 t01 = a06;
            Lib_IntVector_Intrinsics_vec128 t11 = a16;
            Lib_IntVector_Intrinsics_vec128 t2 = a26;
            Lib_IntVector_Intrinsics_vec128 t3 = a36;
            Lib_IntVector_Intrinsics_vec128 t4 = a46;
            Lib_IntVector_Intrinsics_vec128
            mask26 = Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU);
            Lib_IntVector_Intrinsics_vec128
            z0 = Lib_IntVector_Intrinsics_vec128_shift_right64(t01, (u32)26U);
            Lib_IntVector_Intrinsics_vec128
            z1 = Lib_IntVector_Intrinsics_vec128_shift_right64(t3, (u32)26U);
            Lib_IntVector_Intrinsics_vec128 x0 = Lib_IntVector_Intrinsics_vec128_and(t01, mask26);
            Lib_IntVector_Intrinsics_vec128 x3 = Lib_IntVector_Intrinsics_vec128_and(t3, mask26);
            Lib_IntVector_Intrinsics_vec128 x1 = Lib_IntVector_Intrinsics_vec128_add64(t11, z0);
            Lib_IntVector_Intrinsics_vec128 x4 = Lib_IntVector_Intrinsics_vec128_add64(t4, z1);
            Lib_IntVector_Intrinsics_vec128
            z01 = Lib_IntVector_Intrinsics_vec128_shift_right64(x1, (u32)26U);
            Lib_IntVector_Intrinsics_vec128
            z11 = Lib_IntVector_Intrinsics_vec128_shift_right64(x4, (u32)26U);
            Lib_IntVector_Intrinsics_vec128
            t = Lib_IntVector_Intrinsics_vec128_shift_left64(z11, (u32)2U);
            Lib_IntVector_Intrinsics_vec128 z12 = Lib_IntVector_Intrinsics_vec128_add64(z11, t);
            Lib_IntVector_Intrinsics_vec128 x11 = Lib_IntVector_Intrinsics_vec128_and(x1, mask26);
            Lib_IntVector_Intrinsics_vec128 x41 = Lib_IntVector_Intrinsics_vec128_and(x4, mask26);
            Lib_IntVector_Intrinsics_vec128 x2 = Lib_IntVector_Intrinsics_vec128_add64(t2, z01);
            Lib_IntVector_Intrinsics_vec128 x01 = Lib_IntVector_Intrinsics_vec128_add64(x0, z12);
            Lib_IntVector_Intrinsics_vec128
            z02 = Lib_IntVector_Intrinsics_vec128_shift_right64(x2, (u32)26U);
            Lib_IntVector_Intrinsics_vec128
            z13 = Lib_IntVector_Intrinsics_vec128_shift_right64(x01, (u32)26U);
            Lib_IntVector_Intrinsics_vec128 x21 = Lib_IntVector_Intrinsics_vec128_and(x2, mask26);
            Lib_IntVector_Intrinsics_vec128 x02 = Lib_IntVector_Intrinsics_vec128_and(x01, mask26);
            Lib_IntVector_Intrinsics_vec128 x31 = Lib_IntVector_Intrinsics_vec128_add64(x3, z02);
            Lib_IntVector_Intrinsics_vec128 x12 = Lib_IntVector_Intrinsics_vec128_add64(x11, z13);
            Lib_IntVector_Intrinsics_vec128
            z03 = Lib_IntVector_Intrinsics_vec128_shift_right64(x31, (u32)26U);
            Lib_IntVector_Intrinsics_vec128 x32 = Lib_IntVector_Intrinsics_vec128_and(x31, mask26);
            Lib_IntVector_Intrinsics_vec128 x42 = Lib_IntVector_Intrinsics_vec128_add64(x41, z03);
            Lib_IntVector_Intrinsics_vec128 o0 = x02;
            Lib_IntVector_Intrinsics_vec128 o1 = x12;
            Lib_IntVector_Intrinsics_vec128 o2 = x21;
            Lib_IntVector_Intrinsics_vec128 o3 = x32;
            Lib_IntVector_Intrinsics_vec128 o4 = x42;
            acc[0U] = o0;
            acc[1U] = o1;
            acc[2U] = o2;
            acc[3U] = o3;
            acc[4U] = o4;
          }
        }
      }
    }
  }
  if (rem > (u32)0U)
  {
    u8 *last = t10 + nb0 * (u32)16U;
    Lib_IntVector_Intrinsics_vec128 e[5U];
    {
      u32 _i;
      for (_i = 0U; _i < (u32)5U; ++_i)
        e[_i] = Lib_IntVector_Intrinsics_vec128_zero;
    }
    {
      u8 tmp[16U] = { 0U };
      u64 u0;
      u64 lo;
      u64 u;
      u64 hi;
      Lib_IntVector_Intrinsics_vec128 f0;
      Lib_IntVector_Intrinsics_vec128 f1;
      Lib_IntVector_Intrinsics_vec128 f010;
      Lib_IntVector_Intrinsics_vec128 f110;
      Lib_IntVector_Intrinsics_vec128 f20;
      Lib_IntVector_Intrinsics_vec128 f30;
      Lib_IntVector_Intrinsics_vec128 f40;
      Lib_IntVector_Intrinsics_vec128 f01;
      Lib_IntVector_Intrinsics_vec128 f111;
      Lib_IntVector_Intrinsics_vec128 f2;
      Lib_IntVector_Intrinsics_vec128 f3;
      Lib_IntVector_Intrinsics_vec128 f4;
      u64 b;
      Lib_IntVector_Intrinsics_vec128 mask;
      Lib_IntVector_Intrinsics_vec128 fi;
      Lib_IntVector_Intrinsics_vec128 *r;
      Lib_IntVector_Intrinsics_vec128 *r5;
      Lib_IntVector_Intrinsics_vec128 r0;
      Lib_IntVector_Intrinsics_vec128 r1;
      Lib_IntVector_Intrinsics_vec128 r2;
      Lib_IntVector_Intrinsics_vec128 r3;
      Lib_IntVector_Intrinsics_vec128 r4;
      Lib_IntVector_Intrinsics_vec128 r51;
      Lib_IntVector_Intrinsics_vec128 r52;
      Lib_IntVector_Intrinsics_vec128 r53;
      Lib_IntVector_Intrinsics_vec128 r54;
      Lib_IntVector_Intrinsics_vec128 f10;
      Lib_IntVector_Intrinsics_vec128 f11;
      Lib_IntVector_Intrinsics_vec128 f12;
      Lib_IntVector_Intrinsics_vec128 f13;
      Lib_IntVector_Intrinsics_vec128 f14;
      Lib_IntVector_Intrinsics_vec128 a0;
      Lib_IntVector_Intrinsics_vec128 a1;
      Lib_IntVector_Intrinsics_vec128 a2;
      Lib_IntVector_Intrinsics_vec128 a3;
      Lib_IntVector_Intrinsics_vec128 a4;
      Lib_IntVector_Intrinsics_vec128 a01;
      Lib_IntVector_Intrinsics_vec128 a11;
      Lib_IntVector_Intrinsics_vec128 a21;
      Lib_IntVector_Intrinsics_vec128 a31;
      Lib_IntVector_Intrinsics_vec128 a41;
      Lib_IntVector_Intrinsics_vec128 a02;
      Lib_IntVector_Intrinsics_vec128 a12;
      Lib_IntVector_Intrinsics_vec128 a22;
      Lib_IntVector_Intrinsics_vec128 a32;
      Lib_IntVector_Intrinsics_vec128 a42;
      Lib_IntVector_Intrinsics_vec128 a03;
      Lib_IntVector_Intrinsics_vec128 a13;
      Lib_IntVector_Intrinsics_vec128 a23;
      Lib_IntVector_Intrinsics_vec128 a33;
      Lib_IntVector_Intrinsics_vec128 a43;
      Lib_IntVector_Intrinsics_vec128 a04;
      Lib_IntVector_Intrinsics_vec128 a14;
      Lib_IntVector_Intrinsics_vec128 a24;
      Lib_IntVector_Intrinsics_vec128 a34;
      Lib_IntVector_Intrinsics_vec128 a44;
      Lib_IntVector_Intrinsics_vec128 a05;
      Lib_IntVector_Intrinsics_vec128 a15;
      Lib_IntVector_Intrinsics_vec128 a25;
      Lib_IntVector_Intrinsics_vec128 a35;
      Lib_IntVector_Intrinsics_vec128 a45;
      Lib_IntVector_Intrinsics_vec128 a06;
      Lib_IntVector_Intrinsics_vec128 a16;
      Lib_IntVector_Intrinsics_vec128 a26;
      Lib_IntVector_Intrinsics_vec128 a36;
      Lib_IntVector_Intrinsics_vec128 a46;
      Lib_IntVector_Intrinsics_vec128 t01;
      Lib_IntVector_Intrinsics_vec128 t11;
      Lib_IntVector_Intrinsics_vec128 t2;
      Lib_IntVector_Intrinsics_vec128 t3;
      Lib_IntVector_Intrinsics_vec128 t4;
      Lib_IntVector_Intrinsics_vec128 mask26;
      Lib_IntVector_Intrinsics_vec128 z0;
      Lib_IntVector_Intrinsics_vec128 z1;
      Lib_IntVector_Intrinsics_vec128 x0;
      Lib_IntVector_Intrinsics_vec128 x3;
      Lib_IntVector_Intrinsics_vec128 x1;
      Lib_IntVector_Intrinsics_vec128 x4;
      Lib_IntVector_Intrinsics_vec128 z01;
      Lib_IntVector_Intrinsics_vec128 z11;
      Lib_IntVector_Intrinsics_vec128 t;
      Lib_IntVector_Intrinsics_vec128 z12;
      Lib_IntVector_Intrinsics_vec128 x11;
      Lib_IntVector_Intrinsics_vec128 x41;
      Lib_IntVector_Intrinsics_vec128 x2;
      Lib_IntVector_Intrinsics_vec128 x01;
      Lib_IntVector_Intrinsics_vec128 z02;
      Lib_IntVector_Intrinsics_vec128 z13;
      Lib_IntVector_Intrinsics_vec128 x21;
      Lib_IntVector_Intrinsics_vec128 x02;
      Lib_IntVector_Intrinsics_vec128 x31;
      Lib_IntVector_Intrinsics_vec128 x12;
      Lib_IntVector_Intrinsics_vec128 z03;
      Lib_IntVector_Intrinsics_vec128 x32;
      Lib_IntVector_Intrinsics_vec128 x42;
      Lib_IntVector_Intrinsics_vec128 o0;
      Lib_IntVector_Intrinsics_vec128 o1;
      Lib_IntVector_Intrinsics_vec128 o2;
      Lib_IntVector_Intrinsics_vec128 o3;
      Lib_IntVector_Intrinsics_vec128 o4;
      memcpy(tmp, last, rem * sizeof (last[0U]));
      u0 = load64_le(tmp);
      lo = u0;
      u = load64_le(tmp + (u32)8U);
      hi = u;
      f0 = Lib_IntVector_Intrinsics_vec128_load64(lo);
      f1 = Lib_IntVector_Intrinsics_vec128_load64(hi);
      f010 =
        Lib_IntVector_Intrinsics_vec128_and(f0,
          Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
      f110 =
        Lib_IntVector_Intrinsics_vec128_and(Lib_IntVector_Intrinsics_vec128_shift_right64(f0,
            (u32)26U),
          Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
      f20 =
        Lib_IntVector_Intrinsics_vec128_or(Lib_IntVector_Intrinsics_vec128_shift_right64(f0,
            (u32)52U),
          Lib_IntVector_Intrinsics_vec128_shift_left64(Lib_IntVector_Intrinsics_vec128_and(f1,
              Lib_IntVector_Intrinsics_vec128_load64((u64)0x3fffU)),
            (u32)12U));
      f30 =
        Lib_IntVector_Intrinsics_vec128_and(Lib_IntVector_Intrinsics_vec128_shift_right64(f1,
            (u32)14U),
          Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
      f40 = Lib_IntVector_Intrinsics_vec128_shift_right64(f1, (u32)40U);
      f01 = f010;
      f111 = f110;
      f2 = f20;
      f3 = f30;
      f4 = f40;
      e[0U] = f01;
      e[1U] = f111;
      e[2U] = f2;
      e[3U] = f3;
      e[4U] = f4;
      b = (u64)1U << rem * (u32)8U % (u32)26U;
      mask = Lib_IntVector_Intrinsics_vec128_load64(b);
      fi = e[rem * (u32)8U / (u32)26U];
      e[rem * (u32)8U / (u32)26U] = Lib_IntVector_Intrinsics_vec128_or(fi, mask);
      r = pre;
      r5 = pre + (u32)5U;
      r0 = r[0U];
      r1 = r[1U];
      r2 = r[2U];
      r3 = r[3U];
      r4 = r[4U];
      r51 = r5[1U];
      r52 = r5[2U];
      r53 = r5[3U];
      r54 = r5[4U];
      f10 = e[0U];
      f11 = e[1U];
      f12 = e[2U];
      f13 = e[3U];
      f14 = e[4U];
      a0 = acc[0U];
      a1 = acc[1U];
      a2 = acc[2U];
      a3 = acc[3U];
      a4 = acc[4U];
      a01 = Lib_IntVector_Intrinsics_vec128_add64(a0, f10);
      a11 = Lib_IntVector_Intrinsics_vec128_add64(a1, f11);
      a21 = Lib_IntVector_Intrinsics_vec128_add64(a2, f12);
      a31 = Lib_IntVector_Intrinsics_vec128_add64(a3, f13);
      a41 = Lib_IntVector_Intrinsics_vec128_add64(a4, f14);
      a02 = Lib_IntVector_Intrinsics_vec128_mul64(r0, a01);
      a12 = Lib_IntVector_Intrinsics_vec128_mul64(r1, a01);
      a22 = Lib_IntVector_Intrinsics_vec128_mul64(r2, a01);
      a32 = Lib_IntVector_Intrinsics_vec128_mul64(r3, a01);
      a42 = Lib_IntVector_Intrinsics_vec128_mul64(r4, a01);
      a03 =
        Lib_IntVector_Intrinsics_vec128_add64(a02,
          Lib_IntVector_Intrinsics_vec128_mul64(r54, a11));
      a13 =
        Lib_IntVector_Intrinsics_vec128_add64(a12,
          Lib_IntVector_Intrinsics_vec128_mul64(r0, a11));
      a23 =
        Lib_IntVector_Intrinsics_vec128_add64(a22,
          Lib_IntVector_Intrinsics_vec128_mul64(r1, a11));
      a33 =
        Lib_IntVector_Intrinsics_vec128_add64(a32,
          Lib_IntVector_Intrinsics_vec128_mul64(r2, a11));
      a43 =
        Lib_IntVector_Intrinsics_vec128_add64(a42,
          Lib_IntVector_Intrinsics_vec128_mul64(r3, a11));
      a04 =
        Lib_IntVector_Intrinsics_vec128_add64(a03,
          Lib_IntVector_Intrinsics_vec128_mul64(r53, a21));
      a14 =
        Lib_IntVector_Intrinsics_vec128_add64(a13,
          Lib_IntVector_Intrinsics_vec128_mul64(r54, a21));
      a24 =
        Lib_IntVector_Intrinsics_vec128_add64(a23,
          Lib_IntVector_Intrinsics_vec128_mul64(r0, a21));
      a34 =
        Lib_IntVector_Intrinsics_vec128_add64(a33,
          Lib_IntVector_Intrinsics_vec128_mul64(r1, a21));
      a44 =
        Lib_IntVector_Intrinsics_vec128_add64(a43,
          Lib_IntVector_Intrinsics_vec128_mul64(r2, a21));
      a05 =
        Lib_IntVector_Intrinsics_vec128_add64(a04,
          Lib_IntVector_Intrinsics_vec128_mul64(r52, a31));
      a15 =
        Lib_IntVector_Intrinsics_vec128_add64(a14,
          Lib_IntVector_Intrinsics_vec128_mul64(r53, a31));
      a25 =
        Lib_IntVector_Intrinsics_vec128_add64(a24,
          Lib_IntVector_Intrinsics_vec128_mul64(r54, a31));
      a35 =
        Lib_IntVector_Intrinsics_vec128_add64(a34,
          Lib_IntVector_Intrinsics_vec128_mul64(r0, a31));
      a45 =
        Lib_IntVector_Intrinsics_vec128_add64(a44,
          Lib_IntVector_Intrinsics_vec128_mul64(r1, a31));
      a06 =
        Lib_IntVector_Intrinsics_vec128_add64(a05,
          Lib_IntVector_Intrinsics_vec128_mul64(r51, a41));
      a16 =
        Lib_IntVector_Intrinsics_vec128_add64(a15,
          Lib_IntVector_Intrinsics_vec128_mul64(r52, a41));
      a26 =
        Lib_IntVector_Intrinsics_vec128_add64(a25,
          Lib_IntVector_Intrinsics_vec128_mul64(r53, a41));
      a36 =
        Lib_IntVector_Intrinsics_vec128_add64(a35,
          Lib_IntVector_Intrinsics_vec128_mul64(r54, a41));
      a46 =
        Lib_IntVector_Intrinsics_vec128_add64(a45,
          Lib_IntVector_Intrinsics_vec128_mul64(r0, a41));
      t01 = a06;
      t11 = a16;
      t2 = a26;
      t3 = a36;
      t4 = a46;
      mask26 = Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU);
      z0 = Lib_IntVector_Intrinsics_vec128_shift_right64(t01, (u32)26U);
      z1 = Lib_IntVector_Intrinsics_vec128_shift_right64(t3, (u32)26U);
      x0 = Lib_IntVector_Intrinsics_vec128_and(t01, mask26);
      x3 = Lib_IntVector_Intrinsics_vec128_and(t3, mask26);
      x1 = Lib_IntVector_Intrinsics_vec128_add64(t11, z0);
      x4 = Lib_IntVector_Intrinsics_vec128_add64(t4, z1);
      z01 = Lib_IntVector_Intrinsics_vec128_shift_right64(x1, (u32)26U);
      z11 = Lib_IntVector_Intrinsics_vec128_shift_right64(x4, (u32)26U);
      t = Lib_IntVector_Intrinsics_vec128_shift_left64(z11, (u32)2U);
      z12 = Lib_IntVector_Intrinsics_vec128_add64(z11, t);
      x11 = Lib_IntVector_Intrinsics_vec128_and(x1, mask26);
      x41 = Lib_IntVector_Intrinsics_vec128_and(x4, mask26);
      x2 = Lib_IntVector_Intrinsics_vec128_add64(t2, z01);
      x01 = Lib_IntVector_Intrinsics_vec128_add64(x0, z12);
      z02 = Lib_IntVector_Intrinsics_vec128_shift_right64(x2, (u32)26U);
      z13 = Lib_IntVector_Intrinsics_vec128_shift_right64(x01, (u32)26U);
      x21 = Lib_IntVector_Intrinsics_vec128_and(x2, mask26);
      x02 = Lib_IntVector_Intrinsics_vec128_and(x01, mask26);
      x31 = Lib_IntVector_Intrinsics_vec128_add64(x3, z02);
      x12 = Lib_IntVector_Intrinsics_vec128_add64(x11, z13);
      z03 = Lib_IntVector_Intrinsics_vec128_shift_right64(x31, (u32)26U);
      x32 = Lib_IntVector_Intrinsics_vec128_and(x31, mask26);
      x42 = Lib_IntVector_Intrinsics_vec128_add64(x41, z03);
      o0 = x02;
      o1 = x12;
      o2 = x21;
      o3 = x32;
      o4 = x42;
      acc[0U] = o0;
      acc[1U] = o1;
      acc[2U] = o2;
      acc[3U] = o3;
      acc[4U] = o4;
      return;
    }
  }
}

void Hacl_Poly1305_128_poly1305_finish(u8 *tag, u8 *key, Lib_IntVector_Intrinsics_vec128 *ctx)
{
  Lib_IntVector_Intrinsics_vec128 *acc = ctx;
  u8 *ks = key + (u32)16U;
  Lib_IntVector_Intrinsics_vec128 f00 = acc[0U];
  Lib_IntVector_Intrinsics_vec128 f13 = acc[1U];
  Lib_IntVector_Intrinsics_vec128 f23 = acc[2U];
  Lib_IntVector_Intrinsics_vec128 f33 = acc[3U];
  Lib_IntVector_Intrinsics_vec128 f40 = acc[4U];
  Lib_IntVector_Intrinsics_vec128
  l0 = Lib_IntVector_Intrinsics_vec128_add64(f00, Lib_IntVector_Intrinsics_vec128_zero);
  Lib_IntVector_Intrinsics_vec128
  tmp00 =
    Lib_IntVector_Intrinsics_vec128_and(l0,
      Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec128
  c00 = Lib_IntVector_Intrinsics_vec128_shift_right64(l0, (u32)26U);
  Lib_IntVector_Intrinsics_vec128 l1 = Lib_IntVector_Intrinsics_vec128_add64(f13, c00);
  Lib_IntVector_Intrinsics_vec128
  tmp10 =
    Lib_IntVector_Intrinsics_vec128_and(l1,
      Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec128
  c10 = Lib_IntVector_Intrinsics_vec128_shift_right64(l1, (u32)26U);
  Lib_IntVector_Intrinsics_vec128 l2 = Lib_IntVector_Intrinsics_vec128_add64(f23, c10);
  Lib_IntVector_Intrinsics_vec128
  tmp20 =
    Lib_IntVector_Intrinsics_vec128_and(l2,
      Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec128
  c20 = Lib_IntVector_Intrinsics_vec128_shift_right64(l2, (u32)26U);
  Lib_IntVector_Intrinsics_vec128 l3 = Lib_IntVector_Intrinsics_vec128_add64(f33, c20);
  Lib_IntVector_Intrinsics_vec128
  tmp30 =
    Lib_IntVector_Intrinsics_vec128_and(l3,
      Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec128
  c30 = Lib_IntVector_Intrinsics_vec128_shift_right64(l3, (u32)26U);
  Lib_IntVector_Intrinsics_vec128 l4 = Lib_IntVector_Intrinsics_vec128_add64(f40, c30);
  Lib_IntVector_Intrinsics_vec128
  tmp40 =
    Lib_IntVector_Intrinsics_vec128_and(l4,
      Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec128
  c40 = Lib_IntVector_Intrinsics_vec128_shift_right64(l4, (u32)26U);
  Lib_IntVector_Intrinsics_vec128
  f010 =
    Lib_IntVector_Intrinsics_vec128_add64(tmp00,
      Lib_IntVector_Intrinsics_vec128_smul64(c40, (u64)5U));
  Lib_IntVector_Intrinsics_vec128 f110 = tmp10;
  Lib_IntVector_Intrinsics_vec128 f210 = tmp20;
  Lib_IntVector_Intrinsics_vec128 f310 = tmp30;
  Lib_IntVector_Intrinsics_vec128 f410 = tmp40;
  Lib_IntVector_Intrinsics_vec128
  l = Lib_IntVector_Intrinsics_vec128_add64(f010, Lib_IntVector_Intrinsics_vec128_zero);
  Lib_IntVector_Intrinsics_vec128
  tmp0 =
    Lib_IntVector_Intrinsics_vec128_and(l,
      Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec128
  c0 = Lib_IntVector_Intrinsics_vec128_shift_right64(l, (u32)26U);
  Lib_IntVector_Intrinsics_vec128 l5 = Lib_IntVector_Intrinsics_vec128_add64(f110, c0);
  Lib_IntVector_Intrinsics_vec128
  tmp1 =
    Lib_IntVector_Intrinsics_vec128_and(l5,
      Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec128
  c1 = Lib_IntVector_Intrinsics_vec128_shift_right64(l5, (u32)26U);
  Lib_IntVector_Intrinsics_vec128 l6 = Lib_IntVector_Intrinsics_vec128_add64(f210, c1);
  Lib_IntVector_Intrinsics_vec128
  tmp2 =
    Lib_IntVector_Intrinsics_vec128_and(l6,
      Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec128
  c2 = Lib_IntVector_Intrinsics_vec128_shift_right64(l6, (u32)26U);
  Lib_IntVector_Intrinsics_vec128 l7 = Lib_IntVector_Intrinsics_vec128_add64(f310, c2);
  Lib_IntVector_Intrinsics_vec128
  tmp3 =
    Lib_IntVector_Intrinsics_vec128_and(l7,
      Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec128
  c3 = Lib_IntVector_Intrinsics_vec128_shift_right64(l7, (u32)26U);
  Lib_IntVector_Intrinsics_vec128 l8 = Lib_IntVector_Intrinsics_vec128_add64(f410, c3);
  Lib_IntVector_Intrinsics_vec128
  tmp4 =
    Lib_IntVector_Intrinsics_vec128_and(l8,
      Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec128
  c4 = Lib_IntVector_Intrinsics_vec128_shift_right64(l8, (u32)26U);
  Lib_IntVector_Intrinsics_vec128
  f02 =
    Lib_IntVector_Intrinsics_vec128_add64(tmp0,
      Lib_IntVector_Intrinsics_vec128_smul64(c4, (u64)5U));
  Lib_IntVector_Intrinsics_vec128 f12 = tmp1;
  Lib_IntVector_Intrinsics_vec128 f22 = tmp2;
  Lib_IntVector_Intrinsics_vec128 f32 = tmp3;
  Lib_IntVector_Intrinsics_vec128 f42 = tmp4;
  Lib_IntVector_Intrinsics_vec128 mh = Lib_IntVector_Intrinsics_vec128_load64((u64)0x3ffffffU);
  Lib_IntVector_Intrinsics_vec128 ml = Lib_IntVector_Intrinsics_vec128_load64((u64)0x3fffffbU);
  Lib_IntVector_Intrinsics_vec128 mask = Lib_IntVector_Intrinsics_vec128_eq64(f42, mh);
  Lib_IntVector_Intrinsics_vec128
  mask1 =
    Lib_IntVector_Intrinsics_vec128_and(mask,
      Lib_IntVector_Intrinsics_vec128_eq64(f32, mh));
  Lib_IntVector_Intrinsics_vec128
  mask2 =
    Lib_IntVector_Intrinsics_vec128_and(mask1,
      Lib_IntVector_Intrinsics_vec128_eq64(f22, mh));
  Lib_IntVector_Intrinsics_vec128
  mask3 =
    Lib_IntVector_Intrinsics_vec128_and(mask2,
      Lib_IntVector_Intrinsics_vec128_eq64(f12, mh));
  Lib_IntVector_Intrinsics_vec128
  mask4 =
    Lib_IntVector_Intrinsics_vec128_and(mask3,
      Lib_IntVector_Intrinsics_vec128_lognot(Lib_IntVector_Intrinsics_vec128_gt64(ml, f02)));
  Lib_IntVector_Intrinsics_vec128 ph = Lib_IntVector_Intrinsics_vec128_and(mask4, mh);
  Lib_IntVector_Intrinsics_vec128 pl = Lib_IntVector_Intrinsics_vec128_and(mask4, ml);
  Lib_IntVector_Intrinsics_vec128 o0 = Lib_IntVector_Intrinsics_vec128_sub64(f02, pl);
  Lib_IntVector_Intrinsics_vec128 o1 = Lib_IntVector_Intrinsics_vec128_sub64(f12, ph);
  Lib_IntVector_Intrinsics_vec128 o2 = Lib_IntVector_Intrinsics_vec128_sub64(f22, ph);
  Lib_IntVector_Intrinsics_vec128 o3 = Lib_IntVector_Intrinsics_vec128_sub64(f32, ph);
  Lib_IntVector_Intrinsics_vec128 o4 = Lib_IntVector_Intrinsics_vec128_sub64(f42, ph);
  Lib_IntVector_Intrinsics_vec128 f011 = o0;
  Lib_IntVector_Intrinsics_vec128 f111 = o1;
  Lib_IntVector_Intrinsics_vec128 f211 = o2;
  Lib_IntVector_Intrinsics_vec128 f311 = o3;
  Lib_IntVector_Intrinsics_vec128 f411 = o4;
  Lib_IntVector_Intrinsics_vec128 f0;
  Lib_IntVector_Intrinsics_vec128 f1;
  Lib_IntVector_Intrinsics_vec128 f2;
  Lib_IntVector_Intrinsics_vec128 f3;
  Lib_IntVector_Intrinsics_vec128 f4;
  u64 f01;
  u64 f112;
  u64 f212;
  u64 f312;
  u64 f41;
  u64 lo0;
  u64 hi0;
  u64 f10;
  u64 f11;
  u64 u0;
  u64 lo;
  u64 u;
  u64 hi;
  u64 f20;
  u64 f21;
  u64 r0;
  u64 r1;
  u64 c;
  u64 r11;
  u64 f30;
  u64 f31;
  acc[0U] = f011;
  acc[1U] = f111;
  acc[2U] = f211;
  acc[3U] = f311;
  acc[4U] = f411;
  f0 = acc[0U];
  f1 = acc[1U];
  f2 = acc[2U];
  f3 = acc[3U];
  f4 = acc[4U];
  f01 = Lib_IntVector_Intrinsics_vec128_extract64(f0, (u32)0U);
  f112 = Lib_IntVector_Intrinsics_vec128_extract64(f1, (u32)0U);
  f212 = Lib_IntVector_Intrinsics_vec128_extract64(f2, (u32)0U);
  f312 = Lib_IntVector_Intrinsics_vec128_extract64(f3, (u32)0U);
  f41 = Lib_IntVector_Intrinsics_vec128_extract64(f4, (u32)0U);
  lo0 = (f01 | f112 << (u32)26U) | f212 << (u32)52U;
  hi0 = (f212 >> (u32)12U | f312 << (u32)14U) | f41 << (u32)40U;
  f10 = lo0;
  f11 = hi0;
  u0 = load64_le(ks);
  lo = u0;
  u = load64_le(ks + (u32)8U);
  hi = u;
  f20 = lo;
  f21 = hi;
  r0 = f10 + f20;
  r1 = f11 + f21;
  c = (r0 ^ ((r0 ^ f20) | ((r0 - f20) ^ f20))) >> (u32)63U;
  r11 = r1 + c;
  f30 = r0;
  f31 = r11;
  store64_le(tag, f30);
  store64_le(tag + (u32)8U, f31);
}

void Hacl_Poly1305_128_poly1305_mac(u8 *tag, u32 len, u8 *text, u8 *key)
{
  Lib_IntVector_Intrinsics_vec128 ctx[25U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)25U; ++_i)
      ctx[_i] = Lib_IntVector_Intrinsics_vec128_zero;
  }
  Hacl_Poly1305_128_poly1305_init(ctx, key);
  Hacl_Poly1305_128_poly1305_update(ctx, len, text);
  Hacl_Poly1305_128_poly1305_finish(tag, key, ctx);
}

