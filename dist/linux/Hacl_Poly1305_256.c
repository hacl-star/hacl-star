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


#include "Hacl_Poly1305_256.h"

void Hacl_Impl_Poly1305_Field32xN_256_load_acc4(Lib_IntVector_Intrinsics_vec256 *acc, u8 *b)
{
  Lib_IntVector_Intrinsics_vec256 e[5U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)5U; ++_i)
      e[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  }
  {
    Lib_IntVector_Intrinsics_vec256 lo = Lib_IntVector_Intrinsics_vec256_load_le(b);
    Lib_IntVector_Intrinsics_vec256 hi = Lib_IntVector_Intrinsics_vec256_load_le(b + (u32)32U);
    Lib_IntVector_Intrinsics_vec256
    mask26 = Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU);
    Lib_IntVector_Intrinsics_vec256 m0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(lo, hi);
    Lib_IntVector_Intrinsics_vec256
    m1 = Lib_IntVector_Intrinsics_vec256_interleave_high128(lo, hi);
    Lib_IntVector_Intrinsics_vec256 m2 = Lib_IntVector_Intrinsics_vec256_shift_right(m0, (u32)48U);
    Lib_IntVector_Intrinsics_vec256 m3 = Lib_IntVector_Intrinsics_vec256_shift_right(m1, (u32)48U);
    Lib_IntVector_Intrinsics_vec256 m4 = Lib_IntVector_Intrinsics_vec256_interleave_high64(m0, m1);
    Lib_IntVector_Intrinsics_vec256 t0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(m0, m1);
    Lib_IntVector_Intrinsics_vec256 t3 = Lib_IntVector_Intrinsics_vec256_interleave_low64(m2, m3);
    Lib_IntVector_Intrinsics_vec256
    t2 = Lib_IntVector_Intrinsics_vec256_shift_right64(t3, (u32)4U);
    Lib_IntVector_Intrinsics_vec256 o20 = Lib_IntVector_Intrinsics_vec256_and(t2, mask26);
    Lib_IntVector_Intrinsics_vec256
    t1 = Lib_IntVector_Intrinsics_vec256_shift_right64(t0, (u32)26U);
    Lib_IntVector_Intrinsics_vec256 o10 = Lib_IntVector_Intrinsics_vec256_and(t1, mask26);
    Lib_IntVector_Intrinsics_vec256 o5 = Lib_IntVector_Intrinsics_vec256_and(t0, mask26);
    Lib_IntVector_Intrinsics_vec256
    t31 = Lib_IntVector_Intrinsics_vec256_shift_right64(t3, (u32)30U);
    Lib_IntVector_Intrinsics_vec256 o30 = Lib_IntVector_Intrinsics_vec256_and(t31, mask26);
    Lib_IntVector_Intrinsics_vec256
    o40 = Lib_IntVector_Intrinsics_vec256_shift_right64(m4, (u32)40U);
    Lib_IntVector_Intrinsics_vec256 o0 = o5;
    Lib_IntVector_Intrinsics_vec256 o1 = o10;
    Lib_IntVector_Intrinsics_vec256 o2 = o20;
    Lib_IntVector_Intrinsics_vec256 o3 = o30;
    Lib_IntVector_Intrinsics_vec256 o4 = o40;
    u64 b1;
    Lib_IntVector_Intrinsics_vec256 mask;
    Lib_IntVector_Intrinsics_vec256 f40;
    Lib_IntVector_Intrinsics_vec256 acc0;
    Lib_IntVector_Intrinsics_vec256 acc1;
    Lib_IntVector_Intrinsics_vec256 acc2;
    Lib_IntVector_Intrinsics_vec256 acc3;
    Lib_IntVector_Intrinsics_vec256 acc4;
    Lib_IntVector_Intrinsics_vec256 e0;
    Lib_IntVector_Intrinsics_vec256 e1;
    Lib_IntVector_Intrinsics_vec256 e2;
    Lib_IntVector_Intrinsics_vec256 e3;
    Lib_IntVector_Intrinsics_vec256 e4;
    Lib_IntVector_Intrinsics_vec256 r0;
    Lib_IntVector_Intrinsics_vec256 r1;
    Lib_IntVector_Intrinsics_vec256 r2;
    Lib_IntVector_Intrinsics_vec256 r3;
    Lib_IntVector_Intrinsics_vec256 r4;
    Lib_IntVector_Intrinsics_vec256 r01;
    Lib_IntVector_Intrinsics_vec256 r11;
    Lib_IntVector_Intrinsics_vec256 r21;
    Lib_IntVector_Intrinsics_vec256 r31;
    Lib_IntVector_Intrinsics_vec256 r41;
    Lib_IntVector_Intrinsics_vec256 f0;
    Lib_IntVector_Intrinsics_vec256 f1;
    Lib_IntVector_Intrinsics_vec256 f2;
    Lib_IntVector_Intrinsics_vec256 f3;
    Lib_IntVector_Intrinsics_vec256 f4;
    Lib_IntVector_Intrinsics_vec256 acc01;
    Lib_IntVector_Intrinsics_vec256 acc11;
    Lib_IntVector_Intrinsics_vec256 acc21;
    Lib_IntVector_Intrinsics_vec256 acc31;
    Lib_IntVector_Intrinsics_vec256 acc41;
    e[0U] = o0;
    e[1U] = o1;
    e[2U] = o2;
    e[3U] = o3;
    e[4U] = o4;
    b1 = (u64)0x1000000U;
    mask = Lib_IntVector_Intrinsics_vec256_load64(b1);
    f40 = e[4U];
    e[4U] = Lib_IntVector_Intrinsics_vec256_or(f40, mask);
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
    r0 = Lib_IntVector_Intrinsics_vec256_zero;
    r1 = Lib_IntVector_Intrinsics_vec256_zero;
    r2 = Lib_IntVector_Intrinsics_vec256_zero;
    r3 = Lib_IntVector_Intrinsics_vec256_zero;
    r4 = Lib_IntVector_Intrinsics_vec256_zero;
    r01 =
      Lib_IntVector_Intrinsics_vec256_insert64(r0,
        Lib_IntVector_Intrinsics_vec256_extract64(acc0, (u32)0U),
        (u32)0U);
    r11 =
      Lib_IntVector_Intrinsics_vec256_insert64(r1,
        Lib_IntVector_Intrinsics_vec256_extract64(acc1, (u32)0U),
        (u32)0U);
    r21 =
      Lib_IntVector_Intrinsics_vec256_insert64(r2,
        Lib_IntVector_Intrinsics_vec256_extract64(acc2, (u32)0U),
        (u32)0U);
    r31 =
      Lib_IntVector_Intrinsics_vec256_insert64(r3,
        Lib_IntVector_Intrinsics_vec256_extract64(acc3, (u32)0U),
        (u32)0U);
    r41 =
      Lib_IntVector_Intrinsics_vec256_insert64(r4,
        Lib_IntVector_Intrinsics_vec256_extract64(acc4, (u32)0U),
        (u32)0U);
    f0 = Lib_IntVector_Intrinsics_vec256_add64(r01, e0);
    f1 = Lib_IntVector_Intrinsics_vec256_add64(r11, e1);
    f2 = Lib_IntVector_Intrinsics_vec256_add64(r21, e2);
    f3 = Lib_IntVector_Intrinsics_vec256_add64(r31, e3);
    f4 = Lib_IntVector_Intrinsics_vec256_add64(r41, e4);
    acc01 = f0;
    acc11 = f1;
    acc21 = f2;
    acc31 = f3;
    acc41 = f4;
    acc[0U] = acc01;
    acc[1U] = acc11;
    acc[2U] = acc21;
    acc[3U] = acc31;
    acc[4U] = acc41;
  }
}

void
Hacl_Impl_Poly1305_Field32xN_256_fmul_r4_normalize(
  Lib_IntVector_Intrinsics_vec256 *out,
  Lib_IntVector_Intrinsics_vec256 *p
)
{
  Lib_IntVector_Intrinsics_vec256 *r = p;
  Lib_IntVector_Intrinsics_vec256 *r_5 = p + (u32)5U;
  Lib_IntVector_Intrinsics_vec256 *r4 = p + (u32)10U;
  Lib_IntVector_Intrinsics_vec256 a0 = out[0U];
  Lib_IntVector_Intrinsics_vec256 a1 = out[1U];
  Lib_IntVector_Intrinsics_vec256 a2 = out[2U];
  Lib_IntVector_Intrinsics_vec256 a3 = out[3U];
  Lib_IntVector_Intrinsics_vec256 a4 = out[4U];
  Lib_IntVector_Intrinsics_vec256 r10 = r[0U];
  Lib_IntVector_Intrinsics_vec256 r11 = r[1U];
  Lib_IntVector_Intrinsics_vec256 r12 = r[2U];
  Lib_IntVector_Intrinsics_vec256 r13 = r[3U];
  Lib_IntVector_Intrinsics_vec256 r14 = r[4U];
  Lib_IntVector_Intrinsics_vec256 r151 = r_5[1U];
  Lib_IntVector_Intrinsics_vec256 r152 = r_5[2U];
  Lib_IntVector_Intrinsics_vec256 r153 = r_5[3U];
  Lib_IntVector_Intrinsics_vec256 r154 = r_5[4U];
  Lib_IntVector_Intrinsics_vec256 r40 = r4[0U];
  Lib_IntVector_Intrinsics_vec256 r41 = r4[1U];
  Lib_IntVector_Intrinsics_vec256 r42 = r4[2U];
  Lib_IntVector_Intrinsics_vec256 r43 = r4[3U];
  Lib_IntVector_Intrinsics_vec256 r44 = r4[4U];
  Lib_IntVector_Intrinsics_vec256 a010 = Lib_IntVector_Intrinsics_vec256_mul64(r10, r10);
  Lib_IntVector_Intrinsics_vec256 a110 = Lib_IntVector_Intrinsics_vec256_mul64(r11, r10);
  Lib_IntVector_Intrinsics_vec256 a210 = Lib_IntVector_Intrinsics_vec256_mul64(r12, r10);
  Lib_IntVector_Intrinsics_vec256 a310 = Lib_IntVector_Intrinsics_vec256_mul64(r13, r10);
  Lib_IntVector_Intrinsics_vec256 a410 = Lib_IntVector_Intrinsics_vec256_mul64(r14, r10);
  Lib_IntVector_Intrinsics_vec256
  a020 =
    Lib_IntVector_Intrinsics_vec256_add64(a010,
      Lib_IntVector_Intrinsics_vec256_mul64(r154, r11));
  Lib_IntVector_Intrinsics_vec256
  a120 =
    Lib_IntVector_Intrinsics_vec256_add64(a110,
      Lib_IntVector_Intrinsics_vec256_mul64(r10, r11));
  Lib_IntVector_Intrinsics_vec256
  a220 =
    Lib_IntVector_Intrinsics_vec256_add64(a210,
      Lib_IntVector_Intrinsics_vec256_mul64(r11, r11));
  Lib_IntVector_Intrinsics_vec256
  a320 =
    Lib_IntVector_Intrinsics_vec256_add64(a310,
      Lib_IntVector_Intrinsics_vec256_mul64(r12, r11));
  Lib_IntVector_Intrinsics_vec256
  a420 =
    Lib_IntVector_Intrinsics_vec256_add64(a410,
      Lib_IntVector_Intrinsics_vec256_mul64(r13, r11));
  Lib_IntVector_Intrinsics_vec256
  a030 =
    Lib_IntVector_Intrinsics_vec256_add64(a020,
      Lib_IntVector_Intrinsics_vec256_mul64(r153, r12));
  Lib_IntVector_Intrinsics_vec256
  a130 =
    Lib_IntVector_Intrinsics_vec256_add64(a120,
      Lib_IntVector_Intrinsics_vec256_mul64(r154, r12));
  Lib_IntVector_Intrinsics_vec256
  a230 =
    Lib_IntVector_Intrinsics_vec256_add64(a220,
      Lib_IntVector_Intrinsics_vec256_mul64(r10, r12));
  Lib_IntVector_Intrinsics_vec256
  a330 =
    Lib_IntVector_Intrinsics_vec256_add64(a320,
      Lib_IntVector_Intrinsics_vec256_mul64(r11, r12));
  Lib_IntVector_Intrinsics_vec256
  a430 =
    Lib_IntVector_Intrinsics_vec256_add64(a420,
      Lib_IntVector_Intrinsics_vec256_mul64(r12, r12));
  Lib_IntVector_Intrinsics_vec256
  a040 =
    Lib_IntVector_Intrinsics_vec256_add64(a030,
      Lib_IntVector_Intrinsics_vec256_mul64(r152, r13));
  Lib_IntVector_Intrinsics_vec256
  a140 =
    Lib_IntVector_Intrinsics_vec256_add64(a130,
      Lib_IntVector_Intrinsics_vec256_mul64(r153, r13));
  Lib_IntVector_Intrinsics_vec256
  a240 =
    Lib_IntVector_Intrinsics_vec256_add64(a230,
      Lib_IntVector_Intrinsics_vec256_mul64(r154, r13));
  Lib_IntVector_Intrinsics_vec256
  a340 =
    Lib_IntVector_Intrinsics_vec256_add64(a330,
      Lib_IntVector_Intrinsics_vec256_mul64(r10, r13));
  Lib_IntVector_Intrinsics_vec256
  a440 =
    Lib_IntVector_Intrinsics_vec256_add64(a430,
      Lib_IntVector_Intrinsics_vec256_mul64(r11, r13));
  Lib_IntVector_Intrinsics_vec256
  a050 =
    Lib_IntVector_Intrinsics_vec256_add64(a040,
      Lib_IntVector_Intrinsics_vec256_mul64(r151, r14));
  Lib_IntVector_Intrinsics_vec256
  a150 =
    Lib_IntVector_Intrinsics_vec256_add64(a140,
      Lib_IntVector_Intrinsics_vec256_mul64(r152, r14));
  Lib_IntVector_Intrinsics_vec256
  a250 =
    Lib_IntVector_Intrinsics_vec256_add64(a240,
      Lib_IntVector_Intrinsics_vec256_mul64(r153, r14));
  Lib_IntVector_Intrinsics_vec256
  a350 =
    Lib_IntVector_Intrinsics_vec256_add64(a340,
      Lib_IntVector_Intrinsics_vec256_mul64(r154, r14));
  Lib_IntVector_Intrinsics_vec256
  a450 =
    Lib_IntVector_Intrinsics_vec256_add64(a440,
      Lib_IntVector_Intrinsics_vec256_mul64(r10, r14));
  Lib_IntVector_Intrinsics_vec256 t00 = a050;
  Lib_IntVector_Intrinsics_vec256 t10 = a150;
  Lib_IntVector_Intrinsics_vec256 t20 = a250;
  Lib_IntVector_Intrinsics_vec256 t30 = a350;
  Lib_IntVector_Intrinsics_vec256 t40 = a450;
  Lib_IntVector_Intrinsics_vec256
  mask260 = Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU);
  Lib_IntVector_Intrinsics_vec256
  z00 = Lib_IntVector_Intrinsics_vec256_shift_right64(t00, (u32)26U);
  Lib_IntVector_Intrinsics_vec256
  z10 = Lib_IntVector_Intrinsics_vec256_shift_right64(t30, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 x00 = Lib_IntVector_Intrinsics_vec256_and(t00, mask260);
  Lib_IntVector_Intrinsics_vec256 x30 = Lib_IntVector_Intrinsics_vec256_and(t30, mask260);
  Lib_IntVector_Intrinsics_vec256 x10 = Lib_IntVector_Intrinsics_vec256_add64(t10, z00);
  Lib_IntVector_Intrinsics_vec256 x40 = Lib_IntVector_Intrinsics_vec256_add64(t40, z10);
  Lib_IntVector_Intrinsics_vec256
  z010 = Lib_IntVector_Intrinsics_vec256_shift_right64(x10, (u32)26U);
  Lib_IntVector_Intrinsics_vec256
  z110 = Lib_IntVector_Intrinsics_vec256_shift_right64(x40, (u32)26U);
  Lib_IntVector_Intrinsics_vec256
  t5 = Lib_IntVector_Intrinsics_vec256_shift_left64(z110, (u32)2U);
  Lib_IntVector_Intrinsics_vec256 z12 = Lib_IntVector_Intrinsics_vec256_add64(z110, t5);
  Lib_IntVector_Intrinsics_vec256 x110 = Lib_IntVector_Intrinsics_vec256_and(x10, mask260);
  Lib_IntVector_Intrinsics_vec256 x410 = Lib_IntVector_Intrinsics_vec256_and(x40, mask260);
  Lib_IntVector_Intrinsics_vec256 x20 = Lib_IntVector_Intrinsics_vec256_add64(t20, z010);
  Lib_IntVector_Intrinsics_vec256 x010 = Lib_IntVector_Intrinsics_vec256_add64(x00, z12);
  Lib_IntVector_Intrinsics_vec256
  z020 = Lib_IntVector_Intrinsics_vec256_shift_right64(x20, (u32)26U);
  Lib_IntVector_Intrinsics_vec256
  z130 = Lib_IntVector_Intrinsics_vec256_shift_right64(x010, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 x210 = Lib_IntVector_Intrinsics_vec256_and(x20, mask260);
  Lib_IntVector_Intrinsics_vec256 x020 = Lib_IntVector_Intrinsics_vec256_and(x010, mask260);
  Lib_IntVector_Intrinsics_vec256 x310 = Lib_IntVector_Intrinsics_vec256_add64(x30, z020);
  Lib_IntVector_Intrinsics_vec256 x120 = Lib_IntVector_Intrinsics_vec256_add64(x110, z130);
  Lib_IntVector_Intrinsics_vec256
  z030 = Lib_IntVector_Intrinsics_vec256_shift_right64(x310, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 x320 = Lib_IntVector_Intrinsics_vec256_and(x310, mask260);
  Lib_IntVector_Intrinsics_vec256 x420 = Lib_IntVector_Intrinsics_vec256_add64(x410, z030);
  Lib_IntVector_Intrinsics_vec256 r20 = x020;
  Lib_IntVector_Intrinsics_vec256 r21 = x120;
  Lib_IntVector_Intrinsics_vec256 r22 = x210;
  Lib_IntVector_Intrinsics_vec256 r23 = x320;
  Lib_IntVector_Intrinsics_vec256 r24 = x420;
  Lib_IntVector_Intrinsics_vec256 a011 = Lib_IntVector_Intrinsics_vec256_mul64(r10, r20);
  Lib_IntVector_Intrinsics_vec256 a111 = Lib_IntVector_Intrinsics_vec256_mul64(r11, r20);
  Lib_IntVector_Intrinsics_vec256 a211 = Lib_IntVector_Intrinsics_vec256_mul64(r12, r20);
  Lib_IntVector_Intrinsics_vec256 a311 = Lib_IntVector_Intrinsics_vec256_mul64(r13, r20);
  Lib_IntVector_Intrinsics_vec256 a411 = Lib_IntVector_Intrinsics_vec256_mul64(r14, r20);
  Lib_IntVector_Intrinsics_vec256
  a021 =
    Lib_IntVector_Intrinsics_vec256_add64(a011,
      Lib_IntVector_Intrinsics_vec256_mul64(r154, r21));
  Lib_IntVector_Intrinsics_vec256
  a121 =
    Lib_IntVector_Intrinsics_vec256_add64(a111,
      Lib_IntVector_Intrinsics_vec256_mul64(r10, r21));
  Lib_IntVector_Intrinsics_vec256
  a221 =
    Lib_IntVector_Intrinsics_vec256_add64(a211,
      Lib_IntVector_Intrinsics_vec256_mul64(r11, r21));
  Lib_IntVector_Intrinsics_vec256
  a321 =
    Lib_IntVector_Intrinsics_vec256_add64(a311,
      Lib_IntVector_Intrinsics_vec256_mul64(r12, r21));
  Lib_IntVector_Intrinsics_vec256
  a421 =
    Lib_IntVector_Intrinsics_vec256_add64(a411,
      Lib_IntVector_Intrinsics_vec256_mul64(r13, r21));
  Lib_IntVector_Intrinsics_vec256
  a031 =
    Lib_IntVector_Intrinsics_vec256_add64(a021,
      Lib_IntVector_Intrinsics_vec256_mul64(r153, r22));
  Lib_IntVector_Intrinsics_vec256
  a131 =
    Lib_IntVector_Intrinsics_vec256_add64(a121,
      Lib_IntVector_Intrinsics_vec256_mul64(r154, r22));
  Lib_IntVector_Intrinsics_vec256
  a231 =
    Lib_IntVector_Intrinsics_vec256_add64(a221,
      Lib_IntVector_Intrinsics_vec256_mul64(r10, r22));
  Lib_IntVector_Intrinsics_vec256
  a331 =
    Lib_IntVector_Intrinsics_vec256_add64(a321,
      Lib_IntVector_Intrinsics_vec256_mul64(r11, r22));
  Lib_IntVector_Intrinsics_vec256
  a431 =
    Lib_IntVector_Intrinsics_vec256_add64(a421,
      Lib_IntVector_Intrinsics_vec256_mul64(r12, r22));
  Lib_IntVector_Intrinsics_vec256
  a041 =
    Lib_IntVector_Intrinsics_vec256_add64(a031,
      Lib_IntVector_Intrinsics_vec256_mul64(r152, r23));
  Lib_IntVector_Intrinsics_vec256
  a141 =
    Lib_IntVector_Intrinsics_vec256_add64(a131,
      Lib_IntVector_Intrinsics_vec256_mul64(r153, r23));
  Lib_IntVector_Intrinsics_vec256
  a241 =
    Lib_IntVector_Intrinsics_vec256_add64(a231,
      Lib_IntVector_Intrinsics_vec256_mul64(r154, r23));
  Lib_IntVector_Intrinsics_vec256
  a341 =
    Lib_IntVector_Intrinsics_vec256_add64(a331,
      Lib_IntVector_Intrinsics_vec256_mul64(r10, r23));
  Lib_IntVector_Intrinsics_vec256
  a441 =
    Lib_IntVector_Intrinsics_vec256_add64(a431,
      Lib_IntVector_Intrinsics_vec256_mul64(r11, r23));
  Lib_IntVector_Intrinsics_vec256
  a051 =
    Lib_IntVector_Intrinsics_vec256_add64(a041,
      Lib_IntVector_Intrinsics_vec256_mul64(r151, r24));
  Lib_IntVector_Intrinsics_vec256
  a151 =
    Lib_IntVector_Intrinsics_vec256_add64(a141,
      Lib_IntVector_Intrinsics_vec256_mul64(r152, r24));
  Lib_IntVector_Intrinsics_vec256
  a251 =
    Lib_IntVector_Intrinsics_vec256_add64(a241,
      Lib_IntVector_Intrinsics_vec256_mul64(r153, r24));
  Lib_IntVector_Intrinsics_vec256
  a351 =
    Lib_IntVector_Intrinsics_vec256_add64(a341,
      Lib_IntVector_Intrinsics_vec256_mul64(r154, r24));
  Lib_IntVector_Intrinsics_vec256
  a451 =
    Lib_IntVector_Intrinsics_vec256_add64(a441,
      Lib_IntVector_Intrinsics_vec256_mul64(r10, r24));
  Lib_IntVector_Intrinsics_vec256 t01 = a051;
  Lib_IntVector_Intrinsics_vec256 t11 = a151;
  Lib_IntVector_Intrinsics_vec256 t21 = a251;
  Lib_IntVector_Intrinsics_vec256 t31 = a351;
  Lib_IntVector_Intrinsics_vec256 t41 = a451;
  Lib_IntVector_Intrinsics_vec256
  mask261 = Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU);
  Lib_IntVector_Intrinsics_vec256
  z04 = Lib_IntVector_Intrinsics_vec256_shift_right64(t01, (u32)26U);
  Lib_IntVector_Intrinsics_vec256
  z14 = Lib_IntVector_Intrinsics_vec256_shift_right64(t31, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 x03 = Lib_IntVector_Intrinsics_vec256_and(t01, mask261);
  Lib_IntVector_Intrinsics_vec256 x33 = Lib_IntVector_Intrinsics_vec256_and(t31, mask261);
  Lib_IntVector_Intrinsics_vec256 x13 = Lib_IntVector_Intrinsics_vec256_add64(t11, z04);
  Lib_IntVector_Intrinsics_vec256 x43 = Lib_IntVector_Intrinsics_vec256_add64(t41, z14);
  Lib_IntVector_Intrinsics_vec256
  z011 = Lib_IntVector_Intrinsics_vec256_shift_right64(x13, (u32)26U);
  Lib_IntVector_Intrinsics_vec256
  z111 = Lib_IntVector_Intrinsics_vec256_shift_right64(x43, (u32)26U);
  Lib_IntVector_Intrinsics_vec256
  t6 = Lib_IntVector_Intrinsics_vec256_shift_left64(z111, (u32)2U);
  Lib_IntVector_Intrinsics_vec256 z120 = Lib_IntVector_Intrinsics_vec256_add64(z111, t6);
  Lib_IntVector_Intrinsics_vec256 x111 = Lib_IntVector_Intrinsics_vec256_and(x13, mask261);
  Lib_IntVector_Intrinsics_vec256 x411 = Lib_IntVector_Intrinsics_vec256_and(x43, mask261);
  Lib_IntVector_Intrinsics_vec256 x22 = Lib_IntVector_Intrinsics_vec256_add64(t21, z011);
  Lib_IntVector_Intrinsics_vec256 x011 = Lib_IntVector_Intrinsics_vec256_add64(x03, z120);
  Lib_IntVector_Intrinsics_vec256
  z021 = Lib_IntVector_Intrinsics_vec256_shift_right64(x22, (u32)26U);
  Lib_IntVector_Intrinsics_vec256
  z131 = Lib_IntVector_Intrinsics_vec256_shift_right64(x011, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 x211 = Lib_IntVector_Intrinsics_vec256_and(x22, mask261);
  Lib_IntVector_Intrinsics_vec256 x021 = Lib_IntVector_Intrinsics_vec256_and(x011, mask261);
  Lib_IntVector_Intrinsics_vec256 x311 = Lib_IntVector_Intrinsics_vec256_add64(x33, z021);
  Lib_IntVector_Intrinsics_vec256 x121 = Lib_IntVector_Intrinsics_vec256_add64(x111, z131);
  Lib_IntVector_Intrinsics_vec256
  z031 = Lib_IntVector_Intrinsics_vec256_shift_right64(x311, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 x321 = Lib_IntVector_Intrinsics_vec256_and(x311, mask261);
  Lib_IntVector_Intrinsics_vec256 x421 = Lib_IntVector_Intrinsics_vec256_add64(x411, z031);
  Lib_IntVector_Intrinsics_vec256 r30 = x021;
  Lib_IntVector_Intrinsics_vec256 r31 = x121;
  Lib_IntVector_Intrinsics_vec256 r32 = x211;
  Lib_IntVector_Intrinsics_vec256 r33 = x321;
  Lib_IntVector_Intrinsics_vec256 r34 = x421;
  Lib_IntVector_Intrinsics_vec256
  v12120 = Lib_IntVector_Intrinsics_vec256_interleave_low64(r20, r10);
  Lib_IntVector_Intrinsics_vec256
  v34340 = Lib_IntVector_Intrinsics_vec256_interleave_low64(r40, r30);
  Lib_IntVector_Intrinsics_vec256
  r12340 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v34340, v12120);
  Lib_IntVector_Intrinsics_vec256
  v12121 = Lib_IntVector_Intrinsics_vec256_interleave_low64(r21, r11);
  Lib_IntVector_Intrinsics_vec256
  v34341 = Lib_IntVector_Intrinsics_vec256_interleave_low64(r41, r31);
  Lib_IntVector_Intrinsics_vec256
  r12341 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v34341, v12121);
  Lib_IntVector_Intrinsics_vec256
  v12122 = Lib_IntVector_Intrinsics_vec256_interleave_low64(r22, r12);
  Lib_IntVector_Intrinsics_vec256
  v34342 = Lib_IntVector_Intrinsics_vec256_interleave_low64(r42, r32);
  Lib_IntVector_Intrinsics_vec256
  r12342 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v34342, v12122);
  Lib_IntVector_Intrinsics_vec256
  v12123 = Lib_IntVector_Intrinsics_vec256_interleave_low64(r23, r13);
  Lib_IntVector_Intrinsics_vec256
  v34343 = Lib_IntVector_Intrinsics_vec256_interleave_low64(r43, r33);
  Lib_IntVector_Intrinsics_vec256
  r12343 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v34343, v12123);
  Lib_IntVector_Intrinsics_vec256
  v12124 = Lib_IntVector_Intrinsics_vec256_interleave_low64(r24, r14);
  Lib_IntVector_Intrinsics_vec256
  v34344 = Lib_IntVector_Intrinsics_vec256_interleave_low64(r44, r34);
  Lib_IntVector_Intrinsics_vec256
  r12344 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v34344, v12124);
  Lib_IntVector_Intrinsics_vec256
  r123451 = Lib_IntVector_Intrinsics_vec256_smul64(r12341, (u64)5U);
  Lib_IntVector_Intrinsics_vec256
  r123452 = Lib_IntVector_Intrinsics_vec256_smul64(r12342, (u64)5U);
  Lib_IntVector_Intrinsics_vec256
  r123453 = Lib_IntVector_Intrinsics_vec256_smul64(r12343, (u64)5U);
  Lib_IntVector_Intrinsics_vec256
  r123454 = Lib_IntVector_Intrinsics_vec256_smul64(r12344, (u64)5U);
  Lib_IntVector_Intrinsics_vec256 a01 = Lib_IntVector_Intrinsics_vec256_mul64(r12340, a0);
  Lib_IntVector_Intrinsics_vec256 a11 = Lib_IntVector_Intrinsics_vec256_mul64(r12341, a0);
  Lib_IntVector_Intrinsics_vec256 a21 = Lib_IntVector_Intrinsics_vec256_mul64(r12342, a0);
  Lib_IntVector_Intrinsics_vec256 a31 = Lib_IntVector_Intrinsics_vec256_mul64(r12343, a0);
  Lib_IntVector_Intrinsics_vec256 a41 = Lib_IntVector_Intrinsics_vec256_mul64(r12344, a0);
  Lib_IntVector_Intrinsics_vec256
  a02 =
    Lib_IntVector_Intrinsics_vec256_add64(a01,
      Lib_IntVector_Intrinsics_vec256_mul64(r123454, a1));
  Lib_IntVector_Intrinsics_vec256
  a12 =
    Lib_IntVector_Intrinsics_vec256_add64(a11,
      Lib_IntVector_Intrinsics_vec256_mul64(r12340, a1));
  Lib_IntVector_Intrinsics_vec256
  a22 =
    Lib_IntVector_Intrinsics_vec256_add64(a21,
      Lib_IntVector_Intrinsics_vec256_mul64(r12341, a1));
  Lib_IntVector_Intrinsics_vec256
  a32 =
    Lib_IntVector_Intrinsics_vec256_add64(a31,
      Lib_IntVector_Intrinsics_vec256_mul64(r12342, a1));
  Lib_IntVector_Intrinsics_vec256
  a42 =
    Lib_IntVector_Intrinsics_vec256_add64(a41,
      Lib_IntVector_Intrinsics_vec256_mul64(r12343, a1));
  Lib_IntVector_Intrinsics_vec256
  a03 =
    Lib_IntVector_Intrinsics_vec256_add64(a02,
      Lib_IntVector_Intrinsics_vec256_mul64(r123453, a2));
  Lib_IntVector_Intrinsics_vec256
  a13 =
    Lib_IntVector_Intrinsics_vec256_add64(a12,
      Lib_IntVector_Intrinsics_vec256_mul64(r123454, a2));
  Lib_IntVector_Intrinsics_vec256
  a23 =
    Lib_IntVector_Intrinsics_vec256_add64(a22,
      Lib_IntVector_Intrinsics_vec256_mul64(r12340, a2));
  Lib_IntVector_Intrinsics_vec256
  a33 =
    Lib_IntVector_Intrinsics_vec256_add64(a32,
      Lib_IntVector_Intrinsics_vec256_mul64(r12341, a2));
  Lib_IntVector_Intrinsics_vec256
  a43 =
    Lib_IntVector_Intrinsics_vec256_add64(a42,
      Lib_IntVector_Intrinsics_vec256_mul64(r12342, a2));
  Lib_IntVector_Intrinsics_vec256
  a04 =
    Lib_IntVector_Intrinsics_vec256_add64(a03,
      Lib_IntVector_Intrinsics_vec256_mul64(r123452, a3));
  Lib_IntVector_Intrinsics_vec256
  a14 =
    Lib_IntVector_Intrinsics_vec256_add64(a13,
      Lib_IntVector_Intrinsics_vec256_mul64(r123453, a3));
  Lib_IntVector_Intrinsics_vec256
  a24 =
    Lib_IntVector_Intrinsics_vec256_add64(a23,
      Lib_IntVector_Intrinsics_vec256_mul64(r123454, a3));
  Lib_IntVector_Intrinsics_vec256
  a34 =
    Lib_IntVector_Intrinsics_vec256_add64(a33,
      Lib_IntVector_Intrinsics_vec256_mul64(r12340, a3));
  Lib_IntVector_Intrinsics_vec256
  a44 =
    Lib_IntVector_Intrinsics_vec256_add64(a43,
      Lib_IntVector_Intrinsics_vec256_mul64(r12341, a3));
  Lib_IntVector_Intrinsics_vec256
  a05 =
    Lib_IntVector_Intrinsics_vec256_add64(a04,
      Lib_IntVector_Intrinsics_vec256_mul64(r123451, a4));
  Lib_IntVector_Intrinsics_vec256
  a15 =
    Lib_IntVector_Intrinsics_vec256_add64(a14,
      Lib_IntVector_Intrinsics_vec256_mul64(r123452, a4));
  Lib_IntVector_Intrinsics_vec256
  a25 =
    Lib_IntVector_Intrinsics_vec256_add64(a24,
      Lib_IntVector_Intrinsics_vec256_mul64(r123453, a4));
  Lib_IntVector_Intrinsics_vec256
  a35 =
    Lib_IntVector_Intrinsics_vec256_add64(a34,
      Lib_IntVector_Intrinsics_vec256_mul64(r123454, a4));
  Lib_IntVector_Intrinsics_vec256
  a45 =
    Lib_IntVector_Intrinsics_vec256_add64(a44,
      Lib_IntVector_Intrinsics_vec256_mul64(r12340, a4));
  Lib_IntVector_Intrinsics_vec256 t0 = a05;
  Lib_IntVector_Intrinsics_vec256 t1 = a15;
  Lib_IntVector_Intrinsics_vec256 t2 = a25;
  Lib_IntVector_Intrinsics_vec256 t3 = a35;
  Lib_IntVector_Intrinsics_vec256 t4 = a45;
  Lib_IntVector_Intrinsics_vec256
  mask26 = Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU);
  Lib_IntVector_Intrinsics_vec256
  z0 = Lib_IntVector_Intrinsics_vec256_shift_right64(t0, (u32)26U);
  Lib_IntVector_Intrinsics_vec256
  z1 = Lib_IntVector_Intrinsics_vec256_shift_right64(t3, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 x0 = Lib_IntVector_Intrinsics_vec256_and(t0, mask26);
  Lib_IntVector_Intrinsics_vec256 x3 = Lib_IntVector_Intrinsics_vec256_and(t3, mask26);
  Lib_IntVector_Intrinsics_vec256 x1 = Lib_IntVector_Intrinsics_vec256_add64(t1, z0);
  Lib_IntVector_Intrinsics_vec256 x4 = Lib_IntVector_Intrinsics_vec256_add64(t4, z1);
  Lib_IntVector_Intrinsics_vec256
  z01 = Lib_IntVector_Intrinsics_vec256_shift_right64(x1, (u32)26U);
  Lib_IntVector_Intrinsics_vec256
  z11 = Lib_IntVector_Intrinsics_vec256_shift_right64(x4, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 t = Lib_IntVector_Intrinsics_vec256_shift_left64(z11, (u32)2U);
  Lib_IntVector_Intrinsics_vec256 z121 = Lib_IntVector_Intrinsics_vec256_add64(z11, t);
  Lib_IntVector_Intrinsics_vec256 x11 = Lib_IntVector_Intrinsics_vec256_and(x1, mask26);
  Lib_IntVector_Intrinsics_vec256 x41 = Lib_IntVector_Intrinsics_vec256_and(x4, mask26);
  Lib_IntVector_Intrinsics_vec256 x2 = Lib_IntVector_Intrinsics_vec256_add64(t2, z01);
  Lib_IntVector_Intrinsics_vec256 x01 = Lib_IntVector_Intrinsics_vec256_add64(x0, z121);
  Lib_IntVector_Intrinsics_vec256
  z02 = Lib_IntVector_Intrinsics_vec256_shift_right64(x2, (u32)26U);
  Lib_IntVector_Intrinsics_vec256
  z13 = Lib_IntVector_Intrinsics_vec256_shift_right64(x01, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 x21 = Lib_IntVector_Intrinsics_vec256_and(x2, mask26);
  Lib_IntVector_Intrinsics_vec256 x02 = Lib_IntVector_Intrinsics_vec256_and(x01, mask26);
  Lib_IntVector_Intrinsics_vec256 x31 = Lib_IntVector_Intrinsics_vec256_add64(x3, z02);
  Lib_IntVector_Intrinsics_vec256 x12 = Lib_IntVector_Intrinsics_vec256_add64(x11, z13);
  Lib_IntVector_Intrinsics_vec256
  z03 = Lib_IntVector_Intrinsics_vec256_shift_right64(x31, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 x32 = Lib_IntVector_Intrinsics_vec256_and(x31, mask26);
  Lib_IntVector_Intrinsics_vec256 x42 = Lib_IntVector_Intrinsics_vec256_add64(x41, z03);
  Lib_IntVector_Intrinsics_vec256 o0 = x02;
  Lib_IntVector_Intrinsics_vec256 o10 = x12;
  Lib_IntVector_Intrinsics_vec256 o20 = x21;
  Lib_IntVector_Intrinsics_vec256 o30 = x32;
  Lib_IntVector_Intrinsics_vec256 o40 = x42;
  Lib_IntVector_Intrinsics_vec256
  v00 = Lib_IntVector_Intrinsics_vec256_interleave_high128(o0, o0);
  Lib_IntVector_Intrinsics_vec256 v10 = Lib_IntVector_Intrinsics_vec256_add64(o0, v00);
  Lib_IntVector_Intrinsics_vec256
  v10h = Lib_IntVector_Intrinsics_vec256_interleave_high64(v10, v10);
  Lib_IntVector_Intrinsics_vec256 v20 = Lib_IntVector_Intrinsics_vec256_add64(v10, v10h);
  Lib_IntVector_Intrinsics_vec256
  v01 = Lib_IntVector_Intrinsics_vec256_interleave_high128(o10, o10);
  Lib_IntVector_Intrinsics_vec256 v11 = Lib_IntVector_Intrinsics_vec256_add64(o10, v01);
  Lib_IntVector_Intrinsics_vec256
  v11h = Lib_IntVector_Intrinsics_vec256_interleave_high64(v11, v11);
  Lib_IntVector_Intrinsics_vec256 v21 = Lib_IntVector_Intrinsics_vec256_add64(v11, v11h);
  Lib_IntVector_Intrinsics_vec256
  v02 = Lib_IntVector_Intrinsics_vec256_interleave_high128(o20, o20);
  Lib_IntVector_Intrinsics_vec256 v12 = Lib_IntVector_Intrinsics_vec256_add64(o20, v02);
  Lib_IntVector_Intrinsics_vec256
  v12h = Lib_IntVector_Intrinsics_vec256_interleave_high64(v12, v12);
  Lib_IntVector_Intrinsics_vec256 v22 = Lib_IntVector_Intrinsics_vec256_add64(v12, v12h);
  Lib_IntVector_Intrinsics_vec256
  v03 = Lib_IntVector_Intrinsics_vec256_interleave_high128(o30, o30);
  Lib_IntVector_Intrinsics_vec256 v13 = Lib_IntVector_Intrinsics_vec256_add64(o30, v03);
  Lib_IntVector_Intrinsics_vec256
  v13h = Lib_IntVector_Intrinsics_vec256_interleave_high64(v13, v13);
  Lib_IntVector_Intrinsics_vec256 v23 = Lib_IntVector_Intrinsics_vec256_add64(v13, v13h);
  Lib_IntVector_Intrinsics_vec256
  v04 = Lib_IntVector_Intrinsics_vec256_interleave_high128(o40, o40);
  Lib_IntVector_Intrinsics_vec256 v14 = Lib_IntVector_Intrinsics_vec256_add64(o40, v04);
  Lib_IntVector_Intrinsics_vec256
  v14h = Lib_IntVector_Intrinsics_vec256_interleave_high64(v14, v14);
  Lib_IntVector_Intrinsics_vec256 v24 = Lib_IntVector_Intrinsics_vec256_add64(v14, v14h);
  Lib_IntVector_Intrinsics_vec256
  l = Lib_IntVector_Intrinsics_vec256_add64(v20, Lib_IntVector_Intrinsics_vec256_zero);
  Lib_IntVector_Intrinsics_vec256
  tmp0 =
    Lib_IntVector_Intrinsics_vec256_and(l,
      Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec256
  c0 = Lib_IntVector_Intrinsics_vec256_shift_right64(l, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 l0 = Lib_IntVector_Intrinsics_vec256_add64(v21, c0);
  Lib_IntVector_Intrinsics_vec256
  tmp1 =
    Lib_IntVector_Intrinsics_vec256_and(l0,
      Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec256
  c1 = Lib_IntVector_Intrinsics_vec256_shift_right64(l0, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 l1 = Lib_IntVector_Intrinsics_vec256_add64(v22, c1);
  Lib_IntVector_Intrinsics_vec256
  tmp2 =
    Lib_IntVector_Intrinsics_vec256_and(l1,
      Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec256
  c2 = Lib_IntVector_Intrinsics_vec256_shift_right64(l1, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 l2 = Lib_IntVector_Intrinsics_vec256_add64(v23, c2);
  Lib_IntVector_Intrinsics_vec256
  tmp3 =
    Lib_IntVector_Intrinsics_vec256_and(l2,
      Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec256
  c3 = Lib_IntVector_Intrinsics_vec256_shift_right64(l2, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 l3 = Lib_IntVector_Intrinsics_vec256_add64(v24, c3);
  Lib_IntVector_Intrinsics_vec256
  tmp4 =
    Lib_IntVector_Intrinsics_vec256_and(l3,
      Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec256
  c4 = Lib_IntVector_Intrinsics_vec256_shift_right64(l3, (u32)26U);
  Lib_IntVector_Intrinsics_vec256
  o00 =
    Lib_IntVector_Intrinsics_vec256_add64(tmp0,
      Lib_IntVector_Intrinsics_vec256_smul64(c4, (u64)5U));
  Lib_IntVector_Intrinsics_vec256 o1 = tmp1;
  Lib_IntVector_Intrinsics_vec256 o2 = tmp2;
  Lib_IntVector_Intrinsics_vec256 o3 = tmp3;
  Lib_IntVector_Intrinsics_vec256 o4 = tmp4;
  out[0U] = o00;
  out[1U] = o1;
  out[2U] = o2;
  out[3U] = o3;
  out[4U] = o4;
}

u32 Hacl_Poly1305_256_blocklen = (u32)16U;

void Hacl_Poly1305_256_poly1305_init(Lib_IntVector_Intrinsics_vec256 *ctx, u8 *key)
{
  Lib_IntVector_Intrinsics_vec256 *acc = ctx;
  Lib_IntVector_Intrinsics_vec256 *pre = ctx + (u32)5U;
  u8 *kr = key;
  u64 u0;
  u64 lo;
  u64 u;
  u64 hi;
  u64 mask0;
  u64 mask1;
  u64 lo1;
  u64 hi1;
  Lib_IntVector_Intrinsics_vec256 *r;
  Lib_IntVector_Intrinsics_vec256 *r5;
  Lib_IntVector_Intrinsics_vec256 *rn;
  Lib_IntVector_Intrinsics_vec256 *rn_5;
  Lib_IntVector_Intrinsics_vec256 r_vec0;
  Lib_IntVector_Intrinsics_vec256 r_vec1;
  Lib_IntVector_Intrinsics_vec256 f00;
  Lib_IntVector_Intrinsics_vec256 f15;
  Lib_IntVector_Intrinsics_vec256 f25;
  Lib_IntVector_Intrinsics_vec256 f30;
  Lib_IntVector_Intrinsics_vec256 f40;
  Lib_IntVector_Intrinsics_vec256 f0;
  Lib_IntVector_Intrinsics_vec256 f1;
  Lib_IntVector_Intrinsics_vec256 f2;
  Lib_IntVector_Intrinsics_vec256 f3;
  Lib_IntVector_Intrinsics_vec256 f4;
  Lib_IntVector_Intrinsics_vec256 f200;
  Lib_IntVector_Intrinsics_vec256 f210;
  Lib_IntVector_Intrinsics_vec256 f220;
  Lib_IntVector_Intrinsics_vec256 f230;
  Lib_IntVector_Intrinsics_vec256 f240;
  Lib_IntVector_Intrinsics_vec256 r00;
  Lib_IntVector_Intrinsics_vec256 r10;
  Lib_IntVector_Intrinsics_vec256 r20;
  Lib_IntVector_Intrinsics_vec256 r30;
  Lib_IntVector_Intrinsics_vec256 r40;
  Lib_IntVector_Intrinsics_vec256 r510;
  Lib_IntVector_Intrinsics_vec256 r520;
  Lib_IntVector_Intrinsics_vec256 r530;
  Lib_IntVector_Intrinsics_vec256 r540;
  Lib_IntVector_Intrinsics_vec256 f100;
  Lib_IntVector_Intrinsics_vec256 f110;
  Lib_IntVector_Intrinsics_vec256 f120;
  Lib_IntVector_Intrinsics_vec256 f130;
  Lib_IntVector_Intrinsics_vec256 f140;
  Lib_IntVector_Intrinsics_vec256 a00;
  Lib_IntVector_Intrinsics_vec256 a10;
  Lib_IntVector_Intrinsics_vec256 a20;
  Lib_IntVector_Intrinsics_vec256 a30;
  Lib_IntVector_Intrinsics_vec256 a40;
  Lib_IntVector_Intrinsics_vec256 a010;
  Lib_IntVector_Intrinsics_vec256 a110;
  Lib_IntVector_Intrinsics_vec256 a210;
  Lib_IntVector_Intrinsics_vec256 a310;
  Lib_IntVector_Intrinsics_vec256 a410;
  Lib_IntVector_Intrinsics_vec256 a020;
  Lib_IntVector_Intrinsics_vec256 a120;
  Lib_IntVector_Intrinsics_vec256 a220;
  Lib_IntVector_Intrinsics_vec256 a320;
  Lib_IntVector_Intrinsics_vec256 a420;
  Lib_IntVector_Intrinsics_vec256 a030;
  Lib_IntVector_Intrinsics_vec256 a130;
  Lib_IntVector_Intrinsics_vec256 a230;
  Lib_IntVector_Intrinsics_vec256 a330;
  Lib_IntVector_Intrinsics_vec256 a430;
  Lib_IntVector_Intrinsics_vec256 a040;
  Lib_IntVector_Intrinsics_vec256 a140;
  Lib_IntVector_Intrinsics_vec256 a240;
  Lib_IntVector_Intrinsics_vec256 a340;
  Lib_IntVector_Intrinsics_vec256 a440;
  Lib_IntVector_Intrinsics_vec256 t00;
  Lib_IntVector_Intrinsics_vec256 t10;
  Lib_IntVector_Intrinsics_vec256 t20;
  Lib_IntVector_Intrinsics_vec256 t30;
  Lib_IntVector_Intrinsics_vec256 t40;
  Lib_IntVector_Intrinsics_vec256 mask260;
  Lib_IntVector_Intrinsics_vec256 z00;
  Lib_IntVector_Intrinsics_vec256 z10;
  Lib_IntVector_Intrinsics_vec256 x00;
  Lib_IntVector_Intrinsics_vec256 x30;
  Lib_IntVector_Intrinsics_vec256 x10;
  Lib_IntVector_Intrinsics_vec256 x40;
  Lib_IntVector_Intrinsics_vec256 z010;
  Lib_IntVector_Intrinsics_vec256 z110;
  Lib_IntVector_Intrinsics_vec256 t5;
  Lib_IntVector_Intrinsics_vec256 z120;
  Lib_IntVector_Intrinsics_vec256 x110;
  Lib_IntVector_Intrinsics_vec256 x410;
  Lib_IntVector_Intrinsics_vec256 x20;
  Lib_IntVector_Intrinsics_vec256 x010;
  Lib_IntVector_Intrinsics_vec256 z020;
  Lib_IntVector_Intrinsics_vec256 z130;
  Lib_IntVector_Intrinsics_vec256 x210;
  Lib_IntVector_Intrinsics_vec256 x020;
  Lib_IntVector_Intrinsics_vec256 x310;
  Lib_IntVector_Intrinsics_vec256 x120;
  Lib_IntVector_Intrinsics_vec256 z030;
  Lib_IntVector_Intrinsics_vec256 x320;
  Lib_IntVector_Intrinsics_vec256 x420;
  Lib_IntVector_Intrinsics_vec256 o00;
  Lib_IntVector_Intrinsics_vec256 o10;
  Lib_IntVector_Intrinsics_vec256 o20;
  Lib_IntVector_Intrinsics_vec256 o30;
  Lib_IntVector_Intrinsics_vec256 o40;
  Lib_IntVector_Intrinsics_vec256 f201;
  Lib_IntVector_Intrinsics_vec256 f211;
  Lib_IntVector_Intrinsics_vec256 f221;
  Lib_IntVector_Intrinsics_vec256 f231;
  Lib_IntVector_Intrinsics_vec256 f241;
  Lib_IntVector_Intrinsics_vec256 r0;
  Lib_IntVector_Intrinsics_vec256 r1;
  Lib_IntVector_Intrinsics_vec256 r2;
  Lib_IntVector_Intrinsics_vec256 r3;
  Lib_IntVector_Intrinsics_vec256 r4;
  Lib_IntVector_Intrinsics_vec256 r51;
  Lib_IntVector_Intrinsics_vec256 r52;
  Lib_IntVector_Intrinsics_vec256 r53;
  Lib_IntVector_Intrinsics_vec256 r54;
  Lib_IntVector_Intrinsics_vec256 f10;
  Lib_IntVector_Intrinsics_vec256 f11;
  Lib_IntVector_Intrinsics_vec256 f12;
  Lib_IntVector_Intrinsics_vec256 f13;
  Lib_IntVector_Intrinsics_vec256 f14;
  Lib_IntVector_Intrinsics_vec256 a0;
  Lib_IntVector_Intrinsics_vec256 a1;
  Lib_IntVector_Intrinsics_vec256 a2;
  Lib_IntVector_Intrinsics_vec256 a3;
  Lib_IntVector_Intrinsics_vec256 a4;
  Lib_IntVector_Intrinsics_vec256 a01;
  Lib_IntVector_Intrinsics_vec256 a11;
  Lib_IntVector_Intrinsics_vec256 a21;
  Lib_IntVector_Intrinsics_vec256 a31;
  Lib_IntVector_Intrinsics_vec256 a41;
  Lib_IntVector_Intrinsics_vec256 a02;
  Lib_IntVector_Intrinsics_vec256 a12;
  Lib_IntVector_Intrinsics_vec256 a22;
  Lib_IntVector_Intrinsics_vec256 a32;
  Lib_IntVector_Intrinsics_vec256 a42;
  Lib_IntVector_Intrinsics_vec256 a03;
  Lib_IntVector_Intrinsics_vec256 a13;
  Lib_IntVector_Intrinsics_vec256 a23;
  Lib_IntVector_Intrinsics_vec256 a33;
  Lib_IntVector_Intrinsics_vec256 a43;
  Lib_IntVector_Intrinsics_vec256 a04;
  Lib_IntVector_Intrinsics_vec256 a14;
  Lib_IntVector_Intrinsics_vec256 a24;
  Lib_IntVector_Intrinsics_vec256 a34;
  Lib_IntVector_Intrinsics_vec256 a44;
  Lib_IntVector_Intrinsics_vec256 t0;
  Lib_IntVector_Intrinsics_vec256 t1;
  Lib_IntVector_Intrinsics_vec256 t2;
  Lib_IntVector_Intrinsics_vec256 t3;
  Lib_IntVector_Intrinsics_vec256 t4;
  Lib_IntVector_Intrinsics_vec256 mask26;
  Lib_IntVector_Intrinsics_vec256 z0;
  Lib_IntVector_Intrinsics_vec256 z1;
  Lib_IntVector_Intrinsics_vec256 x0;
  Lib_IntVector_Intrinsics_vec256 x3;
  Lib_IntVector_Intrinsics_vec256 x1;
  Lib_IntVector_Intrinsics_vec256 x4;
  Lib_IntVector_Intrinsics_vec256 z01;
  Lib_IntVector_Intrinsics_vec256 z11;
  Lib_IntVector_Intrinsics_vec256 t;
  Lib_IntVector_Intrinsics_vec256 z12;
  Lib_IntVector_Intrinsics_vec256 x11;
  Lib_IntVector_Intrinsics_vec256 x41;
  Lib_IntVector_Intrinsics_vec256 x2;
  Lib_IntVector_Intrinsics_vec256 x01;
  Lib_IntVector_Intrinsics_vec256 z02;
  Lib_IntVector_Intrinsics_vec256 z13;
  Lib_IntVector_Intrinsics_vec256 x21;
  Lib_IntVector_Intrinsics_vec256 x02;
  Lib_IntVector_Intrinsics_vec256 x31;
  Lib_IntVector_Intrinsics_vec256 x12;
  Lib_IntVector_Intrinsics_vec256 z03;
  Lib_IntVector_Intrinsics_vec256 x32;
  Lib_IntVector_Intrinsics_vec256 x42;
  Lib_IntVector_Intrinsics_vec256 o0;
  Lib_IntVector_Intrinsics_vec256 o1;
  Lib_IntVector_Intrinsics_vec256 o2;
  Lib_IntVector_Intrinsics_vec256 o3;
  Lib_IntVector_Intrinsics_vec256 o4;
  Lib_IntVector_Intrinsics_vec256 f20;
  Lib_IntVector_Intrinsics_vec256 f21;
  Lib_IntVector_Intrinsics_vec256 f22;
  Lib_IntVector_Intrinsics_vec256 f23;
  Lib_IntVector_Intrinsics_vec256 f24;
  acc[0U] = Lib_IntVector_Intrinsics_vec256_zero;
  acc[1U] = Lib_IntVector_Intrinsics_vec256_zero;
  acc[2U] = Lib_IntVector_Intrinsics_vec256_zero;
  acc[3U] = Lib_IntVector_Intrinsics_vec256_zero;
  acc[4U] = Lib_IntVector_Intrinsics_vec256_zero;
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
  r_vec0 = Lib_IntVector_Intrinsics_vec256_load64(lo1);
  r_vec1 = Lib_IntVector_Intrinsics_vec256_load64(hi1);
  f00 =
    Lib_IntVector_Intrinsics_vec256_and(r_vec0,
      Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
  f15 =
    Lib_IntVector_Intrinsics_vec256_and(Lib_IntVector_Intrinsics_vec256_shift_right64(r_vec0,
        (u32)26U),
      Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
  f25 =
    Lib_IntVector_Intrinsics_vec256_or(Lib_IntVector_Intrinsics_vec256_shift_right64(r_vec0,
        (u32)52U),
      Lib_IntVector_Intrinsics_vec256_shift_left64(Lib_IntVector_Intrinsics_vec256_and(r_vec1,
          Lib_IntVector_Intrinsics_vec256_load64((u64)0x3fffU)),
        (u32)12U));
  f30 =
    Lib_IntVector_Intrinsics_vec256_and(Lib_IntVector_Intrinsics_vec256_shift_right64(r_vec1,
        (u32)14U),
      Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
  f40 = Lib_IntVector_Intrinsics_vec256_shift_right64(r_vec1, (u32)40U);
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
  r5[0U] = Lib_IntVector_Intrinsics_vec256_smul64(f200, (u64)5U);
  r5[1U] = Lib_IntVector_Intrinsics_vec256_smul64(f210, (u64)5U);
  r5[2U] = Lib_IntVector_Intrinsics_vec256_smul64(f220, (u64)5U);
  r5[3U] = Lib_IntVector_Intrinsics_vec256_smul64(f230, (u64)5U);
  r5[4U] = Lib_IntVector_Intrinsics_vec256_smul64(f240, (u64)5U);
  r00 = r[0U];
  r10 = r[1U];
  r20 = r[2U];
  r30 = r[3U];
  r40 = r[4U];
  r510 = r5[1U];
  r520 = r5[2U];
  r530 = r5[3U];
  r540 = r5[4U];
  f100 = r[0U];
  f110 = r[1U];
  f120 = r[2U];
  f130 = r[3U];
  f140 = r[4U];
  a00 = Lib_IntVector_Intrinsics_vec256_mul64(r00, f100);
  a10 = Lib_IntVector_Intrinsics_vec256_mul64(r10, f100);
  a20 = Lib_IntVector_Intrinsics_vec256_mul64(r20, f100);
  a30 = Lib_IntVector_Intrinsics_vec256_mul64(r30, f100);
  a40 = Lib_IntVector_Intrinsics_vec256_mul64(r40, f100);
  a010 =
    Lib_IntVector_Intrinsics_vec256_add64(a00,
      Lib_IntVector_Intrinsics_vec256_mul64(r540, f110));
  a110 =
    Lib_IntVector_Intrinsics_vec256_add64(a10,
      Lib_IntVector_Intrinsics_vec256_mul64(r00, f110));
  a210 =
    Lib_IntVector_Intrinsics_vec256_add64(a20,
      Lib_IntVector_Intrinsics_vec256_mul64(r10, f110));
  a310 =
    Lib_IntVector_Intrinsics_vec256_add64(a30,
      Lib_IntVector_Intrinsics_vec256_mul64(r20, f110));
  a410 =
    Lib_IntVector_Intrinsics_vec256_add64(a40,
      Lib_IntVector_Intrinsics_vec256_mul64(r30, f110));
  a020 =
    Lib_IntVector_Intrinsics_vec256_add64(a010,
      Lib_IntVector_Intrinsics_vec256_mul64(r530, f120));
  a120 =
    Lib_IntVector_Intrinsics_vec256_add64(a110,
      Lib_IntVector_Intrinsics_vec256_mul64(r540, f120));
  a220 =
    Lib_IntVector_Intrinsics_vec256_add64(a210,
      Lib_IntVector_Intrinsics_vec256_mul64(r00, f120));
  a320 =
    Lib_IntVector_Intrinsics_vec256_add64(a310,
      Lib_IntVector_Intrinsics_vec256_mul64(r10, f120));
  a420 =
    Lib_IntVector_Intrinsics_vec256_add64(a410,
      Lib_IntVector_Intrinsics_vec256_mul64(r20, f120));
  a030 =
    Lib_IntVector_Intrinsics_vec256_add64(a020,
      Lib_IntVector_Intrinsics_vec256_mul64(r520, f130));
  a130 =
    Lib_IntVector_Intrinsics_vec256_add64(a120,
      Lib_IntVector_Intrinsics_vec256_mul64(r530, f130));
  a230 =
    Lib_IntVector_Intrinsics_vec256_add64(a220,
      Lib_IntVector_Intrinsics_vec256_mul64(r540, f130));
  a330 =
    Lib_IntVector_Intrinsics_vec256_add64(a320,
      Lib_IntVector_Intrinsics_vec256_mul64(r00, f130));
  a430 =
    Lib_IntVector_Intrinsics_vec256_add64(a420,
      Lib_IntVector_Intrinsics_vec256_mul64(r10, f130));
  a040 =
    Lib_IntVector_Intrinsics_vec256_add64(a030,
      Lib_IntVector_Intrinsics_vec256_mul64(r510, f140));
  a140 =
    Lib_IntVector_Intrinsics_vec256_add64(a130,
      Lib_IntVector_Intrinsics_vec256_mul64(r520, f140));
  a240 =
    Lib_IntVector_Intrinsics_vec256_add64(a230,
      Lib_IntVector_Intrinsics_vec256_mul64(r530, f140));
  a340 =
    Lib_IntVector_Intrinsics_vec256_add64(a330,
      Lib_IntVector_Intrinsics_vec256_mul64(r540, f140));
  a440 =
    Lib_IntVector_Intrinsics_vec256_add64(a430,
      Lib_IntVector_Intrinsics_vec256_mul64(r00, f140));
  t00 = a040;
  t10 = a140;
  t20 = a240;
  t30 = a340;
  t40 = a440;
  mask260 = Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU);
  z00 = Lib_IntVector_Intrinsics_vec256_shift_right64(t00, (u32)26U);
  z10 = Lib_IntVector_Intrinsics_vec256_shift_right64(t30, (u32)26U);
  x00 = Lib_IntVector_Intrinsics_vec256_and(t00, mask260);
  x30 = Lib_IntVector_Intrinsics_vec256_and(t30, mask260);
  x10 = Lib_IntVector_Intrinsics_vec256_add64(t10, z00);
  x40 = Lib_IntVector_Intrinsics_vec256_add64(t40, z10);
  z010 = Lib_IntVector_Intrinsics_vec256_shift_right64(x10, (u32)26U);
  z110 = Lib_IntVector_Intrinsics_vec256_shift_right64(x40, (u32)26U);
  t5 = Lib_IntVector_Intrinsics_vec256_shift_left64(z110, (u32)2U);
  z120 = Lib_IntVector_Intrinsics_vec256_add64(z110, t5);
  x110 = Lib_IntVector_Intrinsics_vec256_and(x10, mask260);
  x410 = Lib_IntVector_Intrinsics_vec256_and(x40, mask260);
  x20 = Lib_IntVector_Intrinsics_vec256_add64(t20, z010);
  x010 = Lib_IntVector_Intrinsics_vec256_add64(x00, z120);
  z020 = Lib_IntVector_Intrinsics_vec256_shift_right64(x20, (u32)26U);
  z130 = Lib_IntVector_Intrinsics_vec256_shift_right64(x010, (u32)26U);
  x210 = Lib_IntVector_Intrinsics_vec256_and(x20, mask260);
  x020 = Lib_IntVector_Intrinsics_vec256_and(x010, mask260);
  x310 = Lib_IntVector_Intrinsics_vec256_add64(x30, z020);
  x120 = Lib_IntVector_Intrinsics_vec256_add64(x110, z130);
  z030 = Lib_IntVector_Intrinsics_vec256_shift_right64(x310, (u32)26U);
  x320 = Lib_IntVector_Intrinsics_vec256_and(x310, mask260);
  x420 = Lib_IntVector_Intrinsics_vec256_add64(x410, z030);
  o00 = x020;
  o10 = x120;
  o20 = x210;
  o30 = x320;
  o40 = x420;
  rn[0U] = o00;
  rn[1U] = o10;
  rn[2U] = o20;
  rn[3U] = o30;
  rn[4U] = o40;
  f201 = rn[0U];
  f211 = rn[1U];
  f221 = rn[2U];
  f231 = rn[3U];
  f241 = rn[4U];
  rn_5[0U] = Lib_IntVector_Intrinsics_vec256_smul64(f201, (u64)5U);
  rn_5[1U] = Lib_IntVector_Intrinsics_vec256_smul64(f211, (u64)5U);
  rn_5[2U] = Lib_IntVector_Intrinsics_vec256_smul64(f221, (u64)5U);
  rn_5[3U] = Lib_IntVector_Intrinsics_vec256_smul64(f231, (u64)5U);
  rn_5[4U] = Lib_IntVector_Intrinsics_vec256_smul64(f241, (u64)5U);
  r0 = rn[0U];
  r1 = rn[1U];
  r2 = rn[2U];
  r3 = rn[3U];
  r4 = rn[4U];
  r51 = rn_5[1U];
  r52 = rn_5[2U];
  r53 = rn_5[3U];
  r54 = rn_5[4U];
  f10 = rn[0U];
  f11 = rn[1U];
  f12 = rn[2U];
  f13 = rn[3U];
  f14 = rn[4U];
  a0 = Lib_IntVector_Intrinsics_vec256_mul64(r0, f10);
  a1 = Lib_IntVector_Intrinsics_vec256_mul64(r1, f10);
  a2 = Lib_IntVector_Intrinsics_vec256_mul64(r2, f10);
  a3 = Lib_IntVector_Intrinsics_vec256_mul64(r3, f10);
  a4 = Lib_IntVector_Intrinsics_vec256_mul64(r4, f10);
  a01 =
    Lib_IntVector_Intrinsics_vec256_add64(a0,
      Lib_IntVector_Intrinsics_vec256_mul64(r54, f11));
  a11 = Lib_IntVector_Intrinsics_vec256_add64(a1, Lib_IntVector_Intrinsics_vec256_mul64(r0, f11));
  a21 = Lib_IntVector_Intrinsics_vec256_add64(a2, Lib_IntVector_Intrinsics_vec256_mul64(r1, f11));
  a31 = Lib_IntVector_Intrinsics_vec256_add64(a3, Lib_IntVector_Intrinsics_vec256_mul64(r2, f11));
  a41 = Lib_IntVector_Intrinsics_vec256_add64(a4, Lib_IntVector_Intrinsics_vec256_mul64(r3, f11));
  a02 =
    Lib_IntVector_Intrinsics_vec256_add64(a01,
      Lib_IntVector_Intrinsics_vec256_mul64(r53, f12));
  a12 =
    Lib_IntVector_Intrinsics_vec256_add64(a11,
      Lib_IntVector_Intrinsics_vec256_mul64(r54, f12));
  a22 =
    Lib_IntVector_Intrinsics_vec256_add64(a21,
      Lib_IntVector_Intrinsics_vec256_mul64(r0, f12));
  a32 =
    Lib_IntVector_Intrinsics_vec256_add64(a31,
      Lib_IntVector_Intrinsics_vec256_mul64(r1, f12));
  a42 =
    Lib_IntVector_Intrinsics_vec256_add64(a41,
      Lib_IntVector_Intrinsics_vec256_mul64(r2, f12));
  a03 =
    Lib_IntVector_Intrinsics_vec256_add64(a02,
      Lib_IntVector_Intrinsics_vec256_mul64(r52, f13));
  a13 =
    Lib_IntVector_Intrinsics_vec256_add64(a12,
      Lib_IntVector_Intrinsics_vec256_mul64(r53, f13));
  a23 =
    Lib_IntVector_Intrinsics_vec256_add64(a22,
      Lib_IntVector_Intrinsics_vec256_mul64(r54, f13));
  a33 =
    Lib_IntVector_Intrinsics_vec256_add64(a32,
      Lib_IntVector_Intrinsics_vec256_mul64(r0, f13));
  a43 =
    Lib_IntVector_Intrinsics_vec256_add64(a42,
      Lib_IntVector_Intrinsics_vec256_mul64(r1, f13));
  a04 =
    Lib_IntVector_Intrinsics_vec256_add64(a03,
      Lib_IntVector_Intrinsics_vec256_mul64(r51, f14));
  a14 =
    Lib_IntVector_Intrinsics_vec256_add64(a13,
      Lib_IntVector_Intrinsics_vec256_mul64(r52, f14));
  a24 =
    Lib_IntVector_Intrinsics_vec256_add64(a23,
      Lib_IntVector_Intrinsics_vec256_mul64(r53, f14));
  a34 =
    Lib_IntVector_Intrinsics_vec256_add64(a33,
      Lib_IntVector_Intrinsics_vec256_mul64(r54, f14));
  a44 =
    Lib_IntVector_Intrinsics_vec256_add64(a43,
      Lib_IntVector_Intrinsics_vec256_mul64(r0, f14));
  t0 = a04;
  t1 = a14;
  t2 = a24;
  t3 = a34;
  t4 = a44;
  mask26 = Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU);
  z0 = Lib_IntVector_Intrinsics_vec256_shift_right64(t0, (u32)26U);
  z1 = Lib_IntVector_Intrinsics_vec256_shift_right64(t3, (u32)26U);
  x0 = Lib_IntVector_Intrinsics_vec256_and(t0, mask26);
  x3 = Lib_IntVector_Intrinsics_vec256_and(t3, mask26);
  x1 = Lib_IntVector_Intrinsics_vec256_add64(t1, z0);
  x4 = Lib_IntVector_Intrinsics_vec256_add64(t4, z1);
  z01 = Lib_IntVector_Intrinsics_vec256_shift_right64(x1, (u32)26U);
  z11 = Lib_IntVector_Intrinsics_vec256_shift_right64(x4, (u32)26U);
  t = Lib_IntVector_Intrinsics_vec256_shift_left64(z11, (u32)2U);
  z12 = Lib_IntVector_Intrinsics_vec256_add64(z11, t);
  x11 = Lib_IntVector_Intrinsics_vec256_and(x1, mask26);
  x41 = Lib_IntVector_Intrinsics_vec256_and(x4, mask26);
  x2 = Lib_IntVector_Intrinsics_vec256_add64(t2, z01);
  x01 = Lib_IntVector_Intrinsics_vec256_add64(x0, z12);
  z02 = Lib_IntVector_Intrinsics_vec256_shift_right64(x2, (u32)26U);
  z13 = Lib_IntVector_Intrinsics_vec256_shift_right64(x01, (u32)26U);
  x21 = Lib_IntVector_Intrinsics_vec256_and(x2, mask26);
  x02 = Lib_IntVector_Intrinsics_vec256_and(x01, mask26);
  x31 = Lib_IntVector_Intrinsics_vec256_add64(x3, z02);
  x12 = Lib_IntVector_Intrinsics_vec256_add64(x11, z13);
  z03 = Lib_IntVector_Intrinsics_vec256_shift_right64(x31, (u32)26U);
  x32 = Lib_IntVector_Intrinsics_vec256_and(x31, mask26);
  x42 = Lib_IntVector_Intrinsics_vec256_add64(x41, z03);
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
  rn_5[0U] = Lib_IntVector_Intrinsics_vec256_smul64(f20, (u64)5U);
  rn_5[1U] = Lib_IntVector_Intrinsics_vec256_smul64(f21, (u64)5U);
  rn_5[2U] = Lib_IntVector_Intrinsics_vec256_smul64(f22, (u64)5U);
  rn_5[3U] = Lib_IntVector_Intrinsics_vec256_smul64(f23, (u64)5U);
  rn_5[4U] = Lib_IntVector_Intrinsics_vec256_smul64(f24, (u64)5U);
}

void Hacl_Poly1305_256_poly1305_update1(Lib_IntVector_Intrinsics_vec256 *ctx, u8 *text)
{
  Lib_IntVector_Intrinsics_vec256 *pre = ctx + (u32)5U;
  Lib_IntVector_Intrinsics_vec256 *acc = ctx;
  Lib_IntVector_Intrinsics_vec256 e[5U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)5U; ++_i)
      e[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  }
  {
    u64 u0 = load64_le(text);
    u64 lo = u0;
    u64 u = load64_le(text + (u32)8U);
    u64 hi = u;
    Lib_IntVector_Intrinsics_vec256 f0 = Lib_IntVector_Intrinsics_vec256_load64(lo);
    Lib_IntVector_Intrinsics_vec256 f1 = Lib_IntVector_Intrinsics_vec256_load64(hi);
    Lib_IntVector_Intrinsics_vec256
    f010 =
      Lib_IntVector_Intrinsics_vec256_and(f0,
        Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
    Lib_IntVector_Intrinsics_vec256
    f110 =
      Lib_IntVector_Intrinsics_vec256_and(Lib_IntVector_Intrinsics_vec256_shift_right64(f0,
          (u32)26U),
        Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
    Lib_IntVector_Intrinsics_vec256
    f20 =
      Lib_IntVector_Intrinsics_vec256_or(Lib_IntVector_Intrinsics_vec256_shift_right64(f0, (u32)52U),
        Lib_IntVector_Intrinsics_vec256_shift_left64(Lib_IntVector_Intrinsics_vec256_and(f1,
            Lib_IntVector_Intrinsics_vec256_load64((u64)0x3fffU)),
          (u32)12U));
    Lib_IntVector_Intrinsics_vec256
    f30 =
      Lib_IntVector_Intrinsics_vec256_and(Lib_IntVector_Intrinsics_vec256_shift_right64(f1,
          (u32)14U),
        Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
    Lib_IntVector_Intrinsics_vec256
    f40 = Lib_IntVector_Intrinsics_vec256_shift_right64(f1, (u32)40U);
    Lib_IntVector_Intrinsics_vec256 f01 = f010;
    Lib_IntVector_Intrinsics_vec256 f111 = f110;
    Lib_IntVector_Intrinsics_vec256 f2 = f20;
    Lib_IntVector_Intrinsics_vec256 f3 = f30;
    Lib_IntVector_Intrinsics_vec256 f41 = f40;
    u64 b;
    Lib_IntVector_Intrinsics_vec256 mask;
    Lib_IntVector_Intrinsics_vec256 f4;
    Lib_IntVector_Intrinsics_vec256 *r;
    Lib_IntVector_Intrinsics_vec256 *r5;
    Lib_IntVector_Intrinsics_vec256 r0;
    Lib_IntVector_Intrinsics_vec256 r1;
    Lib_IntVector_Intrinsics_vec256 r2;
    Lib_IntVector_Intrinsics_vec256 r3;
    Lib_IntVector_Intrinsics_vec256 r4;
    Lib_IntVector_Intrinsics_vec256 r51;
    Lib_IntVector_Intrinsics_vec256 r52;
    Lib_IntVector_Intrinsics_vec256 r53;
    Lib_IntVector_Intrinsics_vec256 r54;
    Lib_IntVector_Intrinsics_vec256 f10;
    Lib_IntVector_Intrinsics_vec256 f11;
    Lib_IntVector_Intrinsics_vec256 f12;
    Lib_IntVector_Intrinsics_vec256 f13;
    Lib_IntVector_Intrinsics_vec256 f14;
    Lib_IntVector_Intrinsics_vec256 a0;
    Lib_IntVector_Intrinsics_vec256 a1;
    Lib_IntVector_Intrinsics_vec256 a2;
    Lib_IntVector_Intrinsics_vec256 a3;
    Lib_IntVector_Intrinsics_vec256 a4;
    Lib_IntVector_Intrinsics_vec256 a01;
    Lib_IntVector_Intrinsics_vec256 a11;
    Lib_IntVector_Intrinsics_vec256 a21;
    Lib_IntVector_Intrinsics_vec256 a31;
    Lib_IntVector_Intrinsics_vec256 a41;
    Lib_IntVector_Intrinsics_vec256 a02;
    Lib_IntVector_Intrinsics_vec256 a12;
    Lib_IntVector_Intrinsics_vec256 a22;
    Lib_IntVector_Intrinsics_vec256 a32;
    Lib_IntVector_Intrinsics_vec256 a42;
    Lib_IntVector_Intrinsics_vec256 a03;
    Lib_IntVector_Intrinsics_vec256 a13;
    Lib_IntVector_Intrinsics_vec256 a23;
    Lib_IntVector_Intrinsics_vec256 a33;
    Lib_IntVector_Intrinsics_vec256 a43;
    Lib_IntVector_Intrinsics_vec256 a04;
    Lib_IntVector_Intrinsics_vec256 a14;
    Lib_IntVector_Intrinsics_vec256 a24;
    Lib_IntVector_Intrinsics_vec256 a34;
    Lib_IntVector_Intrinsics_vec256 a44;
    Lib_IntVector_Intrinsics_vec256 a05;
    Lib_IntVector_Intrinsics_vec256 a15;
    Lib_IntVector_Intrinsics_vec256 a25;
    Lib_IntVector_Intrinsics_vec256 a35;
    Lib_IntVector_Intrinsics_vec256 a45;
    Lib_IntVector_Intrinsics_vec256 a06;
    Lib_IntVector_Intrinsics_vec256 a16;
    Lib_IntVector_Intrinsics_vec256 a26;
    Lib_IntVector_Intrinsics_vec256 a36;
    Lib_IntVector_Intrinsics_vec256 a46;
    Lib_IntVector_Intrinsics_vec256 t0;
    Lib_IntVector_Intrinsics_vec256 t1;
    Lib_IntVector_Intrinsics_vec256 t2;
    Lib_IntVector_Intrinsics_vec256 t3;
    Lib_IntVector_Intrinsics_vec256 t4;
    Lib_IntVector_Intrinsics_vec256 mask26;
    Lib_IntVector_Intrinsics_vec256 z0;
    Lib_IntVector_Intrinsics_vec256 z1;
    Lib_IntVector_Intrinsics_vec256 x0;
    Lib_IntVector_Intrinsics_vec256 x3;
    Lib_IntVector_Intrinsics_vec256 x1;
    Lib_IntVector_Intrinsics_vec256 x4;
    Lib_IntVector_Intrinsics_vec256 z01;
    Lib_IntVector_Intrinsics_vec256 z11;
    Lib_IntVector_Intrinsics_vec256 t;
    Lib_IntVector_Intrinsics_vec256 z12;
    Lib_IntVector_Intrinsics_vec256 x11;
    Lib_IntVector_Intrinsics_vec256 x41;
    Lib_IntVector_Intrinsics_vec256 x2;
    Lib_IntVector_Intrinsics_vec256 x01;
    Lib_IntVector_Intrinsics_vec256 z02;
    Lib_IntVector_Intrinsics_vec256 z13;
    Lib_IntVector_Intrinsics_vec256 x21;
    Lib_IntVector_Intrinsics_vec256 x02;
    Lib_IntVector_Intrinsics_vec256 x31;
    Lib_IntVector_Intrinsics_vec256 x12;
    Lib_IntVector_Intrinsics_vec256 z03;
    Lib_IntVector_Intrinsics_vec256 x32;
    Lib_IntVector_Intrinsics_vec256 x42;
    Lib_IntVector_Intrinsics_vec256 o0;
    Lib_IntVector_Intrinsics_vec256 o1;
    Lib_IntVector_Intrinsics_vec256 o2;
    Lib_IntVector_Intrinsics_vec256 o3;
    Lib_IntVector_Intrinsics_vec256 o4;
    e[0U] = f01;
    e[1U] = f111;
    e[2U] = f2;
    e[3U] = f3;
    e[4U] = f41;
    b = (u64)0x1000000U;
    mask = Lib_IntVector_Intrinsics_vec256_load64(b);
    f4 = e[4U];
    e[4U] = Lib_IntVector_Intrinsics_vec256_or(f4, mask);
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
    a01 = Lib_IntVector_Intrinsics_vec256_add64(a0, f10);
    a11 = Lib_IntVector_Intrinsics_vec256_add64(a1, f11);
    a21 = Lib_IntVector_Intrinsics_vec256_add64(a2, f12);
    a31 = Lib_IntVector_Intrinsics_vec256_add64(a3, f13);
    a41 = Lib_IntVector_Intrinsics_vec256_add64(a4, f14);
    a02 = Lib_IntVector_Intrinsics_vec256_mul64(r0, a01);
    a12 = Lib_IntVector_Intrinsics_vec256_mul64(r1, a01);
    a22 = Lib_IntVector_Intrinsics_vec256_mul64(r2, a01);
    a32 = Lib_IntVector_Intrinsics_vec256_mul64(r3, a01);
    a42 = Lib_IntVector_Intrinsics_vec256_mul64(r4, a01);
    a03 =
      Lib_IntVector_Intrinsics_vec256_add64(a02,
        Lib_IntVector_Intrinsics_vec256_mul64(r54, a11));
    a13 =
      Lib_IntVector_Intrinsics_vec256_add64(a12,
        Lib_IntVector_Intrinsics_vec256_mul64(r0, a11));
    a23 =
      Lib_IntVector_Intrinsics_vec256_add64(a22,
        Lib_IntVector_Intrinsics_vec256_mul64(r1, a11));
    a33 =
      Lib_IntVector_Intrinsics_vec256_add64(a32,
        Lib_IntVector_Intrinsics_vec256_mul64(r2, a11));
    a43 =
      Lib_IntVector_Intrinsics_vec256_add64(a42,
        Lib_IntVector_Intrinsics_vec256_mul64(r3, a11));
    a04 =
      Lib_IntVector_Intrinsics_vec256_add64(a03,
        Lib_IntVector_Intrinsics_vec256_mul64(r53, a21));
    a14 =
      Lib_IntVector_Intrinsics_vec256_add64(a13,
        Lib_IntVector_Intrinsics_vec256_mul64(r54, a21));
    a24 =
      Lib_IntVector_Intrinsics_vec256_add64(a23,
        Lib_IntVector_Intrinsics_vec256_mul64(r0, a21));
    a34 =
      Lib_IntVector_Intrinsics_vec256_add64(a33,
        Lib_IntVector_Intrinsics_vec256_mul64(r1, a21));
    a44 =
      Lib_IntVector_Intrinsics_vec256_add64(a43,
        Lib_IntVector_Intrinsics_vec256_mul64(r2, a21));
    a05 =
      Lib_IntVector_Intrinsics_vec256_add64(a04,
        Lib_IntVector_Intrinsics_vec256_mul64(r52, a31));
    a15 =
      Lib_IntVector_Intrinsics_vec256_add64(a14,
        Lib_IntVector_Intrinsics_vec256_mul64(r53, a31));
    a25 =
      Lib_IntVector_Intrinsics_vec256_add64(a24,
        Lib_IntVector_Intrinsics_vec256_mul64(r54, a31));
    a35 =
      Lib_IntVector_Intrinsics_vec256_add64(a34,
        Lib_IntVector_Intrinsics_vec256_mul64(r0, a31));
    a45 =
      Lib_IntVector_Intrinsics_vec256_add64(a44,
        Lib_IntVector_Intrinsics_vec256_mul64(r1, a31));
    a06 =
      Lib_IntVector_Intrinsics_vec256_add64(a05,
        Lib_IntVector_Intrinsics_vec256_mul64(r51, a41));
    a16 =
      Lib_IntVector_Intrinsics_vec256_add64(a15,
        Lib_IntVector_Intrinsics_vec256_mul64(r52, a41));
    a26 =
      Lib_IntVector_Intrinsics_vec256_add64(a25,
        Lib_IntVector_Intrinsics_vec256_mul64(r53, a41));
    a36 =
      Lib_IntVector_Intrinsics_vec256_add64(a35,
        Lib_IntVector_Intrinsics_vec256_mul64(r54, a41));
    a46 =
      Lib_IntVector_Intrinsics_vec256_add64(a45,
        Lib_IntVector_Intrinsics_vec256_mul64(r0, a41));
    t0 = a06;
    t1 = a16;
    t2 = a26;
    t3 = a36;
    t4 = a46;
    mask26 = Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU);
    z0 = Lib_IntVector_Intrinsics_vec256_shift_right64(t0, (u32)26U);
    z1 = Lib_IntVector_Intrinsics_vec256_shift_right64(t3, (u32)26U);
    x0 = Lib_IntVector_Intrinsics_vec256_and(t0, mask26);
    x3 = Lib_IntVector_Intrinsics_vec256_and(t3, mask26);
    x1 = Lib_IntVector_Intrinsics_vec256_add64(t1, z0);
    x4 = Lib_IntVector_Intrinsics_vec256_add64(t4, z1);
    z01 = Lib_IntVector_Intrinsics_vec256_shift_right64(x1, (u32)26U);
    z11 = Lib_IntVector_Intrinsics_vec256_shift_right64(x4, (u32)26U);
    t = Lib_IntVector_Intrinsics_vec256_shift_left64(z11, (u32)2U);
    z12 = Lib_IntVector_Intrinsics_vec256_add64(z11, t);
    x11 = Lib_IntVector_Intrinsics_vec256_and(x1, mask26);
    x41 = Lib_IntVector_Intrinsics_vec256_and(x4, mask26);
    x2 = Lib_IntVector_Intrinsics_vec256_add64(t2, z01);
    x01 = Lib_IntVector_Intrinsics_vec256_add64(x0, z12);
    z02 = Lib_IntVector_Intrinsics_vec256_shift_right64(x2, (u32)26U);
    z13 = Lib_IntVector_Intrinsics_vec256_shift_right64(x01, (u32)26U);
    x21 = Lib_IntVector_Intrinsics_vec256_and(x2, mask26);
    x02 = Lib_IntVector_Intrinsics_vec256_and(x01, mask26);
    x31 = Lib_IntVector_Intrinsics_vec256_add64(x3, z02);
    x12 = Lib_IntVector_Intrinsics_vec256_add64(x11, z13);
    z03 = Lib_IntVector_Intrinsics_vec256_shift_right64(x31, (u32)26U);
    x32 = Lib_IntVector_Intrinsics_vec256_and(x31, mask26);
    x42 = Lib_IntVector_Intrinsics_vec256_add64(x41, z03);
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

void Hacl_Poly1305_256_poly1305_update(Lib_IntVector_Intrinsics_vec256 *ctx, u32 len, u8 *text)
{
  Lib_IntVector_Intrinsics_vec256 *pre = ctx + (u32)5U;
  Lib_IntVector_Intrinsics_vec256 *acc = ctx;
  u32 sz_block = (u32)64U;
  u32 len0 = len / sz_block * sz_block;
  u8 *t0 = text;
  u32 len1;
  u8 *t10;
  u32 nb0;
  u32 rem;
  if (len0 > (u32)0U)
  {
    u32 bs = (u32)64U;
    u8 *text0 = t0;
    Hacl_Impl_Poly1305_Field32xN_256_load_acc4(acc, text0);
    {
      u32 len10 = len0 - bs;
      u8 *text1 = t0 + bs;
      u32 nb = len10 / bs;
      {
        u32 i;
        for (i = (u32)0U; i < nb; i++)
        {
          u8 *block = text1 + i * bs;
          Lib_IntVector_Intrinsics_vec256 e[5U];
          {
            u32 _i;
            for (_i = 0U; _i < (u32)5U; ++_i)
              e[_i] = Lib_IntVector_Intrinsics_vec256_zero;
          }
          {
            Lib_IntVector_Intrinsics_vec256 lo = Lib_IntVector_Intrinsics_vec256_load_le(block);
            Lib_IntVector_Intrinsics_vec256
            hi = Lib_IntVector_Intrinsics_vec256_load_le(block + (u32)32U);
            Lib_IntVector_Intrinsics_vec256
            mask260 = Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU);
            Lib_IntVector_Intrinsics_vec256
            m0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(lo, hi);
            Lib_IntVector_Intrinsics_vec256
            m1 = Lib_IntVector_Intrinsics_vec256_interleave_high128(lo, hi);
            Lib_IntVector_Intrinsics_vec256
            m2 = Lib_IntVector_Intrinsics_vec256_shift_right(m0, (u32)48U);
            Lib_IntVector_Intrinsics_vec256
            m3 = Lib_IntVector_Intrinsics_vec256_shift_right(m1, (u32)48U);
            Lib_IntVector_Intrinsics_vec256
            m4 = Lib_IntVector_Intrinsics_vec256_interleave_high64(m0, m1);
            Lib_IntVector_Intrinsics_vec256
            t010 = Lib_IntVector_Intrinsics_vec256_interleave_low64(m0, m1);
            Lib_IntVector_Intrinsics_vec256
            t30 = Lib_IntVector_Intrinsics_vec256_interleave_low64(m2, m3);
            Lib_IntVector_Intrinsics_vec256
            t20 = Lib_IntVector_Intrinsics_vec256_shift_right64(t30, (u32)4U);
            Lib_IntVector_Intrinsics_vec256 o20 = Lib_IntVector_Intrinsics_vec256_and(t20, mask260);
            Lib_IntVector_Intrinsics_vec256
            t11 = Lib_IntVector_Intrinsics_vec256_shift_right64(t010, (u32)26U);
            Lib_IntVector_Intrinsics_vec256 o10 = Lib_IntVector_Intrinsics_vec256_and(t11, mask260);
            Lib_IntVector_Intrinsics_vec256 o5 = Lib_IntVector_Intrinsics_vec256_and(t010, mask260);
            Lib_IntVector_Intrinsics_vec256
            t31 = Lib_IntVector_Intrinsics_vec256_shift_right64(t30, (u32)30U);
            Lib_IntVector_Intrinsics_vec256 o30 = Lib_IntVector_Intrinsics_vec256_and(t31, mask260);
            Lib_IntVector_Intrinsics_vec256
            o40 = Lib_IntVector_Intrinsics_vec256_shift_right64(m4, (u32)40U);
            Lib_IntVector_Intrinsics_vec256 o00 = o5;
            Lib_IntVector_Intrinsics_vec256 o11 = o10;
            Lib_IntVector_Intrinsics_vec256 o21 = o20;
            Lib_IntVector_Intrinsics_vec256 o31 = o30;
            Lib_IntVector_Intrinsics_vec256 o41 = o40;
            e[0U] = o00;
            e[1U] = o11;
            e[2U] = o21;
            e[3U] = o31;
            e[4U] = o41;
            {
              u64 b = (u64)0x1000000U;
              Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_load64(b);
              Lib_IntVector_Intrinsics_vec256 f4 = e[4U];
              e[4U] = Lib_IntVector_Intrinsics_vec256_or(f4, mask);
              {
                Lib_IntVector_Intrinsics_vec256 *rn = pre + (u32)10U;
                Lib_IntVector_Intrinsics_vec256 *rn5 = pre + (u32)15U;
                Lib_IntVector_Intrinsics_vec256 r0 = rn[0U];
                Lib_IntVector_Intrinsics_vec256 r1 = rn[1U];
                Lib_IntVector_Intrinsics_vec256 r2 = rn[2U];
                Lib_IntVector_Intrinsics_vec256 r3 = rn[3U];
                Lib_IntVector_Intrinsics_vec256 r4 = rn[4U];
                Lib_IntVector_Intrinsics_vec256 r51 = rn5[1U];
                Lib_IntVector_Intrinsics_vec256 r52 = rn5[2U];
                Lib_IntVector_Intrinsics_vec256 r53 = rn5[3U];
                Lib_IntVector_Intrinsics_vec256 r54 = rn5[4U];
                Lib_IntVector_Intrinsics_vec256 f10 = acc[0U];
                Lib_IntVector_Intrinsics_vec256 f110 = acc[1U];
                Lib_IntVector_Intrinsics_vec256 f120 = acc[2U];
                Lib_IntVector_Intrinsics_vec256 f130 = acc[3U];
                Lib_IntVector_Intrinsics_vec256 f140 = acc[4U];
                Lib_IntVector_Intrinsics_vec256 a0 = Lib_IntVector_Intrinsics_vec256_mul64(r0, f10);
                Lib_IntVector_Intrinsics_vec256 a1 = Lib_IntVector_Intrinsics_vec256_mul64(r1, f10);
                Lib_IntVector_Intrinsics_vec256 a2 = Lib_IntVector_Intrinsics_vec256_mul64(r2, f10);
                Lib_IntVector_Intrinsics_vec256 a3 = Lib_IntVector_Intrinsics_vec256_mul64(r3, f10);
                Lib_IntVector_Intrinsics_vec256 a4 = Lib_IntVector_Intrinsics_vec256_mul64(r4, f10);
                Lib_IntVector_Intrinsics_vec256
                a01 =
                  Lib_IntVector_Intrinsics_vec256_add64(a0,
                    Lib_IntVector_Intrinsics_vec256_mul64(r54, f110));
                Lib_IntVector_Intrinsics_vec256
                a11 =
                  Lib_IntVector_Intrinsics_vec256_add64(a1,
                    Lib_IntVector_Intrinsics_vec256_mul64(r0, f110));
                Lib_IntVector_Intrinsics_vec256
                a21 =
                  Lib_IntVector_Intrinsics_vec256_add64(a2,
                    Lib_IntVector_Intrinsics_vec256_mul64(r1, f110));
                Lib_IntVector_Intrinsics_vec256
                a31 =
                  Lib_IntVector_Intrinsics_vec256_add64(a3,
                    Lib_IntVector_Intrinsics_vec256_mul64(r2, f110));
                Lib_IntVector_Intrinsics_vec256
                a41 =
                  Lib_IntVector_Intrinsics_vec256_add64(a4,
                    Lib_IntVector_Intrinsics_vec256_mul64(r3, f110));
                Lib_IntVector_Intrinsics_vec256
                a02 =
                  Lib_IntVector_Intrinsics_vec256_add64(a01,
                    Lib_IntVector_Intrinsics_vec256_mul64(r53, f120));
                Lib_IntVector_Intrinsics_vec256
                a12 =
                  Lib_IntVector_Intrinsics_vec256_add64(a11,
                    Lib_IntVector_Intrinsics_vec256_mul64(r54, f120));
                Lib_IntVector_Intrinsics_vec256
                a22 =
                  Lib_IntVector_Intrinsics_vec256_add64(a21,
                    Lib_IntVector_Intrinsics_vec256_mul64(r0, f120));
                Lib_IntVector_Intrinsics_vec256
                a32 =
                  Lib_IntVector_Intrinsics_vec256_add64(a31,
                    Lib_IntVector_Intrinsics_vec256_mul64(r1, f120));
                Lib_IntVector_Intrinsics_vec256
                a42 =
                  Lib_IntVector_Intrinsics_vec256_add64(a41,
                    Lib_IntVector_Intrinsics_vec256_mul64(r2, f120));
                Lib_IntVector_Intrinsics_vec256
                a03 =
                  Lib_IntVector_Intrinsics_vec256_add64(a02,
                    Lib_IntVector_Intrinsics_vec256_mul64(r52, f130));
                Lib_IntVector_Intrinsics_vec256
                a13 =
                  Lib_IntVector_Intrinsics_vec256_add64(a12,
                    Lib_IntVector_Intrinsics_vec256_mul64(r53, f130));
                Lib_IntVector_Intrinsics_vec256
                a23 =
                  Lib_IntVector_Intrinsics_vec256_add64(a22,
                    Lib_IntVector_Intrinsics_vec256_mul64(r54, f130));
                Lib_IntVector_Intrinsics_vec256
                a33 =
                  Lib_IntVector_Intrinsics_vec256_add64(a32,
                    Lib_IntVector_Intrinsics_vec256_mul64(r0, f130));
                Lib_IntVector_Intrinsics_vec256
                a43 =
                  Lib_IntVector_Intrinsics_vec256_add64(a42,
                    Lib_IntVector_Intrinsics_vec256_mul64(r1, f130));
                Lib_IntVector_Intrinsics_vec256
                a04 =
                  Lib_IntVector_Intrinsics_vec256_add64(a03,
                    Lib_IntVector_Intrinsics_vec256_mul64(r51, f140));
                Lib_IntVector_Intrinsics_vec256
                a14 =
                  Lib_IntVector_Intrinsics_vec256_add64(a13,
                    Lib_IntVector_Intrinsics_vec256_mul64(r52, f140));
                Lib_IntVector_Intrinsics_vec256
                a24 =
                  Lib_IntVector_Intrinsics_vec256_add64(a23,
                    Lib_IntVector_Intrinsics_vec256_mul64(r53, f140));
                Lib_IntVector_Intrinsics_vec256
                a34 =
                  Lib_IntVector_Intrinsics_vec256_add64(a33,
                    Lib_IntVector_Intrinsics_vec256_mul64(r54, f140));
                Lib_IntVector_Intrinsics_vec256
                a44 =
                  Lib_IntVector_Intrinsics_vec256_add64(a43,
                    Lib_IntVector_Intrinsics_vec256_mul64(r0, f140));
                Lib_IntVector_Intrinsics_vec256 t01 = a04;
                Lib_IntVector_Intrinsics_vec256 t1 = a14;
                Lib_IntVector_Intrinsics_vec256 t2 = a24;
                Lib_IntVector_Intrinsics_vec256 t3 = a34;
                Lib_IntVector_Intrinsics_vec256 t4 = a44;
                Lib_IntVector_Intrinsics_vec256
                mask26 = Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU);
                Lib_IntVector_Intrinsics_vec256
                z0 = Lib_IntVector_Intrinsics_vec256_shift_right64(t01, (u32)26U);
                Lib_IntVector_Intrinsics_vec256
                z1 = Lib_IntVector_Intrinsics_vec256_shift_right64(t3, (u32)26U);
                Lib_IntVector_Intrinsics_vec256
                x0 = Lib_IntVector_Intrinsics_vec256_and(t01, mask26);
                Lib_IntVector_Intrinsics_vec256
                x3 = Lib_IntVector_Intrinsics_vec256_and(t3, mask26);
                Lib_IntVector_Intrinsics_vec256 x1 = Lib_IntVector_Intrinsics_vec256_add64(t1, z0);
                Lib_IntVector_Intrinsics_vec256 x4 = Lib_IntVector_Intrinsics_vec256_add64(t4, z1);
                Lib_IntVector_Intrinsics_vec256
                z01 = Lib_IntVector_Intrinsics_vec256_shift_right64(x1, (u32)26U);
                Lib_IntVector_Intrinsics_vec256
                z11 = Lib_IntVector_Intrinsics_vec256_shift_right64(x4, (u32)26U);
                Lib_IntVector_Intrinsics_vec256
                t = Lib_IntVector_Intrinsics_vec256_shift_left64(z11, (u32)2U);
                Lib_IntVector_Intrinsics_vec256 z12 = Lib_IntVector_Intrinsics_vec256_add64(z11, t);
                Lib_IntVector_Intrinsics_vec256
                x11 = Lib_IntVector_Intrinsics_vec256_and(x1, mask26);
                Lib_IntVector_Intrinsics_vec256
                x41 = Lib_IntVector_Intrinsics_vec256_and(x4, mask26);
                Lib_IntVector_Intrinsics_vec256 x2 = Lib_IntVector_Intrinsics_vec256_add64(t2, z01);
                Lib_IntVector_Intrinsics_vec256
                x01 = Lib_IntVector_Intrinsics_vec256_add64(x0, z12);
                Lib_IntVector_Intrinsics_vec256
                z02 = Lib_IntVector_Intrinsics_vec256_shift_right64(x2, (u32)26U);
                Lib_IntVector_Intrinsics_vec256
                z13 = Lib_IntVector_Intrinsics_vec256_shift_right64(x01, (u32)26U);
                Lib_IntVector_Intrinsics_vec256
                x21 = Lib_IntVector_Intrinsics_vec256_and(x2, mask26);
                Lib_IntVector_Intrinsics_vec256
                x02 = Lib_IntVector_Intrinsics_vec256_and(x01, mask26);
                Lib_IntVector_Intrinsics_vec256
                x31 = Lib_IntVector_Intrinsics_vec256_add64(x3, z02);
                Lib_IntVector_Intrinsics_vec256
                x12 = Lib_IntVector_Intrinsics_vec256_add64(x11, z13);
                Lib_IntVector_Intrinsics_vec256
                z03 = Lib_IntVector_Intrinsics_vec256_shift_right64(x31, (u32)26U);
                Lib_IntVector_Intrinsics_vec256
                x32 = Lib_IntVector_Intrinsics_vec256_and(x31, mask26);
                Lib_IntVector_Intrinsics_vec256
                x42 = Lib_IntVector_Intrinsics_vec256_add64(x41, z03);
                Lib_IntVector_Intrinsics_vec256 o01 = x02;
                Lib_IntVector_Intrinsics_vec256 o12 = x12;
                Lib_IntVector_Intrinsics_vec256 o22 = x21;
                Lib_IntVector_Intrinsics_vec256 o32 = x32;
                Lib_IntVector_Intrinsics_vec256 o42 = x42;
                acc[0U] = o01;
                acc[1U] = o12;
                acc[2U] = o22;
                acc[3U] = o32;
                acc[4U] = o42;
                {
                  Lib_IntVector_Intrinsics_vec256 f100 = acc[0U];
                  Lib_IntVector_Intrinsics_vec256 f11 = acc[1U];
                  Lib_IntVector_Intrinsics_vec256 f12 = acc[2U];
                  Lib_IntVector_Intrinsics_vec256 f13 = acc[3U];
                  Lib_IntVector_Intrinsics_vec256 f14 = acc[4U];
                  Lib_IntVector_Intrinsics_vec256 f20 = e[0U];
                  Lib_IntVector_Intrinsics_vec256 f21 = e[1U];
                  Lib_IntVector_Intrinsics_vec256 f22 = e[2U];
                  Lib_IntVector_Intrinsics_vec256 f23 = e[3U];
                  Lib_IntVector_Intrinsics_vec256 f24 = e[4U];
                  Lib_IntVector_Intrinsics_vec256
                  o0 = Lib_IntVector_Intrinsics_vec256_add64(f100, f20);
                  Lib_IntVector_Intrinsics_vec256
                  o1 = Lib_IntVector_Intrinsics_vec256_add64(f11, f21);
                  Lib_IntVector_Intrinsics_vec256
                  o2 = Lib_IntVector_Intrinsics_vec256_add64(f12, f22);
                  Lib_IntVector_Intrinsics_vec256
                  o3 = Lib_IntVector_Intrinsics_vec256_add64(f13, f23);
                  Lib_IntVector_Intrinsics_vec256
                  o4 = Lib_IntVector_Intrinsics_vec256_add64(f14, f24);
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
      Hacl_Impl_Poly1305_Field32xN_256_fmul_r4_normalize(acc, pre);
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
      Lib_IntVector_Intrinsics_vec256 e[5U];
      {
        u32 _i;
        for (_i = 0U; _i < (u32)5U; ++_i)
          e[_i] = Lib_IntVector_Intrinsics_vec256_zero;
      }
      {
        u64 u0 = load64_le(block);
        u64 lo = u0;
        u64 u = load64_le(block + (u32)8U);
        u64 hi = u;
        Lib_IntVector_Intrinsics_vec256 f0 = Lib_IntVector_Intrinsics_vec256_load64(lo);
        Lib_IntVector_Intrinsics_vec256 f1 = Lib_IntVector_Intrinsics_vec256_load64(hi);
        Lib_IntVector_Intrinsics_vec256
        f010 =
          Lib_IntVector_Intrinsics_vec256_and(f0,
            Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
        Lib_IntVector_Intrinsics_vec256
        f110 =
          Lib_IntVector_Intrinsics_vec256_and(Lib_IntVector_Intrinsics_vec256_shift_right64(f0,
              (u32)26U),
            Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
        Lib_IntVector_Intrinsics_vec256
        f20 =
          Lib_IntVector_Intrinsics_vec256_or(Lib_IntVector_Intrinsics_vec256_shift_right64(f0,
              (u32)52U),
            Lib_IntVector_Intrinsics_vec256_shift_left64(Lib_IntVector_Intrinsics_vec256_and(f1,
                Lib_IntVector_Intrinsics_vec256_load64((u64)0x3fffU)),
              (u32)12U));
        Lib_IntVector_Intrinsics_vec256
        f30 =
          Lib_IntVector_Intrinsics_vec256_and(Lib_IntVector_Intrinsics_vec256_shift_right64(f1,
              (u32)14U),
            Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
        Lib_IntVector_Intrinsics_vec256
        f40 = Lib_IntVector_Intrinsics_vec256_shift_right64(f1, (u32)40U);
        Lib_IntVector_Intrinsics_vec256 f01 = f010;
        Lib_IntVector_Intrinsics_vec256 f111 = f110;
        Lib_IntVector_Intrinsics_vec256 f2 = f20;
        Lib_IntVector_Intrinsics_vec256 f3 = f30;
        Lib_IntVector_Intrinsics_vec256 f41 = f40;
        e[0U] = f01;
        e[1U] = f111;
        e[2U] = f2;
        e[3U] = f3;
        e[4U] = f41;
        {
          u64 b = (u64)0x1000000U;
          Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_load64(b);
          Lib_IntVector_Intrinsics_vec256 f4 = e[4U];
          e[4U] = Lib_IntVector_Intrinsics_vec256_or(f4, mask);
          {
            Lib_IntVector_Intrinsics_vec256 *r = pre;
            Lib_IntVector_Intrinsics_vec256 *r5 = pre + (u32)5U;
            Lib_IntVector_Intrinsics_vec256 r0 = r[0U];
            Lib_IntVector_Intrinsics_vec256 r1 = r[1U];
            Lib_IntVector_Intrinsics_vec256 r2 = r[2U];
            Lib_IntVector_Intrinsics_vec256 r3 = r[3U];
            Lib_IntVector_Intrinsics_vec256 r4 = r[4U];
            Lib_IntVector_Intrinsics_vec256 r51 = r5[1U];
            Lib_IntVector_Intrinsics_vec256 r52 = r5[2U];
            Lib_IntVector_Intrinsics_vec256 r53 = r5[3U];
            Lib_IntVector_Intrinsics_vec256 r54 = r5[4U];
            Lib_IntVector_Intrinsics_vec256 f10 = e[0U];
            Lib_IntVector_Intrinsics_vec256 f11 = e[1U];
            Lib_IntVector_Intrinsics_vec256 f12 = e[2U];
            Lib_IntVector_Intrinsics_vec256 f13 = e[3U];
            Lib_IntVector_Intrinsics_vec256 f14 = e[4U];
            Lib_IntVector_Intrinsics_vec256 a0 = acc[0U];
            Lib_IntVector_Intrinsics_vec256 a1 = acc[1U];
            Lib_IntVector_Intrinsics_vec256 a2 = acc[2U];
            Lib_IntVector_Intrinsics_vec256 a3 = acc[3U];
            Lib_IntVector_Intrinsics_vec256 a4 = acc[4U];
            Lib_IntVector_Intrinsics_vec256 a01 = Lib_IntVector_Intrinsics_vec256_add64(a0, f10);
            Lib_IntVector_Intrinsics_vec256 a11 = Lib_IntVector_Intrinsics_vec256_add64(a1, f11);
            Lib_IntVector_Intrinsics_vec256 a21 = Lib_IntVector_Intrinsics_vec256_add64(a2, f12);
            Lib_IntVector_Intrinsics_vec256 a31 = Lib_IntVector_Intrinsics_vec256_add64(a3, f13);
            Lib_IntVector_Intrinsics_vec256 a41 = Lib_IntVector_Intrinsics_vec256_add64(a4, f14);
            Lib_IntVector_Intrinsics_vec256 a02 = Lib_IntVector_Intrinsics_vec256_mul64(r0, a01);
            Lib_IntVector_Intrinsics_vec256 a12 = Lib_IntVector_Intrinsics_vec256_mul64(r1, a01);
            Lib_IntVector_Intrinsics_vec256 a22 = Lib_IntVector_Intrinsics_vec256_mul64(r2, a01);
            Lib_IntVector_Intrinsics_vec256 a32 = Lib_IntVector_Intrinsics_vec256_mul64(r3, a01);
            Lib_IntVector_Intrinsics_vec256 a42 = Lib_IntVector_Intrinsics_vec256_mul64(r4, a01);
            Lib_IntVector_Intrinsics_vec256
            a03 =
              Lib_IntVector_Intrinsics_vec256_add64(a02,
                Lib_IntVector_Intrinsics_vec256_mul64(r54, a11));
            Lib_IntVector_Intrinsics_vec256
            a13 =
              Lib_IntVector_Intrinsics_vec256_add64(a12,
                Lib_IntVector_Intrinsics_vec256_mul64(r0, a11));
            Lib_IntVector_Intrinsics_vec256
            a23 =
              Lib_IntVector_Intrinsics_vec256_add64(a22,
                Lib_IntVector_Intrinsics_vec256_mul64(r1, a11));
            Lib_IntVector_Intrinsics_vec256
            a33 =
              Lib_IntVector_Intrinsics_vec256_add64(a32,
                Lib_IntVector_Intrinsics_vec256_mul64(r2, a11));
            Lib_IntVector_Intrinsics_vec256
            a43 =
              Lib_IntVector_Intrinsics_vec256_add64(a42,
                Lib_IntVector_Intrinsics_vec256_mul64(r3, a11));
            Lib_IntVector_Intrinsics_vec256
            a04 =
              Lib_IntVector_Intrinsics_vec256_add64(a03,
                Lib_IntVector_Intrinsics_vec256_mul64(r53, a21));
            Lib_IntVector_Intrinsics_vec256
            a14 =
              Lib_IntVector_Intrinsics_vec256_add64(a13,
                Lib_IntVector_Intrinsics_vec256_mul64(r54, a21));
            Lib_IntVector_Intrinsics_vec256
            a24 =
              Lib_IntVector_Intrinsics_vec256_add64(a23,
                Lib_IntVector_Intrinsics_vec256_mul64(r0, a21));
            Lib_IntVector_Intrinsics_vec256
            a34 =
              Lib_IntVector_Intrinsics_vec256_add64(a33,
                Lib_IntVector_Intrinsics_vec256_mul64(r1, a21));
            Lib_IntVector_Intrinsics_vec256
            a44 =
              Lib_IntVector_Intrinsics_vec256_add64(a43,
                Lib_IntVector_Intrinsics_vec256_mul64(r2, a21));
            Lib_IntVector_Intrinsics_vec256
            a05 =
              Lib_IntVector_Intrinsics_vec256_add64(a04,
                Lib_IntVector_Intrinsics_vec256_mul64(r52, a31));
            Lib_IntVector_Intrinsics_vec256
            a15 =
              Lib_IntVector_Intrinsics_vec256_add64(a14,
                Lib_IntVector_Intrinsics_vec256_mul64(r53, a31));
            Lib_IntVector_Intrinsics_vec256
            a25 =
              Lib_IntVector_Intrinsics_vec256_add64(a24,
                Lib_IntVector_Intrinsics_vec256_mul64(r54, a31));
            Lib_IntVector_Intrinsics_vec256
            a35 =
              Lib_IntVector_Intrinsics_vec256_add64(a34,
                Lib_IntVector_Intrinsics_vec256_mul64(r0, a31));
            Lib_IntVector_Intrinsics_vec256
            a45 =
              Lib_IntVector_Intrinsics_vec256_add64(a44,
                Lib_IntVector_Intrinsics_vec256_mul64(r1, a31));
            Lib_IntVector_Intrinsics_vec256
            a06 =
              Lib_IntVector_Intrinsics_vec256_add64(a05,
                Lib_IntVector_Intrinsics_vec256_mul64(r51, a41));
            Lib_IntVector_Intrinsics_vec256
            a16 =
              Lib_IntVector_Intrinsics_vec256_add64(a15,
                Lib_IntVector_Intrinsics_vec256_mul64(r52, a41));
            Lib_IntVector_Intrinsics_vec256
            a26 =
              Lib_IntVector_Intrinsics_vec256_add64(a25,
                Lib_IntVector_Intrinsics_vec256_mul64(r53, a41));
            Lib_IntVector_Intrinsics_vec256
            a36 =
              Lib_IntVector_Intrinsics_vec256_add64(a35,
                Lib_IntVector_Intrinsics_vec256_mul64(r54, a41));
            Lib_IntVector_Intrinsics_vec256
            a46 =
              Lib_IntVector_Intrinsics_vec256_add64(a45,
                Lib_IntVector_Intrinsics_vec256_mul64(r0, a41));
            Lib_IntVector_Intrinsics_vec256 t01 = a06;
            Lib_IntVector_Intrinsics_vec256 t11 = a16;
            Lib_IntVector_Intrinsics_vec256 t2 = a26;
            Lib_IntVector_Intrinsics_vec256 t3 = a36;
            Lib_IntVector_Intrinsics_vec256 t4 = a46;
            Lib_IntVector_Intrinsics_vec256
            mask26 = Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU);
            Lib_IntVector_Intrinsics_vec256
            z0 = Lib_IntVector_Intrinsics_vec256_shift_right64(t01, (u32)26U);
            Lib_IntVector_Intrinsics_vec256
            z1 = Lib_IntVector_Intrinsics_vec256_shift_right64(t3, (u32)26U);
            Lib_IntVector_Intrinsics_vec256 x0 = Lib_IntVector_Intrinsics_vec256_and(t01, mask26);
            Lib_IntVector_Intrinsics_vec256 x3 = Lib_IntVector_Intrinsics_vec256_and(t3, mask26);
            Lib_IntVector_Intrinsics_vec256 x1 = Lib_IntVector_Intrinsics_vec256_add64(t11, z0);
            Lib_IntVector_Intrinsics_vec256 x4 = Lib_IntVector_Intrinsics_vec256_add64(t4, z1);
            Lib_IntVector_Intrinsics_vec256
            z01 = Lib_IntVector_Intrinsics_vec256_shift_right64(x1, (u32)26U);
            Lib_IntVector_Intrinsics_vec256
            z11 = Lib_IntVector_Intrinsics_vec256_shift_right64(x4, (u32)26U);
            Lib_IntVector_Intrinsics_vec256
            t = Lib_IntVector_Intrinsics_vec256_shift_left64(z11, (u32)2U);
            Lib_IntVector_Intrinsics_vec256 z12 = Lib_IntVector_Intrinsics_vec256_add64(z11, t);
            Lib_IntVector_Intrinsics_vec256 x11 = Lib_IntVector_Intrinsics_vec256_and(x1, mask26);
            Lib_IntVector_Intrinsics_vec256 x41 = Lib_IntVector_Intrinsics_vec256_and(x4, mask26);
            Lib_IntVector_Intrinsics_vec256 x2 = Lib_IntVector_Intrinsics_vec256_add64(t2, z01);
            Lib_IntVector_Intrinsics_vec256 x01 = Lib_IntVector_Intrinsics_vec256_add64(x0, z12);
            Lib_IntVector_Intrinsics_vec256
            z02 = Lib_IntVector_Intrinsics_vec256_shift_right64(x2, (u32)26U);
            Lib_IntVector_Intrinsics_vec256
            z13 = Lib_IntVector_Intrinsics_vec256_shift_right64(x01, (u32)26U);
            Lib_IntVector_Intrinsics_vec256 x21 = Lib_IntVector_Intrinsics_vec256_and(x2, mask26);
            Lib_IntVector_Intrinsics_vec256 x02 = Lib_IntVector_Intrinsics_vec256_and(x01, mask26);
            Lib_IntVector_Intrinsics_vec256 x31 = Lib_IntVector_Intrinsics_vec256_add64(x3, z02);
            Lib_IntVector_Intrinsics_vec256 x12 = Lib_IntVector_Intrinsics_vec256_add64(x11, z13);
            Lib_IntVector_Intrinsics_vec256
            z03 = Lib_IntVector_Intrinsics_vec256_shift_right64(x31, (u32)26U);
            Lib_IntVector_Intrinsics_vec256 x32 = Lib_IntVector_Intrinsics_vec256_and(x31, mask26);
            Lib_IntVector_Intrinsics_vec256 x42 = Lib_IntVector_Intrinsics_vec256_add64(x41, z03);
            Lib_IntVector_Intrinsics_vec256 o0 = x02;
            Lib_IntVector_Intrinsics_vec256 o1 = x12;
            Lib_IntVector_Intrinsics_vec256 o2 = x21;
            Lib_IntVector_Intrinsics_vec256 o3 = x32;
            Lib_IntVector_Intrinsics_vec256 o4 = x42;
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
    Lib_IntVector_Intrinsics_vec256 e[5U];
    {
      u32 _i;
      for (_i = 0U; _i < (u32)5U; ++_i)
        e[_i] = Lib_IntVector_Intrinsics_vec256_zero;
    }
    {
      u8 tmp[16U] = { 0U };
      u64 u0;
      u64 lo;
      u64 u;
      u64 hi;
      Lib_IntVector_Intrinsics_vec256 f0;
      Lib_IntVector_Intrinsics_vec256 f1;
      Lib_IntVector_Intrinsics_vec256 f010;
      Lib_IntVector_Intrinsics_vec256 f110;
      Lib_IntVector_Intrinsics_vec256 f20;
      Lib_IntVector_Intrinsics_vec256 f30;
      Lib_IntVector_Intrinsics_vec256 f40;
      Lib_IntVector_Intrinsics_vec256 f01;
      Lib_IntVector_Intrinsics_vec256 f111;
      Lib_IntVector_Intrinsics_vec256 f2;
      Lib_IntVector_Intrinsics_vec256 f3;
      Lib_IntVector_Intrinsics_vec256 f4;
      u64 b;
      Lib_IntVector_Intrinsics_vec256 mask;
      Lib_IntVector_Intrinsics_vec256 fi;
      Lib_IntVector_Intrinsics_vec256 *r;
      Lib_IntVector_Intrinsics_vec256 *r5;
      Lib_IntVector_Intrinsics_vec256 r0;
      Lib_IntVector_Intrinsics_vec256 r1;
      Lib_IntVector_Intrinsics_vec256 r2;
      Lib_IntVector_Intrinsics_vec256 r3;
      Lib_IntVector_Intrinsics_vec256 r4;
      Lib_IntVector_Intrinsics_vec256 r51;
      Lib_IntVector_Intrinsics_vec256 r52;
      Lib_IntVector_Intrinsics_vec256 r53;
      Lib_IntVector_Intrinsics_vec256 r54;
      Lib_IntVector_Intrinsics_vec256 f10;
      Lib_IntVector_Intrinsics_vec256 f11;
      Lib_IntVector_Intrinsics_vec256 f12;
      Lib_IntVector_Intrinsics_vec256 f13;
      Lib_IntVector_Intrinsics_vec256 f14;
      Lib_IntVector_Intrinsics_vec256 a0;
      Lib_IntVector_Intrinsics_vec256 a1;
      Lib_IntVector_Intrinsics_vec256 a2;
      Lib_IntVector_Intrinsics_vec256 a3;
      Lib_IntVector_Intrinsics_vec256 a4;
      Lib_IntVector_Intrinsics_vec256 a01;
      Lib_IntVector_Intrinsics_vec256 a11;
      Lib_IntVector_Intrinsics_vec256 a21;
      Lib_IntVector_Intrinsics_vec256 a31;
      Lib_IntVector_Intrinsics_vec256 a41;
      Lib_IntVector_Intrinsics_vec256 a02;
      Lib_IntVector_Intrinsics_vec256 a12;
      Lib_IntVector_Intrinsics_vec256 a22;
      Lib_IntVector_Intrinsics_vec256 a32;
      Lib_IntVector_Intrinsics_vec256 a42;
      Lib_IntVector_Intrinsics_vec256 a03;
      Lib_IntVector_Intrinsics_vec256 a13;
      Lib_IntVector_Intrinsics_vec256 a23;
      Lib_IntVector_Intrinsics_vec256 a33;
      Lib_IntVector_Intrinsics_vec256 a43;
      Lib_IntVector_Intrinsics_vec256 a04;
      Lib_IntVector_Intrinsics_vec256 a14;
      Lib_IntVector_Intrinsics_vec256 a24;
      Lib_IntVector_Intrinsics_vec256 a34;
      Lib_IntVector_Intrinsics_vec256 a44;
      Lib_IntVector_Intrinsics_vec256 a05;
      Lib_IntVector_Intrinsics_vec256 a15;
      Lib_IntVector_Intrinsics_vec256 a25;
      Lib_IntVector_Intrinsics_vec256 a35;
      Lib_IntVector_Intrinsics_vec256 a45;
      Lib_IntVector_Intrinsics_vec256 a06;
      Lib_IntVector_Intrinsics_vec256 a16;
      Lib_IntVector_Intrinsics_vec256 a26;
      Lib_IntVector_Intrinsics_vec256 a36;
      Lib_IntVector_Intrinsics_vec256 a46;
      Lib_IntVector_Intrinsics_vec256 t01;
      Lib_IntVector_Intrinsics_vec256 t11;
      Lib_IntVector_Intrinsics_vec256 t2;
      Lib_IntVector_Intrinsics_vec256 t3;
      Lib_IntVector_Intrinsics_vec256 t4;
      Lib_IntVector_Intrinsics_vec256 mask26;
      Lib_IntVector_Intrinsics_vec256 z0;
      Lib_IntVector_Intrinsics_vec256 z1;
      Lib_IntVector_Intrinsics_vec256 x0;
      Lib_IntVector_Intrinsics_vec256 x3;
      Lib_IntVector_Intrinsics_vec256 x1;
      Lib_IntVector_Intrinsics_vec256 x4;
      Lib_IntVector_Intrinsics_vec256 z01;
      Lib_IntVector_Intrinsics_vec256 z11;
      Lib_IntVector_Intrinsics_vec256 t;
      Lib_IntVector_Intrinsics_vec256 z12;
      Lib_IntVector_Intrinsics_vec256 x11;
      Lib_IntVector_Intrinsics_vec256 x41;
      Lib_IntVector_Intrinsics_vec256 x2;
      Lib_IntVector_Intrinsics_vec256 x01;
      Lib_IntVector_Intrinsics_vec256 z02;
      Lib_IntVector_Intrinsics_vec256 z13;
      Lib_IntVector_Intrinsics_vec256 x21;
      Lib_IntVector_Intrinsics_vec256 x02;
      Lib_IntVector_Intrinsics_vec256 x31;
      Lib_IntVector_Intrinsics_vec256 x12;
      Lib_IntVector_Intrinsics_vec256 z03;
      Lib_IntVector_Intrinsics_vec256 x32;
      Lib_IntVector_Intrinsics_vec256 x42;
      Lib_IntVector_Intrinsics_vec256 o0;
      Lib_IntVector_Intrinsics_vec256 o1;
      Lib_IntVector_Intrinsics_vec256 o2;
      Lib_IntVector_Intrinsics_vec256 o3;
      Lib_IntVector_Intrinsics_vec256 o4;
      memcpy(tmp, last, rem * sizeof (last[0U]));
      u0 = load64_le(tmp);
      lo = u0;
      u = load64_le(tmp + (u32)8U);
      hi = u;
      f0 = Lib_IntVector_Intrinsics_vec256_load64(lo);
      f1 = Lib_IntVector_Intrinsics_vec256_load64(hi);
      f010 =
        Lib_IntVector_Intrinsics_vec256_and(f0,
          Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
      f110 =
        Lib_IntVector_Intrinsics_vec256_and(Lib_IntVector_Intrinsics_vec256_shift_right64(f0,
            (u32)26U),
          Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
      f20 =
        Lib_IntVector_Intrinsics_vec256_or(Lib_IntVector_Intrinsics_vec256_shift_right64(f0,
            (u32)52U),
          Lib_IntVector_Intrinsics_vec256_shift_left64(Lib_IntVector_Intrinsics_vec256_and(f1,
              Lib_IntVector_Intrinsics_vec256_load64((u64)0x3fffU)),
            (u32)12U));
      f30 =
        Lib_IntVector_Intrinsics_vec256_and(Lib_IntVector_Intrinsics_vec256_shift_right64(f1,
            (u32)14U),
          Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
      f40 = Lib_IntVector_Intrinsics_vec256_shift_right64(f1, (u32)40U);
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
      mask = Lib_IntVector_Intrinsics_vec256_load64(b);
      fi = e[rem * (u32)8U / (u32)26U];
      e[rem * (u32)8U / (u32)26U] = Lib_IntVector_Intrinsics_vec256_or(fi, mask);
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
      a01 = Lib_IntVector_Intrinsics_vec256_add64(a0, f10);
      a11 = Lib_IntVector_Intrinsics_vec256_add64(a1, f11);
      a21 = Lib_IntVector_Intrinsics_vec256_add64(a2, f12);
      a31 = Lib_IntVector_Intrinsics_vec256_add64(a3, f13);
      a41 = Lib_IntVector_Intrinsics_vec256_add64(a4, f14);
      a02 = Lib_IntVector_Intrinsics_vec256_mul64(r0, a01);
      a12 = Lib_IntVector_Intrinsics_vec256_mul64(r1, a01);
      a22 = Lib_IntVector_Intrinsics_vec256_mul64(r2, a01);
      a32 = Lib_IntVector_Intrinsics_vec256_mul64(r3, a01);
      a42 = Lib_IntVector_Intrinsics_vec256_mul64(r4, a01);
      a03 =
        Lib_IntVector_Intrinsics_vec256_add64(a02,
          Lib_IntVector_Intrinsics_vec256_mul64(r54, a11));
      a13 =
        Lib_IntVector_Intrinsics_vec256_add64(a12,
          Lib_IntVector_Intrinsics_vec256_mul64(r0, a11));
      a23 =
        Lib_IntVector_Intrinsics_vec256_add64(a22,
          Lib_IntVector_Intrinsics_vec256_mul64(r1, a11));
      a33 =
        Lib_IntVector_Intrinsics_vec256_add64(a32,
          Lib_IntVector_Intrinsics_vec256_mul64(r2, a11));
      a43 =
        Lib_IntVector_Intrinsics_vec256_add64(a42,
          Lib_IntVector_Intrinsics_vec256_mul64(r3, a11));
      a04 =
        Lib_IntVector_Intrinsics_vec256_add64(a03,
          Lib_IntVector_Intrinsics_vec256_mul64(r53, a21));
      a14 =
        Lib_IntVector_Intrinsics_vec256_add64(a13,
          Lib_IntVector_Intrinsics_vec256_mul64(r54, a21));
      a24 =
        Lib_IntVector_Intrinsics_vec256_add64(a23,
          Lib_IntVector_Intrinsics_vec256_mul64(r0, a21));
      a34 =
        Lib_IntVector_Intrinsics_vec256_add64(a33,
          Lib_IntVector_Intrinsics_vec256_mul64(r1, a21));
      a44 =
        Lib_IntVector_Intrinsics_vec256_add64(a43,
          Lib_IntVector_Intrinsics_vec256_mul64(r2, a21));
      a05 =
        Lib_IntVector_Intrinsics_vec256_add64(a04,
          Lib_IntVector_Intrinsics_vec256_mul64(r52, a31));
      a15 =
        Lib_IntVector_Intrinsics_vec256_add64(a14,
          Lib_IntVector_Intrinsics_vec256_mul64(r53, a31));
      a25 =
        Lib_IntVector_Intrinsics_vec256_add64(a24,
          Lib_IntVector_Intrinsics_vec256_mul64(r54, a31));
      a35 =
        Lib_IntVector_Intrinsics_vec256_add64(a34,
          Lib_IntVector_Intrinsics_vec256_mul64(r0, a31));
      a45 =
        Lib_IntVector_Intrinsics_vec256_add64(a44,
          Lib_IntVector_Intrinsics_vec256_mul64(r1, a31));
      a06 =
        Lib_IntVector_Intrinsics_vec256_add64(a05,
          Lib_IntVector_Intrinsics_vec256_mul64(r51, a41));
      a16 =
        Lib_IntVector_Intrinsics_vec256_add64(a15,
          Lib_IntVector_Intrinsics_vec256_mul64(r52, a41));
      a26 =
        Lib_IntVector_Intrinsics_vec256_add64(a25,
          Lib_IntVector_Intrinsics_vec256_mul64(r53, a41));
      a36 =
        Lib_IntVector_Intrinsics_vec256_add64(a35,
          Lib_IntVector_Intrinsics_vec256_mul64(r54, a41));
      a46 =
        Lib_IntVector_Intrinsics_vec256_add64(a45,
          Lib_IntVector_Intrinsics_vec256_mul64(r0, a41));
      t01 = a06;
      t11 = a16;
      t2 = a26;
      t3 = a36;
      t4 = a46;
      mask26 = Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU);
      z0 = Lib_IntVector_Intrinsics_vec256_shift_right64(t01, (u32)26U);
      z1 = Lib_IntVector_Intrinsics_vec256_shift_right64(t3, (u32)26U);
      x0 = Lib_IntVector_Intrinsics_vec256_and(t01, mask26);
      x3 = Lib_IntVector_Intrinsics_vec256_and(t3, mask26);
      x1 = Lib_IntVector_Intrinsics_vec256_add64(t11, z0);
      x4 = Lib_IntVector_Intrinsics_vec256_add64(t4, z1);
      z01 = Lib_IntVector_Intrinsics_vec256_shift_right64(x1, (u32)26U);
      z11 = Lib_IntVector_Intrinsics_vec256_shift_right64(x4, (u32)26U);
      t = Lib_IntVector_Intrinsics_vec256_shift_left64(z11, (u32)2U);
      z12 = Lib_IntVector_Intrinsics_vec256_add64(z11, t);
      x11 = Lib_IntVector_Intrinsics_vec256_and(x1, mask26);
      x41 = Lib_IntVector_Intrinsics_vec256_and(x4, mask26);
      x2 = Lib_IntVector_Intrinsics_vec256_add64(t2, z01);
      x01 = Lib_IntVector_Intrinsics_vec256_add64(x0, z12);
      z02 = Lib_IntVector_Intrinsics_vec256_shift_right64(x2, (u32)26U);
      z13 = Lib_IntVector_Intrinsics_vec256_shift_right64(x01, (u32)26U);
      x21 = Lib_IntVector_Intrinsics_vec256_and(x2, mask26);
      x02 = Lib_IntVector_Intrinsics_vec256_and(x01, mask26);
      x31 = Lib_IntVector_Intrinsics_vec256_add64(x3, z02);
      x12 = Lib_IntVector_Intrinsics_vec256_add64(x11, z13);
      z03 = Lib_IntVector_Intrinsics_vec256_shift_right64(x31, (u32)26U);
      x32 = Lib_IntVector_Intrinsics_vec256_and(x31, mask26);
      x42 = Lib_IntVector_Intrinsics_vec256_add64(x41, z03);
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

void Hacl_Poly1305_256_poly1305_finish(u8 *tag, u8 *key, Lib_IntVector_Intrinsics_vec256 *ctx)
{
  Lib_IntVector_Intrinsics_vec256 *acc = ctx;
  u8 *ks = key + (u32)16U;
  Lib_IntVector_Intrinsics_vec256 f00 = acc[0U];
  Lib_IntVector_Intrinsics_vec256 f13 = acc[1U];
  Lib_IntVector_Intrinsics_vec256 f23 = acc[2U];
  Lib_IntVector_Intrinsics_vec256 f33 = acc[3U];
  Lib_IntVector_Intrinsics_vec256 f40 = acc[4U];
  Lib_IntVector_Intrinsics_vec256
  l0 = Lib_IntVector_Intrinsics_vec256_add64(f00, Lib_IntVector_Intrinsics_vec256_zero);
  Lib_IntVector_Intrinsics_vec256
  tmp00 =
    Lib_IntVector_Intrinsics_vec256_and(l0,
      Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec256
  c00 = Lib_IntVector_Intrinsics_vec256_shift_right64(l0, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 l1 = Lib_IntVector_Intrinsics_vec256_add64(f13, c00);
  Lib_IntVector_Intrinsics_vec256
  tmp10 =
    Lib_IntVector_Intrinsics_vec256_and(l1,
      Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec256
  c10 = Lib_IntVector_Intrinsics_vec256_shift_right64(l1, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 l2 = Lib_IntVector_Intrinsics_vec256_add64(f23, c10);
  Lib_IntVector_Intrinsics_vec256
  tmp20 =
    Lib_IntVector_Intrinsics_vec256_and(l2,
      Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec256
  c20 = Lib_IntVector_Intrinsics_vec256_shift_right64(l2, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 l3 = Lib_IntVector_Intrinsics_vec256_add64(f33, c20);
  Lib_IntVector_Intrinsics_vec256
  tmp30 =
    Lib_IntVector_Intrinsics_vec256_and(l3,
      Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec256
  c30 = Lib_IntVector_Intrinsics_vec256_shift_right64(l3, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 l4 = Lib_IntVector_Intrinsics_vec256_add64(f40, c30);
  Lib_IntVector_Intrinsics_vec256
  tmp40 =
    Lib_IntVector_Intrinsics_vec256_and(l4,
      Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec256
  c40 = Lib_IntVector_Intrinsics_vec256_shift_right64(l4, (u32)26U);
  Lib_IntVector_Intrinsics_vec256
  f010 =
    Lib_IntVector_Intrinsics_vec256_add64(tmp00,
      Lib_IntVector_Intrinsics_vec256_smul64(c40, (u64)5U));
  Lib_IntVector_Intrinsics_vec256 f110 = tmp10;
  Lib_IntVector_Intrinsics_vec256 f210 = tmp20;
  Lib_IntVector_Intrinsics_vec256 f310 = tmp30;
  Lib_IntVector_Intrinsics_vec256 f410 = tmp40;
  Lib_IntVector_Intrinsics_vec256
  l = Lib_IntVector_Intrinsics_vec256_add64(f010, Lib_IntVector_Intrinsics_vec256_zero);
  Lib_IntVector_Intrinsics_vec256
  tmp0 =
    Lib_IntVector_Intrinsics_vec256_and(l,
      Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec256
  c0 = Lib_IntVector_Intrinsics_vec256_shift_right64(l, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 l5 = Lib_IntVector_Intrinsics_vec256_add64(f110, c0);
  Lib_IntVector_Intrinsics_vec256
  tmp1 =
    Lib_IntVector_Intrinsics_vec256_and(l5,
      Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec256
  c1 = Lib_IntVector_Intrinsics_vec256_shift_right64(l5, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 l6 = Lib_IntVector_Intrinsics_vec256_add64(f210, c1);
  Lib_IntVector_Intrinsics_vec256
  tmp2 =
    Lib_IntVector_Intrinsics_vec256_and(l6,
      Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec256
  c2 = Lib_IntVector_Intrinsics_vec256_shift_right64(l6, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 l7 = Lib_IntVector_Intrinsics_vec256_add64(f310, c2);
  Lib_IntVector_Intrinsics_vec256
  tmp3 =
    Lib_IntVector_Intrinsics_vec256_and(l7,
      Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec256
  c3 = Lib_IntVector_Intrinsics_vec256_shift_right64(l7, (u32)26U);
  Lib_IntVector_Intrinsics_vec256 l8 = Lib_IntVector_Intrinsics_vec256_add64(f410, c3);
  Lib_IntVector_Intrinsics_vec256
  tmp4 =
    Lib_IntVector_Intrinsics_vec256_and(l8,
      Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU));
  Lib_IntVector_Intrinsics_vec256
  c4 = Lib_IntVector_Intrinsics_vec256_shift_right64(l8, (u32)26U);
  Lib_IntVector_Intrinsics_vec256
  f02 =
    Lib_IntVector_Intrinsics_vec256_add64(tmp0,
      Lib_IntVector_Intrinsics_vec256_smul64(c4, (u64)5U));
  Lib_IntVector_Intrinsics_vec256 f12 = tmp1;
  Lib_IntVector_Intrinsics_vec256 f22 = tmp2;
  Lib_IntVector_Intrinsics_vec256 f32 = tmp3;
  Lib_IntVector_Intrinsics_vec256 f42 = tmp4;
  Lib_IntVector_Intrinsics_vec256 mh = Lib_IntVector_Intrinsics_vec256_load64((u64)0x3ffffffU);
  Lib_IntVector_Intrinsics_vec256 ml = Lib_IntVector_Intrinsics_vec256_load64((u64)0x3fffffbU);
  Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_eq64(f42, mh);
  Lib_IntVector_Intrinsics_vec256
  mask1 =
    Lib_IntVector_Intrinsics_vec256_and(mask,
      Lib_IntVector_Intrinsics_vec256_eq64(f32, mh));
  Lib_IntVector_Intrinsics_vec256
  mask2 =
    Lib_IntVector_Intrinsics_vec256_and(mask1,
      Lib_IntVector_Intrinsics_vec256_eq64(f22, mh));
  Lib_IntVector_Intrinsics_vec256
  mask3 =
    Lib_IntVector_Intrinsics_vec256_and(mask2,
      Lib_IntVector_Intrinsics_vec256_eq64(f12, mh));
  Lib_IntVector_Intrinsics_vec256
  mask4 =
    Lib_IntVector_Intrinsics_vec256_and(mask3,
      Lib_IntVector_Intrinsics_vec256_lognot(Lib_IntVector_Intrinsics_vec256_gt64(ml, f02)));
  Lib_IntVector_Intrinsics_vec256 ph = Lib_IntVector_Intrinsics_vec256_and(mask4, mh);
  Lib_IntVector_Intrinsics_vec256 pl = Lib_IntVector_Intrinsics_vec256_and(mask4, ml);
  Lib_IntVector_Intrinsics_vec256 o0 = Lib_IntVector_Intrinsics_vec256_sub64(f02, pl);
  Lib_IntVector_Intrinsics_vec256 o1 = Lib_IntVector_Intrinsics_vec256_sub64(f12, ph);
  Lib_IntVector_Intrinsics_vec256 o2 = Lib_IntVector_Intrinsics_vec256_sub64(f22, ph);
  Lib_IntVector_Intrinsics_vec256 o3 = Lib_IntVector_Intrinsics_vec256_sub64(f32, ph);
  Lib_IntVector_Intrinsics_vec256 o4 = Lib_IntVector_Intrinsics_vec256_sub64(f42, ph);
  Lib_IntVector_Intrinsics_vec256 f011 = o0;
  Lib_IntVector_Intrinsics_vec256 f111 = o1;
  Lib_IntVector_Intrinsics_vec256 f211 = o2;
  Lib_IntVector_Intrinsics_vec256 f311 = o3;
  Lib_IntVector_Intrinsics_vec256 f411 = o4;
  Lib_IntVector_Intrinsics_vec256 f0;
  Lib_IntVector_Intrinsics_vec256 f1;
  Lib_IntVector_Intrinsics_vec256 f2;
  Lib_IntVector_Intrinsics_vec256 f3;
  Lib_IntVector_Intrinsics_vec256 f4;
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
  f01 = Lib_IntVector_Intrinsics_vec256_extract64(f0, (u32)0U);
  f112 = Lib_IntVector_Intrinsics_vec256_extract64(f1, (u32)0U);
  f212 = Lib_IntVector_Intrinsics_vec256_extract64(f2, (u32)0U);
  f312 = Lib_IntVector_Intrinsics_vec256_extract64(f3, (u32)0U);
  f41 = Lib_IntVector_Intrinsics_vec256_extract64(f4, (u32)0U);
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

void Hacl_Poly1305_256_poly1305_mac(u8 *tag, u32 len, u8 *text, u8 *key)
{
  Lib_IntVector_Intrinsics_vec256 ctx[25U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)25U; ++_i)
      ctx[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  }
  Hacl_Poly1305_256_poly1305_init(ctx, key);
  Hacl_Poly1305_256_poly1305_update(ctx, len, text);
  Hacl_Poly1305_256_poly1305_finish(tag, key, ctx);
}

