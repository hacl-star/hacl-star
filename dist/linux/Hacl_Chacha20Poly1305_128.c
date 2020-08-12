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


#include "Hacl_Chacha20Poly1305_128.h"

static inline void poly1305_padded_128(Lib_IntVector_Intrinsics_vec128 *ctx, u32 len, u8 *text)
{
  u32 n = len / (u32)16U;
  u32 r = len % (u32)16U;
  u8 *blocks = text;
  u8 *rem = text + n * (u32)16U;
  Lib_IntVector_Intrinsics_vec128 *pre0 = ctx + (u32)5U;
  Lib_IntVector_Intrinsics_vec128 *acc0 = ctx;
  u32 sz_block = (u32)32U;
  u32 len0 = n * (u32)16U / sz_block * sz_block;
  u8 *t00 = blocks;
  u32 len1;
  u8 *t10;
  u32 nb0;
  u32 rem1;
  if (len0 > (u32)0U)
  {
    u32 bs = (u32)32U;
    u8 *text0 = t00;
    Hacl_Impl_Poly1305_Field32xN_128_load_acc2(acc0, text0);
    {
      u32 len10 = len0 - bs;
      u8 *text1 = t00 + bs;
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
                Lib_IntVector_Intrinsics_vec128 *rn = pre0 + (u32)10U;
                Lib_IntVector_Intrinsics_vec128 *rn5 = pre0 + (u32)15U;
                Lib_IntVector_Intrinsics_vec128 r0 = rn[0U];
                Lib_IntVector_Intrinsics_vec128 r1 = rn[1U];
                Lib_IntVector_Intrinsics_vec128 r2 = rn[2U];
                Lib_IntVector_Intrinsics_vec128 r3 = rn[3U];
                Lib_IntVector_Intrinsics_vec128 r4 = rn[4U];
                Lib_IntVector_Intrinsics_vec128 r51 = rn5[1U];
                Lib_IntVector_Intrinsics_vec128 r52 = rn5[2U];
                Lib_IntVector_Intrinsics_vec128 r53 = rn5[3U];
                Lib_IntVector_Intrinsics_vec128 r54 = rn5[4U];
                Lib_IntVector_Intrinsics_vec128 f10 = acc0[0U];
                Lib_IntVector_Intrinsics_vec128 f110 = acc0[1U];
                Lib_IntVector_Intrinsics_vec128 f120 = acc0[2U];
                Lib_IntVector_Intrinsics_vec128 f130 = acc0[3U];
                Lib_IntVector_Intrinsics_vec128 f140 = acc0[4U];
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
                acc0[0U] = o00;
                acc0[1U] = o10;
                acc0[2U] = o20;
                acc0[3U] = o30;
                acc0[4U] = o40;
                {
                  Lib_IntVector_Intrinsics_vec128 f100 = acc0[0U];
                  Lib_IntVector_Intrinsics_vec128 f11 = acc0[1U];
                  Lib_IntVector_Intrinsics_vec128 f12 = acc0[2U];
                  Lib_IntVector_Intrinsics_vec128 f13 = acc0[3U];
                  Lib_IntVector_Intrinsics_vec128 f14 = acc0[4U];
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
                  acc0[0U] = o0;
                  acc0[1U] = o1;
                  acc0[2U] = o2;
                  acc0[3U] = o3;
                  acc0[4U] = o4;
                }
              }
            }
          }
        }
      }
      Hacl_Impl_Poly1305_Field32xN_128_fmul_r2_normalize(acc0, pre0);
    }
  }
  len1 = n * (u32)16U - len0;
  t10 = blocks + len0;
  nb0 = len1 / (u32)16U;
  rem1 = len1 % (u32)16U;
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
            Lib_IntVector_Intrinsics_vec128 *r1 = pre0;
            Lib_IntVector_Intrinsics_vec128 *r5 = pre0 + (u32)5U;
            Lib_IntVector_Intrinsics_vec128 r0 = r1[0U];
            Lib_IntVector_Intrinsics_vec128 r11 = r1[1U];
            Lib_IntVector_Intrinsics_vec128 r2 = r1[2U];
            Lib_IntVector_Intrinsics_vec128 r3 = r1[3U];
            Lib_IntVector_Intrinsics_vec128 r4 = r1[4U];
            Lib_IntVector_Intrinsics_vec128 r51 = r5[1U];
            Lib_IntVector_Intrinsics_vec128 r52 = r5[2U];
            Lib_IntVector_Intrinsics_vec128 r53 = r5[3U];
            Lib_IntVector_Intrinsics_vec128 r54 = r5[4U];
            Lib_IntVector_Intrinsics_vec128 f10 = e[0U];
            Lib_IntVector_Intrinsics_vec128 f11 = e[1U];
            Lib_IntVector_Intrinsics_vec128 f12 = e[2U];
            Lib_IntVector_Intrinsics_vec128 f13 = e[3U];
            Lib_IntVector_Intrinsics_vec128 f14 = e[4U];
            Lib_IntVector_Intrinsics_vec128 a0 = acc0[0U];
            Lib_IntVector_Intrinsics_vec128 a1 = acc0[1U];
            Lib_IntVector_Intrinsics_vec128 a2 = acc0[2U];
            Lib_IntVector_Intrinsics_vec128 a3 = acc0[3U];
            Lib_IntVector_Intrinsics_vec128 a4 = acc0[4U];
            Lib_IntVector_Intrinsics_vec128 a01 = Lib_IntVector_Intrinsics_vec128_add64(a0, f10);
            Lib_IntVector_Intrinsics_vec128 a11 = Lib_IntVector_Intrinsics_vec128_add64(a1, f11);
            Lib_IntVector_Intrinsics_vec128 a21 = Lib_IntVector_Intrinsics_vec128_add64(a2, f12);
            Lib_IntVector_Intrinsics_vec128 a31 = Lib_IntVector_Intrinsics_vec128_add64(a3, f13);
            Lib_IntVector_Intrinsics_vec128 a41 = Lib_IntVector_Intrinsics_vec128_add64(a4, f14);
            Lib_IntVector_Intrinsics_vec128 a02 = Lib_IntVector_Intrinsics_vec128_mul64(r0, a01);
            Lib_IntVector_Intrinsics_vec128 a12 = Lib_IntVector_Intrinsics_vec128_mul64(r11, a01);
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
                Lib_IntVector_Intrinsics_vec128_mul64(r11, a11));
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
                Lib_IntVector_Intrinsics_vec128_mul64(r11, a21));
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
                Lib_IntVector_Intrinsics_vec128_mul64(r11, a31));
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
            acc0[0U] = o0;
            acc0[1U] = o1;
            acc0[2U] = o2;
            acc0[3U] = o3;
            acc0[4U] = o4;
          }
        }
      }
    }
  }
  if (rem1 > (u32)0U)
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
      memcpy(tmp, last, rem1 * sizeof (u8));
      {
        u64 u0 = load64_le(tmp);
        u64 lo = u0;
        u64 u = load64_le(tmp + (u32)8U);
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
        Lib_IntVector_Intrinsics_vec128 f4 = f40;
        e[0U] = f01;
        e[1U] = f111;
        e[2U] = f2;
        e[3U] = f3;
        e[4U] = f4;
        {
          u64 b = (u64)1U << rem1 * (u32)8U % (u32)26U;
          Lib_IntVector_Intrinsics_vec128 mask = Lib_IntVector_Intrinsics_vec128_load64(b);
          Lib_IntVector_Intrinsics_vec128 fi = e[rem1 * (u32)8U / (u32)26U];
          e[rem1 * (u32)8U / (u32)26U] = Lib_IntVector_Intrinsics_vec128_or(fi, mask);
          {
            Lib_IntVector_Intrinsics_vec128 *r1 = pre0;
            Lib_IntVector_Intrinsics_vec128 *r5 = pre0 + (u32)5U;
            Lib_IntVector_Intrinsics_vec128 r0 = r1[0U];
            Lib_IntVector_Intrinsics_vec128 r11 = r1[1U];
            Lib_IntVector_Intrinsics_vec128 r2 = r1[2U];
            Lib_IntVector_Intrinsics_vec128 r3 = r1[3U];
            Lib_IntVector_Intrinsics_vec128 r4 = r1[4U];
            Lib_IntVector_Intrinsics_vec128 r51 = r5[1U];
            Lib_IntVector_Intrinsics_vec128 r52 = r5[2U];
            Lib_IntVector_Intrinsics_vec128 r53 = r5[3U];
            Lib_IntVector_Intrinsics_vec128 r54 = r5[4U];
            Lib_IntVector_Intrinsics_vec128 f10 = e[0U];
            Lib_IntVector_Intrinsics_vec128 f11 = e[1U];
            Lib_IntVector_Intrinsics_vec128 f12 = e[2U];
            Lib_IntVector_Intrinsics_vec128 f13 = e[3U];
            Lib_IntVector_Intrinsics_vec128 f14 = e[4U];
            Lib_IntVector_Intrinsics_vec128 a0 = acc0[0U];
            Lib_IntVector_Intrinsics_vec128 a1 = acc0[1U];
            Lib_IntVector_Intrinsics_vec128 a2 = acc0[2U];
            Lib_IntVector_Intrinsics_vec128 a3 = acc0[3U];
            Lib_IntVector_Intrinsics_vec128 a4 = acc0[4U];
            Lib_IntVector_Intrinsics_vec128 a01 = Lib_IntVector_Intrinsics_vec128_add64(a0, f10);
            Lib_IntVector_Intrinsics_vec128 a11 = Lib_IntVector_Intrinsics_vec128_add64(a1, f11);
            Lib_IntVector_Intrinsics_vec128 a21 = Lib_IntVector_Intrinsics_vec128_add64(a2, f12);
            Lib_IntVector_Intrinsics_vec128 a31 = Lib_IntVector_Intrinsics_vec128_add64(a3, f13);
            Lib_IntVector_Intrinsics_vec128 a41 = Lib_IntVector_Intrinsics_vec128_add64(a4, f14);
            Lib_IntVector_Intrinsics_vec128 a02 = Lib_IntVector_Intrinsics_vec128_mul64(r0, a01);
            Lib_IntVector_Intrinsics_vec128 a12 = Lib_IntVector_Intrinsics_vec128_mul64(r11, a01);
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
                Lib_IntVector_Intrinsics_vec128_mul64(r11, a11));
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
                Lib_IntVector_Intrinsics_vec128_mul64(r11, a21));
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
                Lib_IntVector_Intrinsics_vec128_mul64(r11, a31));
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
            acc0[0U] = o0;
            acc0[1U] = o1;
            acc0[2U] = o2;
            acc0[3U] = o3;
            acc0[4U] = o4;
          }
        }
      }
    }
  }
  {
    u8 tmp[16U] = { 0U };
    memcpy(tmp, rem, r * sizeof (u8));
    if (r > (u32)0U)
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
        u64 u0 = load64_le(tmp);
        u64 lo = u0;
        u64 u = load64_le(tmp + (u32)8U);
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
        u64 b;
        Lib_IntVector_Intrinsics_vec128 mask;
        Lib_IntVector_Intrinsics_vec128 f4;
        Lib_IntVector_Intrinsics_vec128 *r1;
        Lib_IntVector_Intrinsics_vec128 *r5;
        Lib_IntVector_Intrinsics_vec128 r0;
        Lib_IntVector_Intrinsics_vec128 r11;
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
        r1 = pre;
        r5 = pre + (u32)5U;
        r0 = r1[0U];
        r11 = r1[1U];
        r2 = r1[2U];
        r3 = r1[3U];
        r4 = r1[4U];
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
        a12 = Lib_IntVector_Intrinsics_vec128_mul64(r11, a01);
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
            Lib_IntVector_Intrinsics_vec128_mul64(r11, a11));
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
            Lib_IntVector_Intrinsics_vec128_mul64(r11, a21));
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
            Lib_IntVector_Intrinsics_vec128_mul64(r11, a31));
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
        return;
      }
    }
  }
}

static inline void poly1305_do_128(u8 *k, u32 aadlen, u8 *aad, u32 mlen, u8 *m, u8 *out)
{
  Lib_IntVector_Intrinsics_vec128 ctx[25U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)25U; ++_i)
      ctx[_i] = Lib_IntVector_Intrinsics_vec128_zero;
  }
  {
    u8 block[16U] = { 0U };
    Lib_IntVector_Intrinsics_vec128 *pre;
    Lib_IntVector_Intrinsics_vec128 *acc;
    Hacl_Poly1305_128_poly1305_init(ctx, k);
    poly1305_padded_128(ctx, aadlen, aad);
    poly1305_padded_128(ctx, mlen, m);
    store64_le(block, (u64)aadlen);
    store64_le(block + (u32)8U, (u64)mlen);
    pre = ctx + (u32)5U;
    acc = ctx;
    {
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
        Hacl_Poly1305_128_poly1305_finish(out, k, ctx);
      }
    }
  }
}

void
Hacl_Chacha20Poly1305_128_aead_encrypt(
  u8 *k,
  u8 *n,
  u32 aadlen,
  u8 *aad,
  u32 mlen,
  u8 *m,
  u8 *cipher,
  u8 *mac
)
{
  Hacl_Chacha20_Vec128_chacha20_encrypt_128(mlen, cipher, m, k, n, (u32)1U);
  {
    u8 tmp[64U] = { 0U };
    u8 *key;
    Hacl_Chacha20_Vec128_chacha20_encrypt_128((u32)64U, tmp, tmp, k, n, (u32)0U);
    key = tmp;
    poly1305_do_128(key, aadlen, aad, mlen, cipher, mac);
  }
}

u32
Hacl_Chacha20Poly1305_128_aead_decrypt(
  u8 *k,
  u8 *n,
  u32 aadlen,
  u8 *aad,
  u32 mlen,
  u8 *m,
  u8 *cipher,
  u8 *mac
)
{
  u8 computed_mac[16U] = { 0U };
  u8 tmp[64U] = { 0U };
  u8 *key;
  Hacl_Chacha20_Vec128_chacha20_encrypt_128((u32)64U, tmp, tmp, k, n, (u32)0U);
  key = tmp;
  poly1305_do_128(key, aadlen, aad, mlen, cipher, computed_mac);
  {
    u8 res0 = (u8)255U;
    u8 z;
    u32 res;
    {
      u32 i;
      for (i = (u32)0U; i < (u32)16U; i++)
      {
        u8 uu____0 = FStar_UInt8_eq_mask(computed_mac[i], mac[i]);
        res0 = uu____0 & res0;
      }
    }
    z = res0;
    if (z == (u8)255U)
    {
      Hacl_Chacha20_Vec128_chacha20_encrypt_128(mlen, m, cipher, k, n, (u32)1U);
      res = (u32)0U;
    }
    else
      res = (u32)1U;
    return res;
  }
}

