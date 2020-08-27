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


#include "Hacl_Chacha20Poly1305_32.h"

static inline void poly1305_padded_32(u64 *ctx, u32 len, u8 *text)
{
  u32 n = len / (u32)16U;
  u32 r = len % (u32)16U;
  u8 *blocks = text;
  u8 *rem = text + n * (u32)16U;
  u64 *pre0 = ctx + (u32)5U;
  u64 *acc0 = ctx;
  u32 nb = n * (u32)16U / (u32)16U;
  u32 rem1 = n * (u32)16U % (u32)16U;
  {
    u32 i;
    for (i = (u32)0U; i < nb; i++)
    {
      u8 *block = blocks + i * (u32)16U;
      u64 e[5U] = { 0U };
      u64 u0 = load64_le(block);
      u64 lo = u0;
      u64 u = load64_le(block + (u32)8U);
      u64 hi = u;
      u64 f0 = lo;
      u64 f1 = hi;
      u64 f010 = f0 & (u64)0x3ffffffU;
      u64 f110 = f0 >> (u32)26U & (u64)0x3ffffffU;
      u64 f20 = f0 >> (u32)52U | (f1 & (u64)0x3fffU) << (u32)12U;
      u64 f30 = f1 >> (u32)14U & (u64)0x3ffffffU;
      u64 f40 = f1 >> (u32)40U;
      u64 f01 = f010;
      u64 f111 = f110;
      u64 f2 = f20;
      u64 f3 = f30;
      u64 f41 = f40;
      e[0U] = f01;
      e[1U] = f111;
      e[2U] = f2;
      e[3U] = f3;
      e[4U] = f41;
      {
        u64 b = (u64)0x1000000U;
        u64 mask = b;
        u64 f4 = e[4U];
        e[4U] = f4 | mask;
        {
          u64 *r1 = pre0;
          u64 *r5 = pre0 + (u32)5U;
          u64 r0 = r1[0U];
          u64 r11 = r1[1U];
          u64 r2 = r1[2U];
          u64 r3 = r1[3U];
          u64 r4 = r1[4U];
          u64 r51 = r5[1U];
          u64 r52 = r5[2U];
          u64 r53 = r5[3U];
          u64 r54 = r5[4U];
          u64 f10 = e[0U];
          u64 f11 = e[1U];
          u64 f12 = e[2U];
          u64 f13 = e[3U];
          u64 f14 = e[4U];
          u64 a0 = acc0[0U];
          u64 a1 = acc0[1U];
          u64 a2 = acc0[2U];
          u64 a3 = acc0[3U];
          u64 a4 = acc0[4U];
          u64 a01 = a0 + f10;
          u64 a11 = a1 + f11;
          u64 a21 = a2 + f12;
          u64 a31 = a3 + f13;
          u64 a41 = a4 + f14;
          u64 a02 = r0 * a01;
          u64 a12 = r11 * a01;
          u64 a22 = r2 * a01;
          u64 a32 = r3 * a01;
          u64 a42 = r4 * a01;
          u64 a03 = a02 + r54 * a11;
          u64 a13 = a12 + r0 * a11;
          u64 a23 = a22 + r11 * a11;
          u64 a33 = a32 + r2 * a11;
          u64 a43 = a42 + r3 * a11;
          u64 a04 = a03 + r53 * a21;
          u64 a14 = a13 + r54 * a21;
          u64 a24 = a23 + r0 * a21;
          u64 a34 = a33 + r11 * a21;
          u64 a44 = a43 + r2 * a21;
          u64 a05 = a04 + r52 * a31;
          u64 a15 = a14 + r53 * a31;
          u64 a25 = a24 + r54 * a31;
          u64 a35 = a34 + r0 * a31;
          u64 a45 = a44 + r11 * a31;
          u64 a06 = a05 + r51 * a41;
          u64 a16 = a15 + r52 * a41;
          u64 a26 = a25 + r53 * a41;
          u64 a36 = a35 + r54 * a41;
          u64 a46 = a45 + r0 * a41;
          u64 t0 = a06;
          u64 t1 = a16;
          u64 t2 = a26;
          u64 t3 = a36;
          u64 t4 = a46;
          u64 mask26 = (u64)0x3ffffffU;
          u64 z0 = t0 >> (u32)26U;
          u64 z1 = t3 >> (u32)26U;
          u64 x0 = t0 & mask26;
          u64 x3 = t3 & mask26;
          u64 x1 = t1 + z0;
          u64 x4 = t4 + z1;
          u64 z01 = x1 >> (u32)26U;
          u64 z11 = x4 >> (u32)26U;
          u64 t = z11 << (u32)2U;
          u64 z12 = z11 + t;
          u64 x11 = x1 & mask26;
          u64 x41 = x4 & mask26;
          u64 x2 = t2 + z01;
          u64 x01 = x0 + z12;
          u64 z02 = x2 >> (u32)26U;
          u64 z13 = x01 >> (u32)26U;
          u64 x21 = x2 & mask26;
          u64 x02 = x01 & mask26;
          u64 x31 = x3 + z02;
          u64 x12 = x11 + z13;
          u64 z03 = x31 >> (u32)26U;
          u64 x32 = x31 & mask26;
          u64 x42 = x41 + z03;
          u64 o0 = x02;
          u64 o1 = x12;
          u64 o2 = x21;
          u64 o3 = x32;
          u64 o4 = x42;
          acc0[0U] = o0;
          acc0[1U] = o1;
          acc0[2U] = o2;
          acc0[3U] = o3;
          acc0[4U] = o4;
        }
      }
    }
  }
  if (rem1 > (u32)0U)
  {
    u8 *last = blocks + nb * (u32)16U;
    u64 e[5U] = { 0U };
    u8 tmp[16U] = { 0U };
    memcpy(tmp, last, rem1 * sizeof (u8));
    {
      u64 u0 = load64_le(tmp);
      u64 lo = u0;
      u64 u = load64_le(tmp + (u32)8U);
      u64 hi = u;
      u64 f0 = lo;
      u64 f1 = hi;
      u64 f010 = f0 & (u64)0x3ffffffU;
      u64 f110 = f0 >> (u32)26U & (u64)0x3ffffffU;
      u64 f20 = f0 >> (u32)52U | (f1 & (u64)0x3fffU) << (u32)12U;
      u64 f30 = f1 >> (u32)14U & (u64)0x3ffffffU;
      u64 f40 = f1 >> (u32)40U;
      u64 f01 = f010;
      u64 f111 = f110;
      u64 f2 = f20;
      u64 f3 = f30;
      u64 f4 = f40;
      e[0U] = f01;
      e[1U] = f111;
      e[2U] = f2;
      e[3U] = f3;
      e[4U] = f4;
      {
        u64 b = (u64)1U << rem1 * (u32)8U % (u32)26U;
        u64 mask = b;
        u64 fi = e[rem1 * (u32)8U / (u32)26U];
        e[rem1 * (u32)8U / (u32)26U] = fi | mask;
        {
          u64 *r1 = pre0;
          u64 *r5 = pre0 + (u32)5U;
          u64 r0 = r1[0U];
          u64 r11 = r1[1U];
          u64 r2 = r1[2U];
          u64 r3 = r1[3U];
          u64 r4 = r1[4U];
          u64 r51 = r5[1U];
          u64 r52 = r5[2U];
          u64 r53 = r5[3U];
          u64 r54 = r5[4U];
          u64 f10 = e[0U];
          u64 f11 = e[1U];
          u64 f12 = e[2U];
          u64 f13 = e[3U];
          u64 f14 = e[4U];
          u64 a0 = acc0[0U];
          u64 a1 = acc0[1U];
          u64 a2 = acc0[2U];
          u64 a3 = acc0[3U];
          u64 a4 = acc0[4U];
          u64 a01 = a0 + f10;
          u64 a11 = a1 + f11;
          u64 a21 = a2 + f12;
          u64 a31 = a3 + f13;
          u64 a41 = a4 + f14;
          u64 a02 = r0 * a01;
          u64 a12 = r11 * a01;
          u64 a22 = r2 * a01;
          u64 a32 = r3 * a01;
          u64 a42 = r4 * a01;
          u64 a03 = a02 + r54 * a11;
          u64 a13 = a12 + r0 * a11;
          u64 a23 = a22 + r11 * a11;
          u64 a33 = a32 + r2 * a11;
          u64 a43 = a42 + r3 * a11;
          u64 a04 = a03 + r53 * a21;
          u64 a14 = a13 + r54 * a21;
          u64 a24 = a23 + r0 * a21;
          u64 a34 = a33 + r11 * a21;
          u64 a44 = a43 + r2 * a21;
          u64 a05 = a04 + r52 * a31;
          u64 a15 = a14 + r53 * a31;
          u64 a25 = a24 + r54 * a31;
          u64 a35 = a34 + r0 * a31;
          u64 a45 = a44 + r11 * a31;
          u64 a06 = a05 + r51 * a41;
          u64 a16 = a15 + r52 * a41;
          u64 a26 = a25 + r53 * a41;
          u64 a36 = a35 + r54 * a41;
          u64 a46 = a45 + r0 * a41;
          u64 t0 = a06;
          u64 t1 = a16;
          u64 t2 = a26;
          u64 t3 = a36;
          u64 t4 = a46;
          u64 mask26 = (u64)0x3ffffffU;
          u64 z0 = t0 >> (u32)26U;
          u64 z1 = t3 >> (u32)26U;
          u64 x0 = t0 & mask26;
          u64 x3 = t3 & mask26;
          u64 x1 = t1 + z0;
          u64 x4 = t4 + z1;
          u64 z01 = x1 >> (u32)26U;
          u64 z11 = x4 >> (u32)26U;
          u64 t = z11 << (u32)2U;
          u64 z12 = z11 + t;
          u64 x11 = x1 & mask26;
          u64 x41 = x4 & mask26;
          u64 x2 = t2 + z01;
          u64 x01 = x0 + z12;
          u64 z02 = x2 >> (u32)26U;
          u64 z13 = x01 >> (u32)26U;
          u64 x21 = x2 & mask26;
          u64 x02 = x01 & mask26;
          u64 x31 = x3 + z02;
          u64 x12 = x11 + z13;
          u64 z03 = x31 >> (u32)26U;
          u64 x32 = x31 & mask26;
          u64 x42 = x41 + z03;
          u64 o0 = x02;
          u64 o1 = x12;
          u64 o2 = x21;
          u64 o3 = x32;
          u64 o4 = x42;
          acc0[0U] = o0;
          acc0[1U] = o1;
          acc0[2U] = o2;
          acc0[3U] = o3;
          acc0[4U] = o4;
        }
      }
    }
  }
  {
    u8 tmp[16U] = { 0U };
    memcpy(tmp, rem, r * sizeof (u8));
    if (r > (u32)0U)
    {
      u64 *pre = ctx + (u32)5U;
      u64 *acc = ctx;
      u64 e[5U] = { 0U };
      u64 u0 = load64_le(tmp);
      u64 lo = u0;
      u64 u = load64_le(tmp + (u32)8U);
      u64 hi = u;
      u64 f0 = lo;
      u64 f1 = hi;
      u64 f010 = f0 & (u64)0x3ffffffU;
      u64 f110 = f0 >> (u32)26U & (u64)0x3ffffffU;
      u64 f20 = f0 >> (u32)52U | (f1 & (u64)0x3fffU) << (u32)12U;
      u64 f30 = f1 >> (u32)14U & (u64)0x3ffffffU;
      u64 f40 = f1 >> (u32)40U;
      u64 f01 = f010;
      u64 f111 = f110;
      u64 f2 = f20;
      u64 f3 = f30;
      u64 f41 = f40;
      u64 b;
      u64 mask;
      u64 f4;
      u64 *r1;
      u64 *r5;
      u64 r0;
      u64 r11;
      u64 r2;
      u64 r3;
      u64 r4;
      u64 r51;
      u64 r52;
      u64 r53;
      u64 r54;
      u64 f10;
      u64 f11;
      u64 f12;
      u64 f13;
      u64 f14;
      u64 a0;
      u64 a1;
      u64 a2;
      u64 a3;
      u64 a4;
      u64 a01;
      u64 a11;
      u64 a21;
      u64 a31;
      u64 a41;
      u64 a02;
      u64 a12;
      u64 a22;
      u64 a32;
      u64 a42;
      u64 a03;
      u64 a13;
      u64 a23;
      u64 a33;
      u64 a43;
      u64 a04;
      u64 a14;
      u64 a24;
      u64 a34;
      u64 a44;
      u64 a05;
      u64 a15;
      u64 a25;
      u64 a35;
      u64 a45;
      u64 a06;
      u64 a16;
      u64 a26;
      u64 a36;
      u64 a46;
      u64 t0;
      u64 t1;
      u64 t2;
      u64 t3;
      u64 t4;
      u64 mask26;
      u64 z0;
      u64 z1;
      u64 x0;
      u64 x3;
      u64 x1;
      u64 x4;
      u64 z01;
      u64 z11;
      u64 t;
      u64 z12;
      u64 x11;
      u64 x41;
      u64 x2;
      u64 x01;
      u64 z02;
      u64 z13;
      u64 x21;
      u64 x02;
      u64 x31;
      u64 x12;
      u64 z03;
      u64 x32;
      u64 x42;
      u64 o0;
      u64 o1;
      u64 o2;
      u64 o3;
      u64 o4;
      e[0U] = f01;
      e[1U] = f111;
      e[2U] = f2;
      e[3U] = f3;
      e[4U] = f41;
      b = (u64)0x1000000U;
      mask = b;
      f4 = e[4U];
      e[4U] = f4 | mask;
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
      a01 = a0 + f10;
      a11 = a1 + f11;
      a21 = a2 + f12;
      a31 = a3 + f13;
      a41 = a4 + f14;
      a02 = r0 * a01;
      a12 = r11 * a01;
      a22 = r2 * a01;
      a32 = r3 * a01;
      a42 = r4 * a01;
      a03 = a02 + r54 * a11;
      a13 = a12 + r0 * a11;
      a23 = a22 + r11 * a11;
      a33 = a32 + r2 * a11;
      a43 = a42 + r3 * a11;
      a04 = a03 + r53 * a21;
      a14 = a13 + r54 * a21;
      a24 = a23 + r0 * a21;
      a34 = a33 + r11 * a21;
      a44 = a43 + r2 * a21;
      a05 = a04 + r52 * a31;
      a15 = a14 + r53 * a31;
      a25 = a24 + r54 * a31;
      a35 = a34 + r0 * a31;
      a45 = a44 + r11 * a31;
      a06 = a05 + r51 * a41;
      a16 = a15 + r52 * a41;
      a26 = a25 + r53 * a41;
      a36 = a35 + r54 * a41;
      a46 = a45 + r0 * a41;
      t0 = a06;
      t1 = a16;
      t2 = a26;
      t3 = a36;
      t4 = a46;
      mask26 = (u64)0x3ffffffU;
      z0 = t0 >> (u32)26U;
      z1 = t3 >> (u32)26U;
      x0 = t0 & mask26;
      x3 = t3 & mask26;
      x1 = t1 + z0;
      x4 = t4 + z1;
      z01 = x1 >> (u32)26U;
      z11 = x4 >> (u32)26U;
      t = z11 << (u32)2U;
      z12 = z11 + t;
      x11 = x1 & mask26;
      x41 = x4 & mask26;
      x2 = t2 + z01;
      x01 = x0 + z12;
      z02 = x2 >> (u32)26U;
      z13 = x01 >> (u32)26U;
      x21 = x2 & mask26;
      x02 = x01 & mask26;
      x31 = x3 + z02;
      x12 = x11 + z13;
      z03 = x31 >> (u32)26U;
      x32 = x31 & mask26;
      x42 = x41 + z03;
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

static inline void poly1305_do_32(u8 *k, u32 aadlen, u8 *aad, u32 mlen, u8 *m, u8 *out)
{
  u64 ctx[25U] = { 0U };
  u8 block[16U] = { 0U };
  u64 *pre;
  u64 *acc;
  Hacl_Poly1305_32_poly1305_init(ctx, k);
  poly1305_padded_32(ctx, aadlen, aad);
  poly1305_padded_32(ctx, mlen, m);
  store64_le(block, (u64)aadlen);
  store64_le(block + (u32)8U, (u64)mlen);
  pre = ctx + (u32)5U;
  acc = ctx;
  {
    u64 e[5U] = { 0U };
    u64 u0 = load64_le(block);
    u64 lo = u0;
    u64 u = load64_le(block + (u32)8U);
    u64 hi = u;
    u64 f0 = lo;
    u64 f1 = hi;
    u64 f010 = f0 & (u64)0x3ffffffU;
    u64 f110 = f0 >> (u32)26U & (u64)0x3ffffffU;
    u64 f20 = f0 >> (u32)52U | (f1 & (u64)0x3fffU) << (u32)12U;
    u64 f30 = f1 >> (u32)14U & (u64)0x3ffffffU;
    u64 f40 = f1 >> (u32)40U;
    u64 f01 = f010;
    u64 f111 = f110;
    u64 f2 = f20;
    u64 f3 = f30;
    u64 f41 = f40;
    u64 b;
    u64 mask;
    u64 f4;
    u64 *r;
    u64 *r5;
    u64 r0;
    u64 r1;
    u64 r2;
    u64 r3;
    u64 r4;
    u64 r51;
    u64 r52;
    u64 r53;
    u64 r54;
    u64 f10;
    u64 f11;
    u64 f12;
    u64 f13;
    u64 f14;
    u64 a0;
    u64 a1;
    u64 a2;
    u64 a3;
    u64 a4;
    u64 a01;
    u64 a11;
    u64 a21;
    u64 a31;
    u64 a41;
    u64 a02;
    u64 a12;
    u64 a22;
    u64 a32;
    u64 a42;
    u64 a03;
    u64 a13;
    u64 a23;
    u64 a33;
    u64 a43;
    u64 a04;
    u64 a14;
    u64 a24;
    u64 a34;
    u64 a44;
    u64 a05;
    u64 a15;
    u64 a25;
    u64 a35;
    u64 a45;
    u64 a06;
    u64 a16;
    u64 a26;
    u64 a36;
    u64 a46;
    u64 t0;
    u64 t1;
    u64 t2;
    u64 t3;
    u64 t4;
    u64 mask26;
    u64 z0;
    u64 z1;
    u64 x0;
    u64 x3;
    u64 x1;
    u64 x4;
    u64 z01;
    u64 z11;
    u64 t;
    u64 z12;
    u64 x11;
    u64 x41;
    u64 x2;
    u64 x01;
    u64 z02;
    u64 z13;
    u64 x21;
    u64 x02;
    u64 x31;
    u64 x12;
    u64 z03;
    u64 x32;
    u64 x42;
    u64 o0;
    u64 o1;
    u64 o2;
    u64 o3;
    u64 o4;
    e[0U] = f01;
    e[1U] = f111;
    e[2U] = f2;
    e[3U] = f3;
    e[4U] = f41;
    b = (u64)0x1000000U;
    mask = b;
    f4 = e[4U];
    e[4U] = f4 | mask;
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
    a01 = a0 + f10;
    a11 = a1 + f11;
    a21 = a2 + f12;
    a31 = a3 + f13;
    a41 = a4 + f14;
    a02 = r0 * a01;
    a12 = r1 * a01;
    a22 = r2 * a01;
    a32 = r3 * a01;
    a42 = r4 * a01;
    a03 = a02 + r54 * a11;
    a13 = a12 + r0 * a11;
    a23 = a22 + r1 * a11;
    a33 = a32 + r2 * a11;
    a43 = a42 + r3 * a11;
    a04 = a03 + r53 * a21;
    a14 = a13 + r54 * a21;
    a24 = a23 + r0 * a21;
    a34 = a33 + r1 * a21;
    a44 = a43 + r2 * a21;
    a05 = a04 + r52 * a31;
    a15 = a14 + r53 * a31;
    a25 = a24 + r54 * a31;
    a35 = a34 + r0 * a31;
    a45 = a44 + r1 * a31;
    a06 = a05 + r51 * a41;
    a16 = a15 + r52 * a41;
    a26 = a25 + r53 * a41;
    a36 = a35 + r54 * a41;
    a46 = a45 + r0 * a41;
    t0 = a06;
    t1 = a16;
    t2 = a26;
    t3 = a36;
    t4 = a46;
    mask26 = (u64)0x3ffffffU;
    z0 = t0 >> (u32)26U;
    z1 = t3 >> (u32)26U;
    x0 = t0 & mask26;
    x3 = t3 & mask26;
    x1 = t1 + z0;
    x4 = t4 + z1;
    z01 = x1 >> (u32)26U;
    z11 = x4 >> (u32)26U;
    t = z11 << (u32)2U;
    z12 = z11 + t;
    x11 = x1 & mask26;
    x41 = x4 & mask26;
    x2 = t2 + z01;
    x01 = x0 + z12;
    z02 = x2 >> (u32)26U;
    z13 = x01 >> (u32)26U;
    x21 = x2 & mask26;
    x02 = x01 & mask26;
    x31 = x3 + z02;
    x12 = x11 + z13;
    z03 = x31 >> (u32)26U;
    x32 = x31 & mask26;
    x42 = x41 + z03;
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
    Hacl_Poly1305_32_poly1305_finish(out, k, ctx);
  }
}

void
Hacl_Chacha20Poly1305_32_aead_encrypt(
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
  Hacl_Chacha20_chacha20_encrypt(mlen, cipher, m, k, n, (u32)1U);
  {
    u8 tmp[64U] = { 0U };
    u8 *key;
    Hacl_Chacha20_chacha20_encrypt((u32)64U, tmp, tmp, k, n, (u32)0U);
    key = tmp;
    poly1305_do_32(key, aadlen, aad, mlen, cipher, mac);
  }
}

u32
Hacl_Chacha20Poly1305_32_aead_decrypt(
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
  Hacl_Chacha20_chacha20_encrypt((u32)64U, tmp, tmp, k, n, (u32)0U);
  key = tmp;
  poly1305_do_32(key, aadlen, aad, mlen, cipher, computed_mac);
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
      Hacl_Chacha20_chacha20_encrypt(mlen, m, cipher, k, n, (u32)1U);
      res = (u32)0U;
    }
    else
      res = (u32)1U;
    return res;
  }
}

