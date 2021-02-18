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


#include "Hacl_Curve25519_64_Slow.h"

static inline u64 add1_(u64 *out, u64 *f1, u64 f2)
{
  u64 c0 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, f1[0U], f2, out);
  if ((u32)1U < (u32)4U)
  {
    u32 rLen = (u32)3U;
    u64 *a1 = f1 + (u32)1U;
    u64 *res1 = out + (u32)1U;
    u64 c = c0;
    {
      u32 i;
      for (i = (u32)0U; i < rLen / (u32)4U * (u32)4U / (u32)4U; i++)
      {
        u64 t1 = a1[(u32)4U * i];
        u64 *res_i0 = res1 + (u32)4U * i;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (u64)0U, res_i0);
        {
          u64 t10 = a1[(u32)4U * i + (u32)1U];
          u64 *res_i1 = res1 + (u32)4U * i + (u32)1U;
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, (u64)0U, res_i1);
          {
            u64 t11 = a1[(u32)4U * i + (u32)2U];
            u64 *res_i2 = res1 + (u32)4U * i + (u32)2U;
            c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (u64)0U, res_i2);
            {
              u64 t12 = a1[(u32)4U * i + (u32)3U];
              u64 *res_i = res1 + (u32)4U * i + (u32)3U;
              c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, (u64)0U, res_i);
            }
          }
        }
      }
    }
    {
      u32 i;
      for (i = rLen / (u32)4U * (u32)4U; i < rLen; i++)
      {
        u64 t1 = a1[i];
        u64 *res_i = res1 + i;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (u64)0U, res_i);
      }
    }
    {
      u64 c1 = c;
      return c1;
    }
  }
  return c0;
}

static inline void fadd_(u64 *out, u64 *f1, u64 *f2)
{
  u64 c1 = (u64)0U;
  u64 c0;
  u64 c01;
  u64 c2;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)1U; i++)
    {
      u64 t1 = f1[(u32)4U * i];
      u64 t20 = f2[(u32)4U * i];
      u64 *res_i0 = out + (u32)4U * i;
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t20, res_i0);
      {
        u64 t10 = f1[(u32)4U * i + (u32)1U];
        u64 t21 = f2[(u32)4U * i + (u32)1U];
        u64 *res_i1 = out + (u32)4U * i + (u32)1U;
        c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t10, t21, res_i1);
        {
          u64 t11 = f1[(u32)4U * i + (u32)2U];
          u64 t22 = f2[(u32)4U * i + (u32)2U];
          u64 *res_i2 = out + (u32)4U * i + (u32)2U;
          c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t11, t22, res_i2);
          {
            u64 t12 = f1[(u32)4U * i + (u32)3U];
            u64 t2 = f2[(u32)4U * i + (u32)3U];
            u64 *res_i = out + (u32)4U * i + (u32)3U;
            c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t12, t2, res_i);
          }
        }
      }
    }
  }
  {
    u32 i;
    for (i = (u32)4U; i < (u32)4U; i++)
    {
      u64 t1 = f1[i];
      u64 t2 = f2[i];
      u64 *res_i = out + i;
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t2, res_i);
    }
  }
  c0 = c1;
  c01 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, out[0U], c0 * (u64)38U, out);
  if ((u32)1U < (u32)4U)
  {
    u32 rLen = (u32)3U;
    u64 *a1 = out + (u32)1U;
    u64 *res1 = out + (u32)1U;
    u64 c = c01;
    {
      u32 i;
      for (i = (u32)0U; i < rLen / (u32)4U * (u32)4U / (u32)4U; i++)
      {
        u64 t1 = a1[(u32)4U * i];
        u64 *res_i0 = res1 + (u32)4U * i;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (u64)0U, res_i0);
        {
          u64 t10 = a1[(u32)4U * i + (u32)1U];
          u64 *res_i1 = res1 + (u32)4U * i + (u32)1U;
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, (u64)0U, res_i1);
          {
            u64 t11 = a1[(u32)4U * i + (u32)2U];
            u64 *res_i2 = res1 + (u32)4U * i + (u32)2U;
            c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (u64)0U, res_i2);
            {
              u64 t12 = a1[(u32)4U * i + (u32)3U];
              u64 *res_i = res1 + (u32)4U * i + (u32)3U;
              c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, (u64)0U, res_i);
            }
          }
        }
      }
    }
    {
      u32 i;
      for (i = rLen / (u32)4U * (u32)4U; i < rLen; i++)
      {
        u64 t1 = a1[i];
        u64 *res_i = res1 + i;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (u64)0U, res_i);
      }
    }
    {
      u64 c10 = c;
      c2 = c10;
    }
  }
  else
    c2 = c01;
  out[0U] = out[0U] + c2 * (u64)38U;
}

static inline void fsub_(u64 *out, u64 *f1, u64 *f2)
{
  u64 c1 = (u64)0U;
  u64 c0;
  u64 c01;
  u64 c2;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)1U; i++)
    {
      u64 t1 = f1[(u32)4U * i];
      u64 t20 = f2[(u32)4U * i];
      u64 *res_i0 = out + (u32)4U * i;
      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, res_i0);
      {
        u64 t10 = f1[(u32)4U * i + (u32)1U];
        u64 t21 = f2[(u32)4U * i + (u32)1U];
        u64 *res_i1 = out + (u32)4U * i + (u32)1U;
        c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t10, t21, res_i1);
        {
          u64 t11 = f1[(u32)4U * i + (u32)2U];
          u64 t22 = f2[(u32)4U * i + (u32)2U];
          u64 *res_i2 = out + (u32)4U * i + (u32)2U;
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t11, t22, res_i2);
          {
            u64 t12 = f1[(u32)4U * i + (u32)3U];
            u64 t2 = f2[(u32)4U * i + (u32)3U];
            u64 *res_i = out + (u32)4U * i + (u32)3U;
            c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t12, t2, res_i);
          }
        }
      }
    }
  }
  {
    u32 i;
    for (i = (u32)4U; i < (u32)4U; i++)
    {
      u64 t1 = f1[i];
      u64 t2 = f2[i];
      u64 *res_i = out + i;
      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, res_i);
    }
  }
  c0 = c1;
  c01 = Lib_IntTypes_Intrinsics_sub_borrow_u64((u64)0U, out[0U], c0 * (u64)38U, out);
  if ((u32)1U < (u32)4U)
  {
    u32 rLen = (u32)3U;
    u64 *a1 = out + (u32)1U;
    u64 *res1 = out + (u32)1U;
    u64 c = c01;
    {
      u32 i;
      for (i = (u32)0U; i < rLen / (u32)4U * (u32)4U / (u32)4U; i++)
      {
        u64 t1 = a1[(u32)4U * i];
        u64 *res_i0 = res1 + (u32)4U * i;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, (u64)0U, res_i0);
        {
          u64 t10 = a1[(u32)4U * i + (u32)1U];
          u64 *res_i1 = res1 + (u32)4U * i + (u32)1U;
          c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, (u64)0U, res_i1);
          {
            u64 t11 = a1[(u32)4U * i + (u32)2U];
            u64 *res_i2 = res1 + (u32)4U * i + (u32)2U;
            c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, (u64)0U, res_i2);
            {
              u64 t12 = a1[(u32)4U * i + (u32)3U];
              u64 *res_i = res1 + (u32)4U * i + (u32)3U;
              c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, (u64)0U, res_i);
            }
          }
        }
      }
    }
    {
      u32 i;
      for (i = rLen / (u32)4U * (u32)4U; i < rLen; i++)
      {
        u64 t1 = a1[i];
        u64 *res_i = res1 + i;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, (u64)0U, res_i);
      }
    }
    {
      u64 c10 = c;
      c2 = c10;
    }
  }
  else
    c2 = c01;
  out[0U] = out[0U] - c2 * (u64)38U;
}

static inline void fmul_(u64 *out, u64 *f1, u64 *f2, u64 *tmp)
{
  u64 *tmp0 = tmp;
  u32 resLen = (u32)8U;
  u64 *uu____0;
  u64 *uu____1;
  u64 *res_j0;
  memset(tmp0, 0U, resLen * sizeof (u64));
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < (u32)4U; i0++)
    {
      u64 bj = f2[i0];
      u64 *res_j = tmp0 + i0;
      u64 c = (u64)0U;
      {
        u32 i;
        for (i = (u32)0U; i < (u32)1U; i++)
        {
          u64 a_i = f1[(u32)4U * i];
          u64 *res_i0 = res_j + (u32)4U * i;
          c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i0);
          {
            u64 a_i0 = f1[(u32)4U * i + (u32)1U];
            u64 *res_i1 = res_j + (u32)4U * i + (u32)1U;
            c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c, res_i1);
            {
              u64 a_i1 = f1[(u32)4U * i + (u32)2U];
              u64 *res_i2 = res_j + (u32)4U * i + (u32)2U;
              c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c, res_i2);
              {
                u64 a_i2 = f1[(u32)4U * i + (u32)3U];
                u64 *res_i = res_j + (u32)4U * i + (u32)3U;
                c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c, res_i);
              }
            }
          }
        }
      }
      {
        u32 i;
        for (i = (u32)4U; i < (u32)4U; i++)
        {
          u64 a_i = f1[i];
          u64 *res_i = res_j + i;
          c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i);
        }
      }
      {
        u64 r = c;
        tmp0[(u32)4U + i0] = r;
      }
    }
  }
  uu____0 = tmp0 + (u32)4U;
  uu____1 = tmp0;
  res_j0 = uu____1;
  {
    u64 c1 = (u64)0U;
    u64 r;
    u64 c0;
    u64 *uu____2;
    u64 c01;
    u64 c2;
    {
      u32 i;
      for (i = (u32)0U; i < (u32)1U; i++)
      {
        u64 a_i = uu____0[(u32)4U * i];
        u64 *res_i0 = res_j0 + (u32)4U * i;
        c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, (u64)38U, c1, res_i0);
        {
          u64 a_i0 = uu____0[(u32)4U * i + (u32)1U];
          u64 *res_i1 = res_j0 + (u32)4U * i + (u32)1U;
          c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, (u64)38U, c1, res_i1);
          {
            u64 a_i1 = uu____0[(u32)4U * i + (u32)2U];
            u64 *res_i2 = res_j0 + (u32)4U * i + (u32)2U;
            c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, (u64)38U, c1, res_i2);
            {
              u64 a_i2 = uu____0[(u32)4U * i + (u32)3U];
              u64 *res_i = res_j0 + (u32)4U * i + (u32)3U;
              c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, (u64)38U, c1, res_i);
            }
          }
        }
      }
    }
    {
      u32 i;
      for (i = (u32)4U; i < (u32)4U; i++)
      {
        u64 a_i = uu____0[i];
        u64 *res_i = res_j0 + i;
        c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, (u64)38U, c1, res_i);
      }
    }
    r = c1;
    c0 = r;
    uu____2 = tmp0;
    c01 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, uu____2[0U], c0 * (u64)38U, out);
    if ((u32)1U < (u32)4U)
    {
      u32 rLen = (u32)3U;
      u64 *a1 = uu____2 + (u32)1U;
      u64 *res1 = out + (u32)1U;
      u64 c = c01;
      {
        u32 i;
        for (i = (u32)0U; i < rLen / (u32)4U * (u32)4U / (u32)4U; i++)
        {
          u64 t1 = a1[(u32)4U * i];
          u64 *res_i0 = res1 + (u32)4U * i;
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (u64)0U, res_i0);
          {
            u64 t10 = a1[(u32)4U * i + (u32)1U];
            u64 *res_i1 = res1 + (u32)4U * i + (u32)1U;
            c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, (u64)0U, res_i1);
            {
              u64 t11 = a1[(u32)4U * i + (u32)2U];
              u64 *res_i2 = res1 + (u32)4U * i + (u32)2U;
              c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (u64)0U, res_i2);
              {
                u64 t12 = a1[(u32)4U * i + (u32)3U];
                u64 *res_i = res1 + (u32)4U * i + (u32)3U;
                c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, (u64)0U, res_i);
              }
            }
          }
        }
      }
      {
        u32 i;
        for (i = rLen / (u32)4U * (u32)4U; i < rLen; i++)
        {
          u64 t1 = a1[i];
          u64 *res_i = res1 + i;
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (u64)0U, res_i);
        }
      }
      {
        u64 c10 = c;
        c2 = c10;
      }
    }
    else
      c2 = c01;
    out[0U] = out[0U] + c2 * (u64)38U;
  }
}

static inline void fmul2_(u64 *out, u64 *f1, u64 *f2, u64 *tmp)
{
  u64 *out1 = out;
  u64 *out2 = out + (u32)4U;
  u64 *f11 = f1;
  u64 *f12 = f1 + (u32)4U;
  u64 *f21 = f2;
  u64 *f22 = f2 + (u32)4U;
  fmul_(out1, f11, f21, tmp);
  fmul_(out2, f12, f22, tmp);
}

static inline void fmul1_(u64 *out, u64 *f1, u64 f2)
{
  u64 c1 = (u64)0U;
  u64 c0;
  u64 c01;
  u64 c2;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)1U; i++)
    {
      u64 a_i = f1[(u32)4U * i];
      u64 *res_i0 = out + (u32)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add_u64(a_i, f2, c1, res_i0);
      {
        u64 a_i0 = f1[(u32)4U * i + (u32)1U];
        u64 *res_i1 = out + (u32)4U * i + (u32)1U;
        c1 = Hacl_Bignum_Base_mul_wide_add_u64(a_i0, f2, c1, res_i1);
        {
          u64 a_i1 = f1[(u32)4U * i + (u32)2U];
          u64 *res_i2 = out + (u32)4U * i + (u32)2U;
          c1 = Hacl_Bignum_Base_mul_wide_add_u64(a_i1, f2, c1, res_i2);
          {
            u64 a_i2 = f1[(u32)4U * i + (u32)3U];
            u64 *res_i = out + (u32)4U * i + (u32)3U;
            c1 = Hacl_Bignum_Base_mul_wide_add_u64(a_i2, f2, c1, res_i);
          }
        }
      }
    }
  }
  {
    u32 i;
    for (i = (u32)4U; i < (u32)4U; i++)
    {
      u64 a_i = f1[i];
      u64 *res_i = out + i;
      c1 = Hacl_Bignum_Base_mul_wide_add_u64(a_i, f2, c1, res_i);
    }
  }
  c0 = c1;
  c01 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, out[0U], c0 * (u64)38U, out);
  if ((u32)1U < (u32)4U)
  {
    u32 rLen = (u32)3U;
    u64 *a1 = out + (u32)1U;
    u64 *res1 = out + (u32)1U;
    u64 c = c01;
    {
      u32 i;
      for (i = (u32)0U; i < rLen / (u32)4U * (u32)4U / (u32)4U; i++)
      {
        u64 t1 = a1[(u32)4U * i];
        u64 *res_i0 = res1 + (u32)4U * i;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (u64)0U, res_i0);
        {
          u64 t10 = a1[(u32)4U * i + (u32)1U];
          u64 *res_i1 = res1 + (u32)4U * i + (u32)1U;
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, (u64)0U, res_i1);
          {
            u64 t11 = a1[(u32)4U * i + (u32)2U];
            u64 *res_i2 = res1 + (u32)4U * i + (u32)2U;
            c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (u64)0U, res_i2);
            {
              u64 t12 = a1[(u32)4U * i + (u32)3U];
              u64 *res_i = res1 + (u32)4U * i + (u32)3U;
              c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, (u64)0U, res_i);
            }
          }
        }
      }
    }
    {
      u32 i;
      for (i = rLen / (u32)4U * (u32)4U; i < rLen; i++)
      {
        u64 t1 = a1[i];
        u64 *res_i = res1 + i;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (u64)0U, res_i);
      }
    }
    {
      u64 c10 = c;
      c2 = c10;
    }
  }
  else
    c2 = c01;
  out[0U] = out[0U] + c2 * (u64)38U;
}

static inline void fsqr_(u64 *out, u64 *f1, u64 *tmp)
{
  u32 resLen = (u32)8U;
  u64 c00;
  memset(tmp, 0U, resLen * sizeof (u64));
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < (u32)4U; i0++)
    {
      u64 *ab = f1;
      u64 a_j = f1[i0];
      u64 *res_j = tmp + i0;
      u64 c = (u64)0U;
      {
        u32 i;
        for (i = (u32)0U; i < i0 / (u32)4U * (u32)4U / (u32)4U; i++)
        {
          u64 a_i = ab[(u32)4U * i];
          u64 *res_i0 = res_j + (u32)4U * i;
          c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c, res_i0);
          {
            u64 a_i0 = ab[(u32)4U * i + (u32)1U];
            u64 *res_i1 = res_j + (u32)4U * i + (u32)1U;
            c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, a_j, c, res_i1);
            {
              u64 a_i1 = ab[(u32)4U * i + (u32)2U];
              u64 *res_i2 = res_j + (u32)4U * i + (u32)2U;
              c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, a_j, c, res_i2);
              {
                u64 a_i2 = ab[(u32)4U * i + (u32)3U];
                u64 *res_i = res_j + (u32)4U * i + (u32)3U;
                c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, a_j, c, res_i);
              }
            }
          }
        }
      }
      {
        u32 i;
        for (i = i0 / (u32)4U * (u32)4U; i < i0; i++)
        {
          u64 a_i = ab[i];
          u64 *res_i = res_j + i;
          c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c, res_i);
        }
      }
      {
        u64 r = c;
        tmp[i0 + i0] = r;
      }
    }
  }
  c00 = Hacl_Bignum_Addition_bn_add_eq_len_u64(resLen, tmp, tmp, tmp);
  KRML_CHECK_SIZE(sizeof (u64), resLen);
  {
    u64 tmp1[resLen];
    memset(tmp1, 0U, resLen * sizeof (u64));
    {
      u64 c1;
      u64 *uu____0;
      u64 *uu____1;
      u64 *res_j;
      {
        u32 i;
        for (i = (u32)0U; i < (u32)4U; i++)
        {
          uint128_t res = (uint128_t)f1[i] * f1[i];
          u64 hi = (uint64_t)(res >> (u32)64U);
          u64 lo = (uint64_t)res;
          tmp1[(u32)2U * i] = lo;
          tmp1[(u32)2U * i + (u32)1U] = hi;
        }
      }
      c1 = Hacl_Bignum_Addition_bn_add_eq_len_u64(resLen, tmp, tmp1, tmp);
      uu____0 = tmp + (u32)4U;
      uu____1 = tmp;
      res_j = uu____1;
      {
        u64 c2 = (u64)0U;
        u64 r;
        u64 c0;
        u64 *uu____2;
        u64 c01;
        u64 c3;
        {
          u32 i;
          for (i = (u32)0U; i < (u32)1U; i++)
          {
            u64 a_i = uu____0[(u32)4U * i];
            u64 *res_i0 = res_j + (u32)4U * i;
            c2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, (u64)38U, c2, res_i0);
            {
              u64 a_i0 = uu____0[(u32)4U * i + (u32)1U];
              u64 *res_i1 = res_j + (u32)4U * i + (u32)1U;
              c2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, (u64)38U, c2, res_i1);
              {
                u64 a_i1 = uu____0[(u32)4U * i + (u32)2U];
                u64 *res_i2 = res_j + (u32)4U * i + (u32)2U;
                c2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, (u64)38U, c2, res_i2);
                {
                  u64 a_i2 = uu____0[(u32)4U * i + (u32)3U];
                  u64 *res_i = res_j + (u32)4U * i + (u32)3U;
                  c2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, (u64)38U, c2, res_i);
                }
              }
            }
          }
        }
        {
          u32 i;
          for (i = (u32)4U; i < (u32)4U; i++)
          {
            u64 a_i = uu____0[i];
            u64 *res_i = res_j + i;
            c2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, (u64)38U, c2, res_i);
          }
        }
        r = c2;
        c0 = r;
        uu____2 = tmp;
        c01 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, uu____2[0U], c0 * (u64)38U, out);
        if ((u32)1U < (u32)4U)
        {
          u32 rLen = (u32)3U;
          u64 *a1 = uu____2 + (u32)1U;
          u64 *res1 = out + (u32)1U;
          u64 c = c01;
          {
            u32 i;
            for (i = (u32)0U; i < rLen / (u32)4U * (u32)4U / (u32)4U; i++)
            {
              u64 t1 = a1[(u32)4U * i];
              u64 *res_i0 = res1 + (u32)4U * i;
              c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (u64)0U, res_i0);
              {
                u64 t10 = a1[(u32)4U * i + (u32)1U];
                u64 *res_i1 = res1 + (u32)4U * i + (u32)1U;
                c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, (u64)0U, res_i1);
                {
                  u64 t11 = a1[(u32)4U * i + (u32)2U];
                  u64 *res_i2 = res1 + (u32)4U * i + (u32)2U;
                  c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (u64)0U, res_i2);
                  {
                    u64 t12 = a1[(u32)4U * i + (u32)3U];
                    u64 *res_i = res1 + (u32)4U * i + (u32)3U;
                    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, (u64)0U, res_i);
                  }
                }
              }
            }
          }
          {
            u32 i;
            for (i = rLen / (u32)4U * (u32)4U; i < rLen; i++)
            {
              u64 t1 = a1[i];
              u64 *res_i = res1 + i;
              c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (u64)0U, res_i);
            }
          }
          {
            u64 c10 = c;
            c3 = c10;
          }
        }
        else
          c3 = c01;
        out[0U] = out[0U] + c3 * (u64)38U;
      }
    }
  }
}

static inline void fsqr2_(u64 *out, u64 *f, u64 *tmp)
{
  u64 *out1 = out;
  u64 *out2 = out + (u32)4U;
  u64 *f1 = f;
  u64 *f2 = f + (u32)4U;
  fmul_(out1, f1, f1, tmp);
  fmul_(out2, f2, f2, tmp);
}

static inline void cswap2_(u64 bit, u64 *p1, u64 *p2)
{
  u64 mask = (u64)0U - bit;
  u32 i;
  for (i = (u32)0U; i < (u32)8U; i++)
  {
    u64 dummy = mask & (p1[i] ^ p2[i]);
    p1[i] = p1[i] ^ dummy;
    p2[i] = p2[i] ^ dummy;
  }
}

static const u8 g25519[32U] = { (u8)9U };

static void point_add_and_double(u64 *q, u64 *p01_tmp1, u64 *tmp2)
{
  u64 *nq = p01_tmp1;
  u64 *nq_p1 = p01_tmp1 + (u32)8U;
  u64 *tmp1 = p01_tmp1 + (u32)16U;
  u64 *x1 = q;
  u64 *x2 = nq;
  u64 *z2 = nq + (u32)4U;
  u64 *z3 = nq_p1 + (u32)4U;
  u64 *a = tmp1;
  u64 *b = tmp1 + (u32)4U;
  u64 *ab = tmp1;
  u64 *dc = tmp1 + (u32)8U;
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
  fadd_(a, x2, z2);
  fsub_(b, x2, z2);
  x3 = nq_p1;
  z31 = nq_p1 + (u32)4U;
  d0 = dc;
  c0 = dc + (u32)4U;
  fadd_(c0, x3, z31);
  fsub_(d0, x3, z31);
  fmul2_(dc, dc, ab, tmp2);
  fadd_(x3, d0, c0);
  fsub_(z31, d0, c0);
  a1 = tmp1;
  b1 = tmp1 + (u32)4U;
  d = tmp1 + (u32)8U;
  c = tmp1 + (u32)12U;
  ab1 = tmp1;
  dc1 = tmp1 + (u32)8U;
  fsqr2_(dc1, ab1, tmp2);
  fsqr2_(nq_p1, nq_p1, tmp2);
  a1[0U] = c[0U];
  a1[1U] = c[1U];
  a1[2U] = c[2U];
  a1[3U] = c[3U];
  fsub_(c, d, c);
  fmul1_(b1, c, (u64)121665U);
  fadd_(b1, b1, d);
  fmul2_(nq, dc1, ab1, tmp2);
  fmul_(z3, z3, x1, tmp2);
}

static void point_double(u64 *nq, u64 *tmp1, u64 *tmp2)
{
  u64 *x2 = nq;
  u64 *z2 = nq + (u32)4U;
  u64 *a = tmp1;
  u64 *b = tmp1 + (u32)4U;
  u64 *d = tmp1 + (u32)8U;
  u64 *c = tmp1 + (u32)12U;
  u64 *ab = tmp1;
  u64 *dc = tmp1 + (u32)8U;
  fadd_(a, x2, z2);
  fsub_(b, x2, z2);
  fsqr2_(dc, ab, tmp2);
  a[0U] = c[0U];
  a[1U] = c[1U];
  a[2U] = c[2U];
  a[3U] = c[3U];
  fsub_(c, d, c);
  fmul1_(b, c, (u64)121665U);
  fadd_(b, b, d);
  fmul2_(nq, dc, ab, tmp2);
}

static void montgomery_ladder(u64 *out, u8 *key, u64 *init)
{
  u64 tmp2[16U] = { 0U };
  u64 p01_tmp1_swap[33U] = { 0U };
  u64 *p0 = p01_tmp1_swap;
  u64 *p01 = p01_tmp1_swap;
  u64 *p03 = p01;
  u64 *p11 = p01 + (u32)8U;
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
  memcpy(p11, init, (u32)8U * sizeof (u64));
  x0 = p03;
  z0 = p03 + (u32)4U;
  x0[0U] = (u64)1U;
  x0[1U] = (u64)0U;
  x0[2U] = (u64)0U;
  x0[3U] = (u64)0U;
  z0[0U] = (u64)0U;
  z0[1U] = (u64)0U;
  z0[2U] = (u64)0U;
  z0[3U] = (u64)0U;
  p01_tmp1 = p01_tmp1_swap;
  p01_tmp11 = p01_tmp1_swap;
  nq10 = p01_tmp1_swap;
  nq_p11 = p01_tmp1_swap + (u32)8U;
  swap = p01_tmp1_swap + (u32)32U;
  cswap2_((u64)1U, nq10, nq_p11);
  point_add_and_double(init, p01_tmp11, tmp2);
  swap[0U] = (u64)1U;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)251U; i++)
    {
      u64 *p01_tmp12 = p01_tmp1_swap;
      u64 *swap1 = p01_tmp1_swap + (u32)32U;
      u64 *nq2 = p01_tmp12;
      u64 *nq_p12 = p01_tmp12 + (u32)8U;
      u64 bit = (u64)(key[((u32)253U - i) / (u32)8U] >> ((u32)253U - i) % (u32)8U & (u8)1U);
      u64 sw = swap1[0U] ^ bit;
      cswap2_(sw, nq2, nq_p12);
      point_add_and_double(init, p01_tmp12, tmp2);
      swap1[0U] = bit;
    }
  }
  sw0 = swap[0U];
  cswap2_(sw0, nq10, nq_p11);
  nq1 = p01_tmp1;
  tmp1 = p01_tmp1 + (u32)16U;
  point_double(nq1, tmp1, tmp2);
  point_double(nq1, tmp1, tmp2);
  point_double(nq1, tmp1, tmp2);
  memcpy(out, p0, (u32)8U * sizeof (u64));
}

static void fsquare_times(u64 *o, u64 *inp, u64 *tmp, u32 n)
{
  u32 i;
  fsqr_(o, inp, tmp);
  for (i = (u32)0U; i < n - (u32)1U; i++)
    fsqr_(o, o, tmp);
}

static void finv(u64 *o, u64 *i, u64 *tmp)
{
  u64 t1[16U] = { 0U };
  u64 *a1 = t1;
  u64 *b10 = t1 + (u32)4U;
  u64 *t010 = t1 + (u32)12U;
  u64 *tmp10 = tmp;
  u64 *b11;
  u64 *c10;
  u64 *t011;
  u64 *tmp11;
  u64 *b1;
  u64 *c1;
  u64 *t01;
  u64 *tmp1;
  u64 *a;
  u64 *t0;
  fsquare_times(a1, i, tmp10, (u32)1U);
  fsquare_times(t010, a1, tmp10, (u32)2U);
  fmul_(b10, t010, i, tmp);
  fmul_(a1, b10, a1, tmp);
  fsquare_times(t010, a1, tmp10, (u32)1U);
  fmul_(b10, t010, b10, tmp);
  fsquare_times(t010, b10, tmp10, (u32)5U);
  fmul_(b10, t010, b10, tmp);
  b11 = t1 + (u32)4U;
  c10 = t1 + (u32)8U;
  t011 = t1 + (u32)12U;
  tmp11 = tmp;
  fsquare_times(t011, b11, tmp11, (u32)10U);
  fmul_(c10, t011, b11, tmp);
  fsquare_times(t011, c10, tmp11, (u32)20U);
  fmul_(t011, t011, c10, tmp);
  fsquare_times(t011, t011, tmp11, (u32)10U);
  fmul_(b11, t011, b11, tmp);
  fsquare_times(t011, b11, tmp11, (u32)50U);
  fmul_(c10, t011, b11, tmp);
  b1 = t1 + (u32)4U;
  c1 = t1 + (u32)8U;
  t01 = t1 + (u32)12U;
  tmp1 = tmp;
  fsquare_times(t01, c1, tmp1, (u32)100U);
  fmul_(t01, t01, c1, tmp);
  fsquare_times(t01, t01, tmp1, (u32)50U);
  fmul_(t01, t01, b1, tmp);
  fsquare_times(t01, t01, tmp1, (u32)5U);
  a = t1;
  t0 = t1 + (u32)12U;
  fmul_(o, t0, a, tmp);
}

static void store_felem(u64 *b, u64 *f)
{
  u64 f30 = f[3U];
  u64 top_bit0 = f30 >> (u32)63U;
  u64 carry0;
  u64 f31;
  u64 top_bit;
  u64 carry;
  u64 f0;
  u64 f1;
  u64 f2;
  u64 f3;
  u64 m0;
  u64 m1;
  u64 m2;
  u64 m3;
  u64 mask;
  u64 f0_;
  u64 f1_;
  u64 f2_;
  u64 f3_;
  u64 o0;
  u64 o1;
  u64 o2;
  u64 o3;
  f[3U] = f30 & (u64)0x7fffffffffffffffU;
  carry0 = add1_(f, f, (u64)19U * top_bit0);
  f31 = f[3U];
  top_bit = f31 >> (u32)63U;
  f[3U] = f31 & (u64)0x7fffffffffffffffU;
  carry = add1_(f, f, (u64)19U * top_bit);
  f0 = f[0U];
  f1 = f[1U];
  f2 = f[2U];
  f3 = f[3U];
  m0 = FStar_UInt64_gte_mask(f0, (u64)0xffffffffffffffedU);
  m1 = FStar_UInt64_eq_mask(f1, (u64)0xffffffffffffffffU);
  m2 = FStar_UInt64_eq_mask(f2, (u64)0xffffffffffffffffU);
  m3 = FStar_UInt64_eq_mask(f3, (u64)0x7fffffffffffffffU);
  mask = ((m0 & m1) & m2) & m3;
  f0_ = f0 - (mask & (u64)0xffffffffffffffedU);
  f1_ = f1 - (mask & (u64)0xffffffffffffffffU);
  f2_ = f2 - (mask & (u64)0xffffffffffffffffU);
  f3_ = f3 - (mask & (u64)0x7fffffffffffffffU);
  o0 = f0_;
  o1 = f1_;
  o2 = f2_;
  o3 = f3_;
  b[0U] = o0;
  b[1U] = o1;
  b[2U] = o2;
  b[3U] = o3;
}

static void encode_point(u8 *o, u64 *i)
{
  u64 *x = i;
  u64 *z = i + (u32)4U;
  u64 tmp[4U] = { 0U };
  u64 u64s[4U] = { 0U };
  u64 tmp_w[16U] = { 0U };
  finv(tmp, z, tmp_w);
  fmul_(tmp, tmp, x, tmp_w);
  store_felem(u64s, tmp);
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < (u32)4U; i0++)
      store64_le(o + i0 * (u32)8U, u64s[i0]);
  }
}

void Hacl_Curve25519_64_Slow_scalarmult(u8 *out, u8 *priv, u8 *pub)
{
  u64 init[8U] = { 0U };
  u64 tmp[4U] = { 0U };
  u64 tmp3;
  u64 *x;
  u64 *z;
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
  z = init + (u32)4U;
  z[0U] = (u64)1U;
  z[1U] = (u64)0U;
  z[2U] = (u64)0U;
  z[3U] = (u64)0U;
  x[0U] = tmp[0U];
  x[1U] = tmp[1U];
  x[2U] = tmp[2U];
  x[3U] = tmp[3U];
  montgomery_ladder(init, priv, init);
  encode_point(out, init);
}

void Hacl_Curve25519_64_Slow_secret_to_public(u8 *pub, u8 *priv)
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
  Hacl_Curve25519_64_Slow_scalarmult(pub, priv, basepoint);
}

bool Hacl_Curve25519_64_Slow_ecdh(u8 *out, u8 *priv, u8 *pub)
{
  u8 zeros[32U] = { 0U };
  Hacl_Curve25519_64_Slow_scalarmult(out, priv, pub);
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

