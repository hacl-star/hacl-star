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


#ifndef __Hacl_Frodo_KEM_H
#define __Hacl_Frodo_KEM_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_Kremlib.h"
#include "Lib_RandomBuffer_System.h"
#include "Hacl_Spec.h"
#include "Hacl_SHA3.h"

static inline void
Hacl_Keccak_shake128_4x(
  u32 input_len,
  u8 *input0,
  u8 *input1,
  u8 *input2,
  u8 *input3,
  u32 output_len,
  u8 *output0,
  u8 *output1,
  u8 *output2,
  u8 *output3
)
{
  Hacl_SHA3_shake128_hacl(input_len, input0, output_len, output0);
  Hacl_SHA3_shake128_hacl(input_len, input1, output_len, output1);
  Hacl_SHA3_shake128_hacl(input_len, input2, output_len, output2);
  Hacl_SHA3_shake128_hacl(input_len, input3, output_len, output3);
}

static inline void Hacl_Impl_Matrix_mod_pow2(u32 n1, u32 n2, u32 logq, u16 *a)
{
  if (logq < (u32)16U)
  {
    u32 i;
    for (i = (u32)0U; i < n1; i++)
    {
      u32 i0;
      for (i0 = (u32)0U; i0 < n2; i0++)
        a[i * n2 + i0] = a[i * n2 + i0] & (((u16)1U << logq) - (u16)1U);
    }
    return;
  }
}

static inline void Hacl_Impl_Matrix_matrix_add(u32 n1, u32 n2, u16 *a, u16 *b)
{
  u32 i;
  for (i = (u32)0U; i < n1; i++)
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < n2; i0++)
      a[i * n2 + i0] = a[i * n2 + i0] + b[i * n2 + i0];
  }
}

static inline void Hacl_Impl_Matrix_matrix_sub(u32 n1, u32 n2, u16 *a, u16 *b)
{
  u32 i;
  for (i = (u32)0U; i < n1; i++)
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < n2; i0++)
      b[i * n2 + i0] = a[i * n2 + i0] - b[i * n2 + i0];
  }
}

static inline void Hacl_Impl_Matrix_matrix_mul(u32 n1, u32 n2, u32 n3, u16 *a, u16 *b, u16 *c)
{
  u32 i0;
  for (i0 = (u32)0U; i0 < n1; i0++)
  {
    u32 i1;
    for (i1 = (u32)0U; i1 < n3; i1++)
    {
      u16 res = (u16)0U;
      {
        u32 i;
        for (i = (u32)0U; i < n2; i++)
        {
          u16 aij = a[i0 * n2 + i];
          u16 bjk = b[i * n3 + i1];
          u16 res0 = res;
          res = res0 + aij * bjk;
        }
      }
      c[i0 * n3 + i1] = res;
    }
  }
}

static inline void
Hacl_Impl_Matrix_matrix_mul_s(u32 n1, u32 n2, u32 n3, u16 *a, u16 *b, u16 *c)
{
  u32 i0;
  for (i0 = (u32)0U; i0 < n1; i0++)
  {
    u32 i1;
    for (i1 = (u32)0U; i1 < n3; i1++)
    {
      u16 res = (u16)0U;
      {
        u32 i;
        for (i = (u32)0U; i < n2; i++)
        {
          u16 aij = a[i0 * n2 + i];
          u16 bjk = b[i1 * n2 + i];
          u16 res0 = res;
          res = res0 + aij * bjk;
        }
      }
      c[i0 * n3 + i1] = res;
    }
  }
}

static inline u16 Hacl_Impl_Matrix_matrix_eq(u32 n1, u32 n2, u16 *a, u16 *b)
{
  u16 res = (u16)0xFFFFU;
  u16 r;
  {
    u32 i;
    for (i = (u32)0U; i < n1 * n2; i++)
    {
      u16 uu____0 = FStar_UInt16_eq_mask(a[i], b[i]);
      res = uu____0 & res;
    }
  }
  r = res;
  return r;
}

static inline void Hacl_Impl_Matrix_matrix_to_lbytes(u32 n1, u32 n2, u16 *m, u8 *res)
{
  u32 i;
  for (i = (u32)0U; i < n1 * n2; i++)
    store16_le(res + (u32)2U * i, m[i]);
}

static inline void Hacl_Impl_Matrix_matrix_from_lbytes(u32 n1, u32 n2, u8 *b, u16 *res)
{
  u32 i;
  for (i = (u32)0U; i < n1 * n2; i++)
  {
    u16 *os = res;
    u16 u = load16_le(b + (u32)2U * i);
    u16 x = u;
    os[i] = x;
  }
}

static inline void Hacl_Impl_Frodo_Gen_frodo_gen_matrix_shake_4x(u32 n, u8 *seed, u16 *res)
{
  KRML_CHECK_SIZE(sizeof (u8), (u32)8U * n);
  {
    u8 r[(u32)8U * n];
    memset(r, 0U, (u32)8U * n * sizeof (u8));
    {
      u8 tmp_seed[72U] = { 0U };
      memcpy(tmp_seed + (u32)2U, seed, (u32)16U * sizeof (u8));
      memcpy(tmp_seed + (u32)20U, seed, (u32)16U * sizeof (u8));
      memcpy(tmp_seed + (u32)38U, seed, (u32)16U * sizeof (u8));
      memcpy(tmp_seed + (u32)56U, seed, (u32)16U * sizeof (u8));
      memset(res, 0U, n * n * sizeof (u16));
      {
        u32 i;
        for (i = (u32)0U; i < n / (u32)4U; i++)
        {
          u8 *r0 = r + (u32)0U * n;
          u8 *r1 = r + (u32)2U * n;
          u8 *r2 = r + (u32)4U * n;
          u8 *r3 = r + (u32)6U * n;
          u8 *tmp_seed0 = tmp_seed;
          u8 *tmp_seed1 = tmp_seed + (u32)18U;
          u8 *tmp_seed2 = tmp_seed + (u32)36U;
          u8 *tmp_seed3 = tmp_seed + (u32)54U;
          store16_le(tmp_seed0, (u16)((u32)4U * i + (u32)0U));
          store16_le(tmp_seed1, (u16)((u32)4U * i + (u32)1U));
          store16_le(tmp_seed2, (u16)((u32)4U * i + (u32)2U));
          store16_le(tmp_seed3, (u16)((u32)4U * i + (u32)3U));
          Hacl_Keccak_shake128_4x((u32)18U,
            tmp_seed0,
            tmp_seed1,
            tmp_seed2,
            tmp_seed3,
            (u32)2U * n,
            r0,
            r1,
            r2,
            r3);
          {
            u32 i0;
            for (i0 = (u32)0U; i0 < n; i0++)
            {
              u8 *resij0 = r0 + i0 * (u32)2U;
              u8 *resij1 = r1 + i0 * (u32)2U;
              u8 *resij2 = r2 + i0 * (u32)2U;
              u8 *resij3 = r3 + i0 * (u32)2U;
              u16 u = load16_le(resij0);
              res[((u32)4U * i + (u32)0U) * n + i0] = u;
              {
                u16 u0 = load16_le(resij1);
                res[((u32)4U * i + (u32)1U) * n + i0] = u0;
                {
                  u16 u1 = load16_le(resij2);
                  res[((u32)4U * i + (u32)2U) * n + i0] = u1;
                  {
                    u16 u2 = load16_le(resij3);
                    res[((u32)4U * i + (u32)3U) * n + i0] = u2;
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

static inline void
Hacl_Impl_Frodo_Params_frodo_gen_matrix(
  Spec_Frodo_Params_frodo_gen_a a,
  u32 n,
  u8 *seed,
  u16 *a_matrix
)
{
  switch (a)
  {
    case Spec_Frodo_Params_SHAKE128:
      {
        Hacl_Impl_Frodo_Gen_frodo_gen_matrix_shake_4x(n, seed, a_matrix);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static const
u16
Hacl_Impl_Frodo_Params_cdf_table640[13U] =
  {
    (u16)4643U, (u16)13363U, (u16)20579U, (u16)25843U, (u16)29227U, (u16)31145U, (u16)32103U,
    (u16)32525U, (u16)32689U, (u16)32745U, (u16)32762U, (u16)32766U, (u16)32767U
  };

static const
u16
Hacl_Impl_Frodo_Params_cdf_table976[11U] =
  {
    (u16)5638U, (u16)15915U, (u16)23689U, (u16)28571U, (u16)31116U, (u16)32217U, (u16)32613U,
    (u16)32731U, (u16)32760U, (u16)32766U, (u16)32767U
  };

static const
u16
Hacl_Impl_Frodo_Params_cdf_table1344[7U] =
  { (u16)9142U, (u16)23462U, (u16)30338U, (u16)32361U, (u16)32725U, (u16)32765U, (u16)32767U };

static inline void
Hacl_Impl_Frodo_Sample_frodo_sample_matrix64(u32 n1, u32 n2, u8 *r, u16 *res)
{
  u32 i;
  memset(res, 0U, n1 * n2 * sizeof (u16));
  for (i = (u32)0U; i < n1; i++)
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < n2; i0++)
    {
      u8 *resij = r + (u32)2U * (n2 * i + i0);
      u16 u = load16_le(resij);
      u16 uu____0 = u;
      u16 prnd = uu____0 >> (u32)1U;
      u16 sign = uu____0 & (u16)1U;
      u16 sample = (u16)0U;
      u32 bound = (u32)12U;
      u16 sample00;
      {
        u32 i1;
        for (i1 = (u32)0U; i1 < bound; i1++)
        {
          u16 sample0 = sample;
          u16 ti = Hacl_Impl_Frodo_Params_cdf_table640[i1];
          u16 samplei = (u16)(u32)(ti - prnd) >> (u32)15U;
          sample = samplei + sample0;
        }
      }
      sample00 = sample;
      res[i * n2 + i0] = ((~sign + (u16)1U) ^ sample00) + sign;
    }
  }
}

static inline void
Hacl_Impl_Frodo_Sample_frodo_sample_matrix640(u32 n1, u32 n2, u8 *r, u16 *res)
{
  u32 i;
  memset(res, 0U, n1 * n2 * sizeof (u16));
  for (i = (u32)0U; i < n1; i++)
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < n2; i0++)
    {
      u8 *resij = r + (u32)2U * (n2 * i + i0);
      u16 u = load16_le(resij);
      u16 uu____0 = u;
      u16 prnd = uu____0 >> (u32)1U;
      u16 sign = uu____0 & (u16)1U;
      u16 sample = (u16)0U;
      u32 bound = (u32)12U;
      u16 sample00;
      {
        u32 i1;
        for (i1 = (u32)0U; i1 < bound; i1++)
        {
          u16 sample0 = sample;
          u16 ti = Hacl_Impl_Frodo_Params_cdf_table640[i1];
          u16 samplei = (u16)(u32)(ti - prnd) >> (u32)15U;
          sample = samplei + sample0;
        }
      }
      sample00 = sample;
      res[i * n2 + i0] = ((~sign + (u16)1U) ^ sample00) + sign;
    }
  }
}

static inline void
Hacl_Impl_Frodo_Sample_frodo_sample_matrix976(u32 n1, u32 n2, u8 *r, u16 *res)
{
  u32 i;
  memset(res, 0U, n1 * n2 * sizeof (u16));
  for (i = (u32)0U; i < n1; i++)
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < n2; i0++)
    {
      u8 *resij = r + (u32)2U * (n2 * i + i0);
      u16 u = load16_le(resij);
      u16 uu____0 = u;
      u16 prnd = uu____0 >> (u32)1U;
      u16 sign = uu____0 & (u16)1U;
      u16 sample = (u16)0U;
      u32 bound = (u32)10U;
      u16 sample00;
      {
        u32 i1;
        for (i1 = (u32)0U; i1 < bound; i1++)
        {
          u16 sample0 = sample;
          u16 ti = Hacl_Impl_Frodo_Params_cdf_table976[i1];
          u16 samplei = (u16)(u32)(ti - prnd) >> (u32)15U;
          sample = samplei + sample0;
        }
      }
      sample00 = sample;
      res[i * n2 + i0] = ((~sign + (u16)1U) ^ sample00) + sign;
    }
  }
}

static inline void
Hacl_Impl_Frodo_Sample_frodo_sample_matrix1344(u32 n1, u32 n2, u8 *r, u16 *res)
{
  u32 i;
  memset(res, 0U, n1 * n2 * sizeof (u16));
  for (i = (u32)0U; i < n1; i++)
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < n2; i0++)
    {
      u8 *resij = r + (u32)2U * (n2 * i + i0);
      u16 u = load16_le(resij);
      u16 uu____0 = u;
      u16 prnd = uu____0 >> (u32)1U;
      u16 sign = uu____0 & (u16)1U;
      u16 sample = (u16)0U;
      u32 bound = (u32)6U;
      u16 sample00;
      {
        u32 i1;
        for (i1 = (u32)0U; i1 < bound; i1++)
        {
          u16 sample0 = sample;
          u16 ti = Hacl_Impl_Frodo_Params_cdf_table1344[i1];
          u16 samplei = (u16)(u32)(ti - prnd) >> (u32)15U;
          sample = samplei + sample0;
        }
      }
      sample00 = sample;
      res[i * n2 + i0] = ((~sign + (u16)1U) ^ sample00) + sign;
    }
  }
}

void randombytes_(u32 len, u8 *res);

static inline void Hacl_Impl_Frodo_Pack_frodo_pack(u32 n1, u32 n2, u32 d, u16 *a, u8 *res)
{
  u32 n = n1 * n2 / (u32)8U;
  u32 i;
  for (i = (u32)0U; i < n; i++)
  {
    u16 *a1 = a + (u32)8U * i;
    u8 *r = res + d * i;
    u16 maskd = (u16)((u32)1U << d) - (u16)1U;
    u8 v16[16U] = { 0U };
    u16 a0 = a1[0U] & maskd;
    u16 a11 = a1[1U] & maskd;
    u16 a2 = a1[2U] & maskd;
    u16 a3 = a1[3U] & maskd;
    u16 a4 = a1[4U] & maskd;
    u16 a5 = a1[5U] & maskd;
    u16 a6 = a1[6U] & maskd;
    u16 a7 = a1[7U] & maskd;
    uint128_t
    templong =
      (((((((uint128_t)(u64)a0 << (u32)7U * d | (uint128_t)(u64)a11 << (u32)6U * d)
      | (uint128_t)(u64)a2 << (u32)5U * d)
      | (uint128_t)(u64)a3 << (u32)4U * d)
      | (uint128_t)(u64)a4 << (u32)3U * d)
      | (uint128_t)(u64)a5 << (u32)2U * d)
      | (uint128_t)(u64)a6 << (u32)1U * d)
      | (uint128_t)(u64)a7 << (u32)0U * d;
    u8 *src;
    store128_be(v16, templong);
    src = v16 + ((u32)16U - d);
    memcpy(r, src, d * sizeof (u8));
  }
}

static inline void Hacl_Impl_Frodo_Pack_frodo_unpack(u32 n1, u32 n2, u32 d, u8 *b, u16 *res)
{
  u32 n = n1 * n2 / (u32)8U;
  u32 i;
  for (i = (u32)0U; i < n; i++)
  {
    u8 *b1 = b + d * i;
    u16 *r = res + (u32)8U * i;
    u16 maskd = (u16)((u32)1U << d) - (u16)1U;
    u8 src[16U] = { 0U };
    uint128_t u;
    uint128_t templong;
    memcpy(src + ((u32)16U - d), b1, d * sizeof (u8));
    u = load128_be(src);
    templong = u;
    r[0U] = (u16)(uint64_t)(templong >> (u32)7U * d) & maskd;
    r[1U] = (u16)(uint64_t)(templong >> (u32)6U * d) & maskd;
    r[2U] = (u16)(uint64_t)(templong >> (u32)5U * d) & maskd;
    r[3U] = (u16)(uint64_t)(templong >> (u32)4U * d) & maskd;
    r[4U] = (u16)(uint64_t)(templong >> (u32)3U * d) & maskd;
    r[5U] = (u16)(uint64_t)(templong >> (u32)2U * d) & maskd;
    r[6U] = (u16)(uint64_t)(templong >> (u32)1U * d) & maskd;
    r[7U] = (u16)(uint64_t)(templong >> (u32)0U * d) & maskd;
  }
}

static inline void
Hacl_Impl_Frodo_Encode_frodo_key_encode(u32 logq, u32 b, u32 n, u8 *a, u16 *res)
{
  u32 i0;
  for (i0 = (u32)0U; i0 < n; i0++)
  {
    u8 v8[8U] = { 0U };
    u8 *chunk = a + i0 * b;
    u64 u;
    u64 x0;
    u64 x;
    u32 i;
    memcpy(v8, chunk, b * sizeof (u8));
    u = load64_le(v8);
    x0 = u;
    x = x0;
    for (i = (u32)0U; i < (u32)8U; i++)
    {
      u64 rk = x >> b * i & (((u64)1U << b) - (u64)1U);
      res[i0 * n + i] = (u16)rk << (logq - b);
    }
  }
}

static inline void
Hacl_Impl_Frodo_Encode_frodo_key_decode(u32 logq, u32 b, u32 n, u16 *a, u8 *res)
{
  u32 i;
  for (i = (u32)0U; i < n; i++)
  {
    u64 templong0 = (u64)0U;
    u64 templong;
    {
      u32 i0;
      for (i0 = (u32)0U; i0 < (u32)8U; i0++)
      {
        u16 aik = a[i * n + i0];
        u16 res1 = (aik + ((u16)1U << (logq - b - (u32)1U))) >> (logq - b);
        templong0 = templong0 | (u64)(res1 & (((u16)1U << b) - (u16)1U)) << b * i0;
      }
    }
    templong = templong0;
    {
      u8 v8[8U] = { 0U };
      u8 *tmp;
      store64_le(v8, templong);
      tmp = v8;
      memcpy(res + i * b, tmp, b * sizeof (u8));
    }
  }
}

#if defined(__cplusplus)
}
#endif

#define __Hacl_Frodo_KEM_H_DEFINED
#endif
