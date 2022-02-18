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

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Lib_RandomBuffer_System.h"
#include "Hacl_Spec.h"
#include "Hacl_SHA3.h"
#include "Hacl_Kremlib.h"

static inline void
Hacl_Keccak_shake128_4x(
  uint32_t input_len,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint32_t output_len,
  uint8_t *output0,
  uint8_t *output1,
  uint8_t *output2,
  uint8_t *output3
)
{
  Hacl_SHA3_shake128_hacl(input_len, input0, output_len, output0);
  Hacl_SHA3_shake128_hacl(input_len, input1, output_len, output1);
  Hacl_SHA3_shake128_hacl(input_len, input2, output_len, output2);
  Hacl_SHA3_shake128_hacl(input_len, input3, output_len, output3);
}

static inline void
Hacl_Impl_Matrix_mod_pow2(uint32_t n1, uint32_t n2, uint32_t logq, uint16_t *a)
{
  if (logq < (uint32_t)16U)
  {
    for (uint32_t i0 = (uint32_t)0U; i0 < n1; i0++)
    {
      for (uint32_t i = (uint32_t)0U; i < n2; i++)
      {
        a[i0 * n2 + i] = a[i0 * n2 + i] & (((uint16_t)1U << logq) - (uint16_t)1U);
      }
    }
    return;
  }
}

static inline void
Hacl_Impl_Matrix_matrix_add(uint32_t n1, uint32_t n2, uint16_t *a, uint16_t *b)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < n1; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < n2; i++)
    {
      a[i0 * n2 + i] = a[i0 * n2 + i] + b[i0 * n2 + i];
    }
  }
}

static inline void
Hacl_Impl_Matrix_matrix_sub(uint32_t n1, uint32_t n2, uint16_t *a, uint16_t *b)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < n1; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < n2; i++)
    {
      b[i0 * n2 + i] = a[i0 * n2 + i] - b[i0 * n2 + i];
    }
  }
}

static inline void
Hacl_Impl_Matrix_matrix_mul(
  uint32_t n1,
  uint32_t n2,
  uint32_t n3,
  uint16_t *a,
  uint16_t *b,
  uint16_t *c
)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < n1; i0++)
  {
    for (uint32_t i1 = (uint32_t)0U; i1 < n3; i1++)
    {
      uint16_t res = (uint16_t)0U;
      for (uint32_t i = (uint32_t)0U; i < n2; i++)
      {
        uint16_t aij = a[i0 * n2 + i];
        uint16_t bjk = b[i * n3 + i1];
        uint16_t res0 = res;
        res = res0 + aij * bjk;
      }
      c[i0 * n3 + i1] = res;
    }
  }
}

static inline void
Hacl_Impl_Matrix_matrix_mul_s(
  uint32_t n1,
  uint32_t n2,
  uint32_t n3,
  uint16_t *a,
  uint16_t *b,
  uint16_t *c
)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < n1; i0++)
  {
    for (uint32_t i1 = (uint32_t)0U; i1 < n3; i1++)
    {
      uint16_t res = (uint16_t)0U;
      for (uint32_t i = (uint32_t)0U; i < n2; i++)
      {
        uint16_t aij = a[i0 * n2 + i];
        uint16_t bjk = b[i1 * n2 + i];
        uint16_t res0 = res;
        res = res0 + aij * bjk;
      }
      c[i0 * n3 + i1] = res;
    }
  }
}

static inline uint16_t
Hacl_Impl_Matrix_matrix_eq(uint32_t n1, uint32_t n2, uint16_t *a, uint16_t *b)
{
  uint16_t res = (uint16_t)0xFFFFU;
  for (uint32_t i = (uint32_t)0U; i < n1 * n2; i++)
  {
    uint16_t uu____0 = FStar_UInt16_eq_mask(a[i], b[i]);
    res = uu____0 & res;
  }
  uint16_t r = res;
  return r;
}

static inline void
Hacl_Impl_Matrix_matrix_to_lbytes(uint32_t n1, uint32_t n2, uint16_t *m, uint8_t *res)
{
  for (uint32_t i = (uint32_t)0U; i < n1 * n2; i++)
  {
    store16_le(res + (uint32_t)2U * i, m[i]);
  }
}

static inline void
Hacl_Impl_Matrix_matrix_from_lbytes(uint32_t n1, uint32_t n2, uint8_t *b, uint16_t *res)
{
  for (uint32_t i = (uint32_t)0U; i < n1 * n2; i++)
  {
    uint16_t *os = res;
    uint16_t u = load16_le(b + (uint32_t)2U * i);
    uint16_t x = u;
    os[i] = x;
  }
}

static inline void
Hacl_Impl_Frodo_Gen_frodo_gen_matrix_shake_4x(uint32_t n, uint8_t *seed, uint16_t *res)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)8U * n);
  uint8_t r[(uint32_t)8U * n];
  memset(r, 0U, (uint32_t)8U * n * sizeof (uint8_t));
  uint8_t tmp_seed[72U] = { 0U };
  memcpy(tmp_seed + (uint32_t)2U, seed, (uint32_t)16U * sizeof (uint8_t));
  memcpy(tmp_seed + (uint32_t)20U, seed, (uint32_t)16U * sizeof (uint8_t));
  memcpy(tmp_seed + (uint32_t)38U, seed, (uint32_t)16U * sizeof (uint8_t));
  memcpy(tmp_seed + (uint32_t)56U, seed, (uint32_t)16U * sizeof (uint8_t));
  memset(res, 0U, n * n * sizeof (uint16_t));
  for (uint32_t i = (uint32_t)0U; i < n / (uint32_t)4U; i++)
  {
    uint8_t *r0 = r + (uint32_t)0U * n;
    uint8_t *r1 = r + (uint32_t)2U * n;
    uint8_t *r2 = r + (uint32_t)4U * n;
    uint8_t *r3 = r + (uint32_t)6U * n;
    uint8_t *tmp_seed0 = tmp_seed;
    uint8_t *tmp_seed1 = tmp_seed + (uint32_t)18U;
    uint8_t *tmp_seed2 = tmp_seed + (uint32_t)36U;
    uint8_t *tmp_seed3 = tmp_seed + (uint32_t)54U;
    store16_le(tmp_seed0, (uint16_t)((uint32_t)4U * i + (uint32_t)0U));
    store16_le(tmp_seed1, (uint16_t)((uint32_t)4U * i + (uint32_t)1U));
    store16_le(tmp_seed2, (uint16_t)((uint32_t)4U * i + (uint32_t)2U));
    store16_le(tmp_seed3, (uint16_t)((uint32_t)4U * i + (uint32_t)3U));
    Hacl_Keccak_shake128_4x((uint32_t)18U,
      tmp_seed0,
      tmp_seed1,
      tmp_seed2,
      tmp_seed3,
      (uint32_t)2U * n,
      r0,
      r1,
      r2,
      r3);
    for (uint32_t i0 = (uint32_t)0U; i0 < n; i0++)
    {
      uint8_t *resij0 = r0 + i0 * (uint32_t)2U;
      uint8_t *resij1 = r1 + i0 * (uint32_t)2U;
      uint8_t *resij2 = r2 + i0 * (uint32_t)2U;
      uint8_t *resij3 = r3 + i0 * (uint32_t)2U;
      uint16_t u = load16_le(resij0);
      res[((uint32_t)4U * i + (uint32_t)0U) * n + i0] = u;
      uint16_t u0 = load16_le(resij1);
      res[((uint32_t)4U * i + (uint32_t)1U) * n + i0] = u0;
      uint16_t u1 = load16_le(resij2);
      res[((uint32_t)4U * i + (uint32_t)2U) * n + i0] = u1;
      uint16_t u2 = load16_le(resij3);
      res[((uint32_t)4U * i + (uint32_t)3U) * n + i0] = u2;
    }
  }
}

static inline void
Hacl_Impl_Frodo_Params_frodo_gen_matrix(
  Spec_Frodo_Params_frodo_gen_a a,
  uint32_t n,
  uint8_t *seed,
  uint16_t *a_matrix
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
uint16_t
Hacl_Impl_Frodo_Params_cdf_table640[13U] =
  {
    (uint16_t)4643U, (uint16_t)13363U, (uint16_t)20579U, (uint16_t)25843U, (uint16_t)29227U,
    (uint16_t)31145U, (uint16_t)32103U, (uint16_t)32525U, (uint16_t)32689U, (uint16_t)32745U,
    (uint16_t)32762U, (uint16_t)32766U, (uint16_t)32767U
  };

static const
uint16_t
Hacl_Impl_Frodo_Params_cdf_table976[11U] =
  {
    (uint16_t)5638U, (uint16_t)15915U, (uint16_t)23689U, (uint16_t)28571U, (uint16_t)31116U,
    (uint16_t)32217U, (uint16_t)32613U, (uint16_t)32731U, (uint16_t)32760U, (uint16_t)32766U,
    (uint16_t)32767U
  };

static const
uint16_t
Hacl_Impl_Frodo_Params_cdf_table1344[7U] =
  {
    (uint16_t)9142U, (uint16_t)23462U, (uint16_t)30338U, (uint16_t)32361U, (uint16_t)32725U,
    (uint16_t)32765U, (uint16_t)32767U
  };

static inline void
Hacl_Impl_Frodo_Sample_frodo_sample_matrix64(
  uint32_t n1,
  uint32_t n2,
  uint8_t *r,
  uint16_t *res
)
{
  memset(res, 0U, n1 * n2 * sizeof (uint16_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < n1; i0++)
  {
    for (uint32_t i1 = (uint32_t)0U; i1 < n2; i1++)
    {
      uint8_t *resij = r + (uint32_t)2U * (n2 * i0 + i1);
      uint16_t u = load16_le(resij);
      uint16_t uu____0 = u;
      uint16_t prnd = uu____0 >> (uint32_t)1U;
      uint16_t sign = uu____0 & (uint16_t)1U;
      uint16_t sample = (uint16_t)0U;
      uint32_t bound = (uint32_t)12U;
      for (uint32_t i = (uint32_t)0U; i < bound; i++)
      {
        uint16_t sample0 = sample;
        uint16_t ti = Hacl_Impl_Frodo_Params_cdf_table640[i];
        uint16_t samplei = (uint16_t)(uint32_t)(ti - prnd) >> (uint32_t)15U;
        sample = samplei + sample0;
      }
      uint16_t sample0 = sample;
      res[i0 * n2 + i1] = ((~sign + (uint16_t)1U) ^ sample0) + sign;
    }
  }
}

static inline void
Hacl_Impl_Frodo_Sample_frodo_sample_matrix640(
  uint32_t n1,
  uint32_t n2,
  uint8_t *r,
  uint16_t *res
)
{
  memset(res, 0U, n1 * n2 * sizeof (uint16_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < n1; i0++)
  {
    for (uint32_t i1 = (uint32_t)0U; i1 < n2; i1++)
    {
      uint8_t *resij = r + (uint32_t)2U * (n2 * i0 + i1);
      uint16_t u = load16_le(resij);
      uint16_t uu____0 = u;
      uint16_t prnd = uu____0 >> (uint32_t)1U;
      uint16_t sign = uu____0 & (uint16_t)1U;
      uint16_t sample = (uint16_t)0U;
      uint32_t bound = (uint32_t)12U;
      for (uint32_t i = (uint32_t)0U; i < bound; i++)
      {
        uint16_t sample0 = sample;
        uint16_t ti = Hacl_Impl_Frodo_Params_cdf_table640[i];
        uint16_t samplei = (uint16_t)(uint32_t)(ti - prnd) >> (uint32_t)15U;
        sample = samplei + sample0;
      }
      uint16_t sample0 = sample;
      res[i0 * n2 + i1] = ((~sign + (uint16_t)1U) ^ sample0) + sign;
    }
  }
}

static inline void
Hacl_Impl_Frodo_Sample_frodo_sample_matrix976(
  uint32_t n1,
  uint32_t n2,
  uint8_t *r,
  uint16_t *res
)
{
  memset(res, 0U, n1 * n2 * sizeof (uint16_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < n1; i0++)
  {
    for (uint32_t i1 = (uint32_t)0U; i1 < n2; i1++)
    {
      uint8_t *resij = r + (uint32_t)2U * (n2 * i0 + i1);
      uint16_t u = load16_le(resij);
      uint16_t uu____0 = u;
      uint16_t prnd = uu____0 >> (uint32_t)1U;
      uint16_t sign = uu____0 & (uint16_t)1U;
      uint16_t sample = (uint16_t)0U;
      uint32_t bound = (uint32_t)10U;
      for (uint32_t i = (uint32_t)0U; i < bound; i++)
      {
        uint16_t sample0 = sample;
        uint16_t ti = Hacl_Impl_Frodo_Params_cdf_table976[i];
        uint16_t samplei = (uint16_t)(uint32_t)(ti - prnd) >> (uint32_t)15U;
        sample = samplei + sample0;
      }
      uint16_t sample0 = sample;
      res[i0 * n2 + i1] = ((~sign + (uint16_t)1U) ^ sample0) + sign;
    }
  }
}

static inline void
Hacl_Impl_Frodo_Sample_frodo_sample_matrix1344(
  uint32_t n1,
  uint32_t n2,
  uint8_t *r,
  uint16_t *res
)
{
  memset(res, 0U, n1 * n2 * sizeof (uint16_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < n1; i0++)
  {
    for (uint32_t i1 = (uint32_t)0U; i1 < n2; i1++)
    {
      uint8_t *resij = r + (uint32_t)2U * (n2 * i0 + i1);
      uint16_t u = load16_le(resij);
      uint16_t uu____0 = u;
      uint16_t prnd = uu____0 >> (uint32_t)1U;
      uint16_t sign = uu____0 & (uint16_t)1U;
      uint16_t sample = (uint16_t)0U;
      uint32_t bound = (uint32_t)6U;
      for (uint32_t i = (uint32_t)0U; i < bound; i++)
      {
        uint16_t sample0 = sample;
        uint16_t ti = Hacl_Impl_Frodo_Params_cdf_table1344[i];
        uint16_t samplei = (uint16_t)(uint32_t)(ti - prnd) >> (uint32_t)15U;
        sample = samplei + sample0;
      }
      uint16_t sample0 = sample;
      res[i0 * n2 + i1] = ((~sign + (uint16_t)1U) ^ sample0) + sign;
    }
  }
}

static inline void
Hacl_Impl_Frodo_Pack_frodo_pack(
  uint32_t n1,
  uint32_t n2,
  uint32_t d,
  uint16_t *a,
  uint8_t *res
)
{
  uint32_t n = n1 * n2 / (uint32_t)8U;
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    uint16_t *a1 = a + (uint32_t)8U * i;
    uint8_t *r = res + d * i;
    uint16_t maskd = (uint16_t)((uint32_t)1U << d) - (uint16_t)1U;
    uint8_t v16[16U] = { 0U };
    uint16_t a0 = a1[0U] & maskd;
    uint16_t a11 = a1[1U] & maskd;
    uint16_t a2 = a1[2U] & maskd;
    uint16_t a3 = a1[3U] & maskd;
    uint16_t a4 = a1[4U] & maskd;
    uint16_t a5 = a1[5U] & maskd;
    uint16_t a6 = a1[6U] & maskd;
    uint16_t a7 = a1[7U] & maskd;
    FStar_UInt128_uint128
    templong =
      FStar_UInt128_logor(FStar_UInt128_logor(FStar_UInt128_logor(FStar_UInt128_logor(FStar_UInt128_logor(FStar_UInt128_logor(FStar_UInt128_logor(FStar_UInt128_shift_left(FStar_UInt128_uint64_to_uint128((uint64_t)a0),
                      (uint32_t)7U * d),
                    FStar_UInt128_shift_left(FStar_UInt128_uint64_to_uint128((uint64_t)a11),
                      (uint32_t)6U * d)),
                  FStar_UInt128_shift_left(FStar_UInt128_uint64_to_uint128((uint64_t)a2),
                    (uint32_t)5U * d)),
                FStar_UInt128_shift_left(FStar_UInt128_uint64_to_uint128((uint64_t)a3),
                  (uint32_t)4U * d)),
              FStar_UInt128_shift_left(FStar_UInt128_uint64_to_uint128((uint64_t)a4),
                (uint32_t)3U * d)),
            FStar_UInt128_shift_left(FStar_UInt128_uint64_to_uint128((uint64_t)a5),
              (uint32_t)2U * d)),
          FStar_UInt128_shift_left(FStar_UInt128_uint64_to_uint128((uint64_t)a6), (uint32_t)1U * d)),
        FStar_UInt128_shift_left(FStar_UInt128_uint64_to_uint128((uint64_t)a7), (uint32_t)0U * d));
    store128_be(v16, templong);
    uint8_t *src = v16 + (uint32_t)16U - d;
    memcpy(r, src, d * sizeof (uint8_t));
  }
}

static inline void
Hacl_Impl_Frodo_Pack_frodo_unpack(
  uint32_t n1,
  uint32_t n2,
  uint32_t d,
  uint8_t *b,
  uint16_t *res
)
{
  uint32_t n = n1 * n2 / (uint32_t)8U;
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    uint8_t *b1 = b + d * i;
    uint16_t *r = res + (uint32_t)8U * i;
    uint16_t maskd = (uint16_t)((uint32_t)1U << d) - (uint16_t)1U;
    uint8_t src[16U] = { 0U };
    memcpy(src + (uint32_t)16U - d, b1, d * sizeof (uint8_t));
    FStar_UInt128_uint128 u = load128_be(src);
    FStar_UInt128_uint128 templong = u;
    r[0U] =
      (uint16_t)FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(templong,
          (uint32_t)7U * d))
      & maskd;
    r[1U] =
      (uint16_t)FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(templong,
          (uint32_t)6U * d))
      & maskd;
    r[2U] =
      (uint16_t)FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(templong,
          (uint32_t)5U * d))
      & maskd;
    r[3U] =
      (uint16_t)FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(templong,
          (uint32_t)4U * d))
      & maskd;
    r[4U] =
      (uint16_t)FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(templong,
          (uint32_t)3U * d))
      & maskd;
    r[5U] =
      (uint16_t)FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(templong,
          (uint32_t)2U * d))
      & maskd;
    r[6U] =
      (uint16_t)FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(templong,
          (uint32_t)1U * d))
      & maskd;
    r[7U] =
      (uint16_t)FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(templong,
          (uint32_t)0U * d))
      & maskd;
  }
}

static inline void
Hacl_Impl_Frodo_Encode_frodo_key_encode(
  uint32_t logq,
  uint32_t b,
  uint32_t n,
  uint8_t *a,
  uint16_t *res
)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < n; i0++)
  {
    uint8_t v8[8U] = { 0U };
    uint8_t *chunk = a + i0 * b;
    memcpy(v8, chunk, b * sizeof (uint8_t));
    uint64_t u = load64_le(v8);
    uint64_t x = u;
    uint64_t x0 = x;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
    {
      uint64_t rk = x0 >> b * i & (((uint64_t)1U << b) - (uint64_t)1U);
      res[i0 * n + i] = (uint16_t)rk << (logq - b);
    }
  }
}

static inline void
Hacl_Impl_Frodo_Encode_frodo_key_decode(
  uint32_t logq,
  uint32_t b,
  uint32_t n,
  uint16_t *a,
  uint8_t *res
)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < n; i0++)
  {
    uint64_t templong = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
    {
      uint16_t aik = a[i0 * n + i];
      uint16_t res1 = (aik + ((uint16_t)1U << (logq - b - (uint32_t)1U))) >> (logq - b);
      templong = templong | (uint64_t)(res1 & (((uint16_t)1U << b) - (uint16_t)1U)) << b * i;
    }
    uint64_t templong0 = templong;
    uint8_t v8[8U] = { 0U };
    store64_le(v8, templong0);
    uint8_t *tmp = v8;
    memcpy(res + i0 * b, tmp, b * sizeof (uint8_t));
  }
}

#if defined(__cplusplus)
}
#endif

#define __Hacl_Frodo_KEM_H_DEFINED
#endif
