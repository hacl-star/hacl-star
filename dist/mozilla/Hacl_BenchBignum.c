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


#include "Hacl_BenchBignum.h"

#include "internal/Hacl_Bignum256_32_Hacl_Bignum4096_32_Hacl_Bignum256_Hacl_Bignum4096_Hacl_Bignum32_Hacl_Bignum64_Hacl_GenericField32_Hacl_GenericField64_Hacl_Bignum_Hacl_Bignum.h"

void
Hacl_BenchBignum_mod_exp_bm_vartime_mm_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k10 = *k;
  uint32_t len1 = k10.len;
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t aM[len1];
  memset(aM, 0U, len1 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t c[len1 + len1];
  memset(c, 0U, (len1 + len1) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len1);
  uint64_t tmp0[(uint32_t)4U * len1];
  memset(tmp0, 0U, (uint32_t)4U * len1 * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len1, a, k1.r2, tmp0, c);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, c, aM);
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t resM[len1];
  memset(resM, 0U, len1 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t tmp1[len1 + len1];
  memset(tmp1, 0U, (len1 + len1) * sizeof (uint64_t));
  memcpy(tmp1, k1.r2, len1 * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, tmp1, resM);
  for (uint32_t i = (uint32_t)0U; i < bBits; i++)
  {
    uint32_t i1 = i / (uint32_t)64U;
    uint32_t j = i % (uint32_t)64U;
    uint64_t tmp = b[i1];
    uint64_t bit = tmp >> j & (uint64_t)1U;
    if (!(bit == (uint64_t)0U))
    {
      Hacl_Bignum_Montgomery_bn_mont_mul_u64(len1, k1.n, k1.mu, resM, aM, resM);
    }
    Hacl_Bignum_Montgomery_bn_mont_sqr_u64(len1, k1.n, k1.mu, aM, aM);
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t tmp[len1 + len1];
  memset(tmp, 0U, (len1 + len1) * sizeof (uint64_t));
  memcpy(tmp, resM, len1 * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, tmp, res);
}

void
Hacl_BenchBignum_mod_exp_bm_consttime_mm_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k10 = *k;
  uint32_t len1 = k10.len;
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t aM[len1];
  memset(aM, 0U, len1 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t c[len1 + len1];
  memset(c, 0U, (len1 + len1) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len1);
  uint64_t tmp0[(uint32_t)4U * len1];
  memset(tmp0, 0U, (uint32_t)4U * len1 * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len1, a, k1.r2, tmp0, c);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, c, aM);
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t resM[len1];
  memset(resM, 0U, len1 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t tmp1[len1 + len1];
  memset(tmp1, 0U, (len1 + len1) * sizeof (uint64_t));
  memcpy(tmp1, k1.r2, len1 * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, tmp1, resM);
  uint64_t sw = (uint64_t)0U;
  for (uint32_t i0 = (uint32_t)0U; i0 < bBits; i0++)
  {
    uint32_t i1 = (bBits - i0 - (uint32_t)1U) / (uint32_t)64U;
    uint32_t j = (bBits - i0 - (uint32_t)1U) % (uint32_t)64U;
    uint64_t tmp = b[i1];
    uint64_t bit = tmp >> j & (uint64_t)1U;
    uint64_t sw1 = bit ^ sw;
    for (uint32_t i = (uint32_t)0U; i < len1; i++)
    {
      uint64_t dummy = ((uint64_t)0U - sw1) & (resM[i] ^ aM[i]);
      resM[i] = resM[i] ^ dummy;
      aM[i] = aM[i] ^ dummy;
    }
    Hacl_Bignum_Montgomery_bn_mont_mul_u64(len1, k1.n, k1.mu, aM, resM, aM);
    Hacl_Bignum_Montgomery_bn_mont_sqr_u64(len1, k1.n, k1.mu, resM, resM);
    sw = bit;
  }
  uint64_t sw0 = sw;
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint64_t dummy = ((uint64_t)0U - sw0) & (resM[i] ^ aM[i]);
    resM[i] = resM[i] ^ dummy;
    aM[i] = aM[i] ^ dummy;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t tmp[len1 + len1];
  memset(tmp, 0U, (len1 + len1) * sizeof (uint64_t));
  memcpy(tmp, resM, len1 * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, tmp, res);
}

void
Hacl_BenchBignum_mod_exp_fw_vartime_mm_precomp(
  uint32_t l,
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k10 = *k;
  uint32_t len1 = k10.len;
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t aM[len1];
  memset(aM, 0U, len1 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t c[len1 + len1];
  memset(c, 0U, (len1 + len1) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len1);
  uint64_t tmp0[(uint32_t)4U * len1];
  memset(tmp0, 0U, (uint32_t)4U * len1 * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len1, a, k1.r2, tmp0, c);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, c, aM);
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t resM[len1];
  memset(resM, 0U, len1 * sizeof (uint64_t));
  uint32_t bLen;
  if (bBits == (uint32_t)0U)
  {
    bLen = (uint32_t)1U;
  }
  else
  {
    bLen = (bBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t tmp[len1 + len1];
  memset(tmp, 0U, (len1 + len1) * sizeof (uint64_t));
  memcpy(tmp, k1.r2, len1 * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, tmp, resM);
  KRML_CHECK_SIZE(sizeof (uint64_t), ((uint32_t)1U << l) * len1);
  uint64_t table[((uint32_t)1U << l) * len1];
  memset(table, 0U, ((uint32_t)1U << l) * len1 * sizeof (uint64_t));
  memcpy(table, resM, len1 * sizeof (uint64_t));
  uint64_t *t1 = table + len1;
  memcpy(t1, aM, len1 * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < ((uint32_t)1U << l) - (uint32_t)1U; i++)
  {
    uint64_t *t11 = table + i * len1;
    uint64_t *t2 = table + i * len1 + len1;
    Hacl_Bignum_Montgomery_bn_mont_mul_u64(len1, k1.n, k1.mu, aM, t11, t2);
  }
  if (bBits % l != (uint32_t)0U)
  {
    uint64_t mask_l = ((uint64_t)1U << l) - (uint64_t)1U;
    uint32_t i = bBits / l * l / (uint32_t)64U;
    uint32_t j = bBits / l * l % (uint32_t)64U;
    uint64_t p1 = b[i] >> j;
    uint64_t ite;
    if (i + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_c = ite & mask_l;
    uint32_t bits_l32 = (uint32_t)bits_c;
    uint64_t *a_bits_l = table + bits_l32 * len1;
    memcpy(resM, a_bits_l, len1 * sizeof (uint64_t));
  }
  for (uint32_t i = (uint32_t)0U; i < bBits / l; i++)
  {
    for (uint32_t i0 = (uint32_t)0U; i0 < l; i0++)
    {
      Hacl_Bignum_Montgomery_bn_mont_sqr_u64(len1, k1.n, k1.mu, resM, resM);
    }
    uint32_t bk = bBits - bBits % l;
    uint64_t mask_l = ((uint64_t)1U << l) - (uint64_t)1U;
    uint32_t i1 = (bk - l * i - l) / (uint32_t)64U;
    uint32_t j = (bk - l * i - l) % (uint32_t)64U;
    uint64_t p1 = b[i1] >> j;
    uint64_t ite;
    if (i1 + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_l = ite & mask_l;
    KRML_CHECK_SIZE(sizeof (uint64_t), len1);
    uint64_t a_bits_l[len1];
    memset(a_bits_l, 0U, len1 * sizeof (uint64_t));
    uint32_t bits_l32 = (uint32_t)bits_l;
    uint64_t *a_bits_l1 = table + bits_l32 * len1;
    memcpy(a_bits_l, a_bits_l1, len1 * sizeof (uint64_t));
    Hacl_Bignum_Montgomery_bn_mont_mul_u64(len1, k1.n, k1.mu, resM, a_bits_l, resM);
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t tmp1[len1 + len1];
  memset(tmp1, 0U, (len1 + len1) * sizeof (uint64_t));
  memcpy(tmp1, resM, len1 * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, tmp1, res);
}

void
Hacl_BenchBignum_mod_exp_fw_consttime_mm_precomp(
  uint32_t l,
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k10 = *k;
  uint32_t len1 = k10.len;
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t aM[len1];
  memset(aM, 0U, len1 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t c0[len1 + len1];
  memset(c0, 0U, (len1 + len1) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len1);
  uint64_t tmp0[(uint32_t)4U * len1];
  memset(tmp0, 0U, (uint32_t)4U * len1 * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len1, a, k1.r2, tmp0, c0);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, c0, aM);
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t resM[len1];
  memset(resM, 0U, len1 * sizeof (uint64_t));
  uint32_t bLen;
  if (bBits == (uint32_t)0U)
  {
    bLen = (uint32_t)1U;
  }
  else
  {
    bLen = (bBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t tmp[len1 + len1];
  memset(tmp, 0U, (len1 + len1) * sizeof (uint64_t));
  memcpy(tmp, k1.r2, len1 * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, tmp, resM);
  KRML_CHECK_SIZE(sizeof (uint64_t), ((uint32_t)1U << l) * len1);
  uint64_t table[((uint32_t)1U << l) * len1];
  memset(table, 0U, ((uint32_t)1U << l) * len1 * sizeof (uint64_t));
  memcpy(table, resM, len1 * sizeof (uint64_t));
  uint64_t *t1 = table + len1;
  memcpy(t1, aM, len1 * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < ((uint32_t)1U << l) - (uint32_t)1U; i++)
  {
    uint64_t *t11 = table + i * len1;
    uint64_t *t2 = table + i * len1 + len1;
    Hacl_Bignum_Montgomery_bn_mont_mul_u64(len1, k1.n, k1.mu, aM, t11, t2);
  }
  if (bBits % l != (uint32_t)0U)
  {
    uint64_t mask_l = ((uint64_t)1U << l) - (uint64_t)1U;
    uint32_t i0 = bBits / l * l / (uint32_t)64U;
    uint32_t j = bBits / l * l % (uint32_t)64U;
    uint64_t p1 = b[i0] >> j;
    uint64_t ite;
    if (i0 + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i0 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_c = ite & mask_l;
    memcpy(resM, table, len1 * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < ((uint32_t)1U << l) - (uint32_t)1U; i1++)
    {
      uint64_t c = FStar_UInt64_eq_mask(bits_c, (uint64_t)(i1 + (uint32_t)1U));
      uint64_t *res_j = table + (i1 + (uint32_t)1U) * len1;
      for (uint32_t i = (uint32_t)0U; i < len1; i++)
      {
        uint64_t *os = resM;
        uint64_t x = (c & res_j[i]) | (~c & resM[i]);
        os[i] = x;
      }
    }
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < bBits / l; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < l; i++)
    {
      Hacl_Bignum_Montgomery_bn_mont_sqr_u64(len1, k1.n, k1.mu, resM, resM);
    }
    uint32_t bk = bBits - bBits % l;
    uint64_t mask_l = ((uint64_t)1U << l) - (uint64_t)1U;
    uint32_t i1 = (bk - l * i0 - l) / (uint32_t)64U;
    uint32_t j = (bk - l * i0 - l) % (uint32_t)64U;
    uint64_t p1 = b[i1] >> j;
    uint64_t ite;
    if (i1 + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_l = ite & mask_l;
    KRML_CHECK_SIZE(sizeof (uint64_t), len1);
    uint64_t a_bits_l[len1];
    memset(a_bits_l, 0U, len1 * sizeof (uint64_t));
    memcpy(a_bits_l, table, len1 * sizeof (uint64_t));
    for (uint32_t i2 = (uint32_t)0U; i2 < ((uint32_t)1U << l) - (uint32_t)1U; i2++)
    {
      uint64_t c = FStar_UInt64_eq_mask(bits_l, (uint64_t)(i2 + (uint32_t)1U));
      uint64_t *res_j = table + (i2 + (uint32_t)1U) * len1;
      for (uint32_t i = (uint32_t)0U; i < len1; i++)
      {
        uint64_t *os = a_bits_l;
        uint64_t x = (c & res_j[i]) | (~c & a_bits_l[i]);
        os[i] = x;
      }
    }
    Hacl_Bignum_Montgomery_bn_mont_mul_u64(len1, k1.n, k1.mu, resM, a_bits_l, resM);
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t tmp1[len1 + len1];
  memset(tmp1, 0U, (len1 + len1) * sizeof (uint64_t));
  memcpy(tmp1, resM, len1 * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, tmp1, res);
}

void
Hacl_BenchBignum_mod_exp_bm_vartime_amm_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k10 = *k;
  uint32_t len1 = k10.len;
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t aM[len1];
  memset(aM, 0U, len1 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t c[len1 + len1];
  memset(c, 0U, (len1 + len1) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len1);
  uint64_t tmp0[(uint32_t)4U * len1];
  memset(tmp0, 0U, (uint32_t)4U * len1 * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len1, a, k1.r2, tmp0, c);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, c, aM);
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t resM[len1];
  memset(resM, 0U, len1 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t tmp1[len1 + len1];
  memset(tmp1, 0U, (len1 + len1) * sizeof (uint64_t));
  memcpy(tmp1, k1.r2, len1 * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, tmp1, resM);
  for (uint32_t i = (uint32_t)0U; i < bBits; i++)
  {
    uint32_t i1 = i / (uint32_t)64U;
    uint32_t j = i % (uint32_t)64U;
    uint64_t tmp = b[i1];
    uint64_t bit = tmp >> j & (uint64_t)1U;
    if (!(bit == (uint64_t)0U))
    {
      Hacl_Bignum_AlmostMontgomery_bn_almost_mont_mul_u64(len1, k1.n, k1.mu, resM, aM, resM);
    }
    Hacl_Bignum_AlmostMontgomery_bn_almost_mont_sqr_u64(len1, k1.n, k1.mu, aM, aM);
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t tmp[len1 + len1];
  memset(tmp, 0U, (len1 + len1) * sizeof (uint64_t));
  memcpy(tmp, resM, len1 * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, tmp, res);
}

void
Hacl_BenchBignum_mod_exp_bm_consttime_amm_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k10 = *k;
  uint32_t len1 = k10.len;
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t aM[len1];
  memset(aM, 0U, len1 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t c[len1 + len1];
  memset(c, 0U, (len1 + len1) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len1);
  uint64_t tmp0[(uint32_t)4U * len1];
  memset(tmp0, 0U, (uint32_t)4U * len1 * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len1, a, k1.r2, tmp0, c);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, c, aM);
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t resM[len1];
  memset(resM, 0U, len1 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t tmp1[len1 + len1];
  memset(tmp1, 0U, (len1 + len1) * sizeof (uint64_t));
  memcpy(tmp1, k1.r2, len1 * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, tmp1, resM);
  uint64_t sw = (uint64_t)0U;
  for (uint32_t i0 = (uint32_t)0U; i0 < bBits; i0++)
  {
    uint32_t i1 = (bBits - i0 - (uint32_t)1U) / (uint32_t)64U;
    uint32_t j = (bBits - i0 - (uint32_t)1U) % (uint32_t)64U;
    uint64_t tmp = b[i1];
    uint64_t bit = tmp >> j & (uint64_t)1U;
    uint64_t sw1 = bit ^ sw;
    for (uint32_t i = (uint32_t)0U; i < len1; i++)
    {
      uint64_t dummy = ((uint64_t)0U - sw1) & (resM[i] ^ aM[i]);
      resM[i] = resM[i] ^ dummy;
      aM[i] = aM[i] ^ dummy;
    }
    Hacl_Bignum_AlmostMontgomery_bn_almost_mont_mul_u64(len1, k1.n, k1.mu, aM, resM, aM);
    Hacl_Bignum_AlmostMontgomery_bn_almost_mont_sqr_u64(len1, k1.n, k1.mu, resM, resM);
    sw = bit;
  }
  uint64_t sw0 = sw;
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint64_t dummy = ((uint64_t)0U - sw0) & (resM[i] ^ aM[i]);
    resM[i] = resM[i] ^ dummy;
    aM[i] = aM[i] ^ dummy;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t tmp[len1 + len1];
  memset(tmp, 0U, (len1 + len1) * sizeof (uint64_t));
  memcpy(tmp, resM, len1 * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, tmp, res);
}

void
Hacl_BenchBignum_mod_exp_fw_vartime_amm_precomp(
  uint32_t l,
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k10 = *k;
  uint32_t len1 = k10.len;
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t aM[len1];
  memset(aM, 0U, len1 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t c[len1 + len1];
  memset(c, 0U, (len1 + len1) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len1);
  uint64_t tmp0[(uint32_t)4U * len1];
  memset(tmp0, 0U, (uint32_t)4U * len1 * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len1, a, k1.r2, tmp0, c);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, c, aM);
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t resM[len1];
  memset(resM, 0U, len1 * sizeof (uint64_t));
  uint32_t bLen;
  if (bBits == (uint32_t)0U)
  {
    bLen = (uint32_t)1U;
  }
  else
  {
    bLen = (bBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t tmp[len1 + len1];
  memset(tmp, 0U, (len1 + len1) * sizeof (uint64_t));
  memcpy(tmp, k1.r2, len1 * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, tmp, resM);
  KRML_CHECK_SIZE(sizeof (uint64_t), ((uint32_t)1U << l) * len1);
  uint64_t table[((uint32_t)1U << l) * len1];
  memset(table, 0U, ((uint32_t)1U << l) * len1 * sizeof (uint64_t));
  memcpy(table, resM, len1 * sizeof (uint64_t));
  uint64_t *t1 = table + len1;
  memcpy(t1, aM, len1 * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < ((uint32_t)1U << l) - (uint32_t)1U; i++)
  {
    uint64_t *t11 = table + i * len1;
    uint64_t *t2 = table + i * len1 + len1;
    Hacl_Bignum_AlmostMontgomery_bn_almost_mont_mul_u64(len1, k1.n, k1.mu, aM, t11, t2);
  }
  if (bBits % l != (uint32_t)0U)
  {
    uint64_t mask_l = ((uint64_t)1U << l) - (uint64_t)1U;
    uint32_t i = bBits / l * l / (uint32_t)64U;
    uint32_t j = bBits / l * l % (uint32_t)64U;
    uint64_t p1 = b[i] >> j;
    uint64_t ite;
    if (i + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_c = ite & mask_l;
    uint32_t bits_l32 = (uint32_t)bits_c;
    uint64_t *a_bits_l = table + bits_l32 * len1;
    memcpy(resM, a_bits_l, len1 * sizeof (uint64_t));
  }
  for (uint32_t i = (uint32_t)0U; i < bBits / l; i++)
  {
    for (uint32_t i0 = (uint32_t)0U; i0 < l; i0++)
    {
      Hacl_Bignum_AlmostMontgomery_bn_almost_mont_sqr_u64(len1, k1.n, k1.mu, resM, resM);
    }
    uint32_t bk = bBits - bBits % l;
    uint64_t mask_l = ((uint64_t)1U << l) - (uint64_t)1U;
    uint32_t i1 = (bk - l * i - l) / (uint32_t)64U;
    uint32_t j = (bk - l * i - l) % (uint32_t)64U;
    uint64_t p1 = b[i1] >> j;
    uint64_t ite;
    if (i1 + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_l = ite & mask_l;
    KRML_CHECK_SIZE(sizeof (uint64_t), len1);
    uint64_t a_bits_l[len1];
    memset(a_bits_l, 0U, len1 * sizeof (uint64_t));
    uint32_t bits_l32 = (uint32_t)bits_l;
    uint64_t *a_bits_l1 = table + bits_l32 * len1;
    memcpy(a_bits_l, a_bits_l1, len1 * sizeof (uint64_t));
    Hacl_Bignum_AlmostMontgomery_bn_almost_mont_mul_u64(len1, k1.n, k1.mu, resM, a_bits_l, resM);
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t tmp1[len1 + len1];
  memset(tmp1, 0U, (len1 + len1) * sizeof (uint64_t));
  memcpy(tmp1, resM, len1 * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, tmp1, res);
}

void
Hacl_BenchBignum_mod_exp_fw_consttime_amm_precomp(
  uint32_t l,
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k10 = *k;
  uint32_t len1 = k10.len;
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t aM[len1];
  memset(aM, 0U, len1 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t c0[len1 + len1];
  memset(c0, 0U, (len1 + len1) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len1);
  uint64_t tmp0[(uint32_t)4U * len1];
  memset(tmp0, 0U, (uint32_t)4U * len1 * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len1, a, k1.r2, tmp0, c0);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, c0, aM);
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t resM[len1];
  memset(resM, 0U, len1 * sizeof (uint64_t));
  uint32_t bLen;
  if (bBits == (uint32_t)0U)
  {
    bLen = (uint32_t)1U;
  }
  else
  {
    bLen = (bBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t tmp[len1 + len1];
  memset(tmp, 0U, (len1 + len1) * sizeof (uint64_t));
  memcpy(tmp, k1.r2, len1 * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, tmp, resM);
  KRML_CHECK_SIZE(sizeof (uint64_t), ((uint32_t)1U << l) * len1);
  uint64_t table[((uint32_t)1U << l) * len1];
  memset(table, 0U, ((uint32_t)1U << l) * len1 * sizeof (uint64_t));
  memcpy(table, resM, len1 * sizeof (uint64_t));
  uint64_t *t1 = table + len1;
  memcpy(t1, aM, len1 * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < ((uint32_t)1U << l) - (uint32_t)1U; i++)
  {
    uint64_t *t11 = table + i * len1;
    uint64_t *t2 = table + i * len1 + len1;
    Hacl_Bignum_AlmostMontgomery_bn_almost_mont_mul_u64(len1, k1.n, k1.mu, aM, t11, t2);
  }
  if (bBits % l != (uint32_t)0U)
  {
    uint64_t mask_l = ((uint64_t)1U << l) - (uint64_t)1U;
    uint32_t i0 = bBits / l * l / (uint32_t)64U;
    uint32_t j = bBits / l * l % (uint32_t)64U;
    uint64_t p1 = b[i0] >> j;
    uint64_t ite;
    if (i0 + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i0 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_c = ite & mask_l;
    memcpy(resM, table, len1 * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < ((uint32_t)1U << l) - (uint32_t)1U; i1++)
    {
      uint64_t c = FStar_UInt64_eq_mask(bits_c, (uint64_t)(i1 + (uint32_t)1U));
      uint64_t *res_j = table + (i1 + (uint32_t)1U) * len1;
      for (uint32_t i = (uint32_t)0U; i < len1; i++)
      {
        uint64_t *os = resM;
        uint64_t x = (c & res_j[i]) | (~c & resM[i]);
        os[i] = x;
      }
    }
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < bBits / l; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < l; i++)
    {
      Hacl_Bignum_AlmostMontgomery_bn_almost_mont_sqr_u64(len1, k1.n, k1.mu, resM, resM);
    }
    uint32_t bk = bBits - bBits % l;
    uint64_t mask_l = ((uint64_t)1U << l) - (uint64_t)1U;
    uint32_t i1 = (bk - l * i0 - l) / (uint32_t)64U;
    uint32_t j = (bk - l * i0 - l) % (uint32_t)64U;
    uint64_t p1 = b[i1] >> j;
    uint64_t ite;
    if (i1 + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_l = ite & mask_l;
    KRML_CHECK_SIZE(sizeof (uint64_t), len1);
    uint64_t a_bits_l[len1];
    memset(a_bits_l, 0U, len1 * sizeof (uint64_t));
    memcpy(a_bits_l, table, len1 * sizeof (uint64_t));
    for (uint32_t i2 = (uint32_t)0U; i2 < ((uint32_t)1U << l) - (uint32_t)1U; i2++)
    {
      uint64_t c = FStar_UInt64_eq_mask(bits_l, (uint64_t)(i2 + (uint32_t)1U));
      uint64_t *res_j = table + (i2 + (uint32_t)1U) * len1;
      for (uint32_t i = (uint32_t)0U; i < len1; i++)
      {
        uint64_t *os = a_bits_l;
        uint64_t x = (c & res_j[i]) | (~c & a_bits_l[i]);
        os[i] = x;
      }
    }
    Hacl_Bignum_AlmostMontgomery_bn_almost_mont_mul_u64(len1, k1.n, k1.mu, resM, a_bits_l, resM);
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t tmp1[len1 + len1];
  memset(tmp1, 0U, (len1 + len1) * sizeof (uint64_t));
  memcpy(tmp1, resM, len1 * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len1, k1.n, k1.mu, tmp1, res);
}

