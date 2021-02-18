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


#include "Hacl_FFDHE4096.h"

static inline void add_mod_n(uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint64_t t1 = a[(uint32_t)4U * i];
    uint64_t t20 = b[(uint32_t)4U * i];
    uint64_t *res_i0 = res + (uint32_t)4U * i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, res_i0);
    uint64_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = res + (uint32_t)4U * i + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, res_i1);
    uint64_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = res + (uint32_t)4U * i + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, res_i2);
    uint64_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = res + (uint32_t)4U * i + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, res_i);
  }
  for (uint32_t i = (uint32_t)64U; i < (uint32_t)64U; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = res + i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, res_i);
  }
  uint64_t c00 = c0;
  uint64_t tmp[64U] = { 0U };
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint64_t t1 = res[(uint32_t)4U * i];
    uint64_t t20 = n[(uint32_t)4U * i];
    uint64_t *res_i0 = tmp + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tmp + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tmp + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tmp + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = (uint32_t)64U; i < (uint32_t)64U; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    uint64_t *res_i = tmp + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
  }
  uint64_t c1 = c;
  uint64_t c2 = c00 - c1;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

static inline void mul(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t tmp[256U] = { 0U };
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64((uint32_t)64U, a, b, tmp, res);
}

static inline void precomp(uint32_t nBits, uint64_t *n, uint64_t *res)
{
  memset(res, 0U, (uint32_t)64U * sizeof (uint64_t));
  uint32_t i = nBits / (uint32_t)64U;
  uint32_t j = nBits % (uint32_t)64U;
  res[i] = res[i] | (uint64_t)1U << j;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)8192U - nBits; i0++)
  {
    add_mod_n(n, res, res, res);
  }
}

static inline void reduction(uint64_t *n, uint64_t nInv, uint64_t *c, uint64_t *res)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)64U; i0++)
  {
    uint64_t qj = nInv * c[i0];
    uint64_t *res_j0 = c + i0;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint64_t a_i = n[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j0 + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i0);
      uint64_t a_i0 = n[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j0 + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, qj, c1, res_i1);
      uint64_t a_i1 = n[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j0 + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, qj, c1, res_i2);
      uint64_t a_i2 = n[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j0 + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, qj, c1, res_i);
    }
    for (uint32_t i = (uint32_t)64U; i < (uint32_t)64U; i++)
    {
      uint64_t a_i = n[i];
      uint64_t *res_i = res_j0 + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i);
    }
    uint64_t r = c1;
    uint64_t c10 = r;
    uint64_t *resb = c + (uint32_t)64U + i0;
    uint64_t res_j = c[(uint32_t)64U + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c10, res_j, resb);
  }
  memcpy(res, c + (uint32_t)64U, (uint32_t)64U * sizeof (uint64_t));
  uint64_t c01 = c0;
  uint64_t tmp[64U] = { 0U };
  uint64_t c1 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint64_t t1 = res[(uint32_t)4U * i];
    uint64_t t20 = n[(uint32_t)4U * i];
    uint64_t *res_i0 = tmp + (uint32_t)4U * i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, res_i0);
    uint64_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tmp + (uint32_t)4U * i + (uint32_t)1U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t10, t21, res_i1);
    uint64_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tmp + (uint32_t)4U * i + (uint32_t)2U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t11, t22, res_i2);
    uint64_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tmp + (uint32_t)4U * i + (uint32_t)3U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t12, t2, res_i);
  }
  for (uint32_t i = (uint32_t)64U; i < (uint32_t)64U; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    uint64_t *res_i = tmp + i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, res_i);
  }
  uint64_t c10 = c1;
  uint64_t c2 = c01 - c10;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

static inline void
mont_mul(uint64_t *n, uint64_t nInv_u64, uint64_t *aM, uint64_t *bM, uint64_t *resM)
{
  uint64_t c[128U] = { 0U };
  uint64_t tmp[256U] = { 0U };
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64((uint32_t)64U, aM, bM, tmp, c);
  reduction(n, nInv_u64, c, resM);
}

static inline void mont_sqr(uint64_t *n, uint64_t nInv_u64, uint64_t *aM, uint64_t *resM)
{
  uint64_t c[128U] = { 0U };
  uint64_t tmp[256U] = { 0U };
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64((uint32_t)64U, aM, tmp, c);
  reduction(n, nInv_u64, c, resM);
}

static inline void
mod_exp_fw_ct_precompr2(
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint32_t l,
  uint64_t *r2,
  uint64_t *res
)
{
  uint32_t bLen = (bBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint64_t nInv = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  uint64_t aM[64U] = { 0U };
  uint64_t accM[64U] = { 0U };
  uint64_t c0[128U] = { 0U };
  mul(a, r2, c0);
  reduction(n, nInv, c0, aM);
  uint64_t one[64U] = { 0U };
  memset(one, 0U, (uint32_t)64U * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  uint64_t c2[128U] = { 0U };
  mul(one, r2, c2);
  reduction(n, nInv, c2, accM);
  uint32_t table_len = (uint32_t)1U << l;
  KRML_CHECK_SIZE(sizeof (uint64_t), table_len * (uint32_t)64U);
  uint64_t *table = alloca(table_len * (uint32_t)64U * sizeof (uint64_t));
  memset(table, 0U, table_len * (uint32_t)64U * sizeof (uint64_t));
  memcpy(table, accM, (uint32_t)64U * sizeof (uint64_t));
  uint64_t *t1 = table + (uint32_t)64U;
  memcpy(t1, aM, (uint32_t)64U * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < table_len - (uint32_t)2U; i++)
  {
    uint64_t *t11 = table + (i + (uint32_t)1U) * (uint32_t)64U;
    uint64_t *t2 = table + (i + (uint32_t)2U) * (uint32_t)64U;
    mont_mul(n, nInv, t11, aM, t2);
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < bBits / l; i0++)
  {
    uint64_t mask_l = ((uint64_t)1U << l) - (uint64_t)1U;
    uint32_t i1 = (bBits - l * i0 - l) / (uint32_t)64U;
    uint32_t j = (bBits - l * i0 - l) % (uint32_t)64U;
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
    uint64_t a_bits_l[64U] = { 0U };
    memcpy(a_bits_l, table, (uint32_t)64U * sizeof (uint64_t));
    for (uint32_t i2 = (uint32_t)0U; i2 < table_len - (uint32_t)1U; i2++)
    {
      uint64_t c = FStar_UInt64_eq_mask(bits_l, (uint64_t)(i2 + (uint32_t)1U));
      uint64_t *res_j = table + (i2 + (uint32_t)1U) * (uint32_t)64U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
      {
        uint64_t *os = a_bits_l;
        uint64_t x = (c & res_j[i]) | (~c & a_bits_l[i]);
        os[i] = x;
      }
    }
    for (uint32_t i = (uint32_t)0U; i < l; i++)
    {
      mont_sqr(n, nInv, accM, accM);
    }
    mont_mul(n, nInv, accM, a_bits_l, accM);
  }
  if (!(bBits % l == (uint32_t)0U))
  {
    uint32_t c = bBits % l;
    uint32_t c10 = bBits % l;
    uint64_t mask_l = ((uint64_t)1U << c10) - (uint64_t)1U;
    uint32_t i0 = (uint32_t)0U;
    uint32_t j = (uint32_t)0U;
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
    uint64_t bits_c0 = bits_c;
    uint64_t a_bits_c[64U] = { 0U };
    memcpy(a_bits_c, table, (uint32_t)64U * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < table_len - (uint32_t)1U; i1++)
    {
      uint64_t c1 = FStar_UInt64_eq_mask(bits_c0, (uint64_t)(i1 + (uint32_t)1U));
      uint64_t *res_j = table + (i1 + (uint32_t)1U) * (uint32_t)64U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
      {
        uint64_t *os = a_bits_c;
        uint64_t x = (c1 & res_j[i]) | (~c1 & a_bits_c[i]);
        os[i] = x;
      }
    }
    for (uint32_t i = (uint32_t)0U; i < c; i++)
    {
      mont_sqr(n, nInv, accM, accM);
    }
    mont_mul(n, nInv, accM, a_bits_c, accM);
  }
  uint64_t tmp[128U] = { 0U };
  memcpy(tmp, accM, (uint32_t)64U * sizeof (uint64_t));
  reduction(n, nInv, tmp, res);
}

static inline void ffdhe_precomp_p(uint64_t *p_r2_n)
{
  uint32_t nLen = ((uint32_t)512U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint64_t *p_n = p_r2_n;
  uint64_t *r2_n = p_r2_n + nLen;
  uint8_t p_s[512U] = { 0U };
  const uint8_t *p = Hacl_Impl_FFDHE_Constants_ffdhe_p4096;
  uint32_t len1 = Hacl_Impl_FFDHE_ffdhe_len(Spec_FFDHE_FFDHE4096);
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint8_t *os = p_s;
    uint8_t x = p[i];
    os[i] = x;
  }
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64((uint32_t)512U, p_s, p_n);
  precomp((uint32_t)4095U, p_n, r2_n);
}

static inline uint64_t ffdhe_check_pk(uint64_t *pk_n, uint64_t *p_n)
{
  uint32_t nLen = ((uint32_t)512U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *p_n1 = alloca(nLen * sizeof (uint64_t));
  memset(p_n1, 0U, nLen * sizeof (uint64_t));
  uint64_t
  c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64((uint64_t)0U, p_n[0U], (uint64_t)1U, p_n1);
  uint64_t c1;
  if ((uint32_t)1U < nLen)
  {
    uint32_t rLen = nLen - (uint32_t)1U;
    uint64_t *a1 = p_n + (uint32_t)1U;
    uint64_t *res1 = p_n1 + (uint32_t)1U;
    uint64_t c = c0;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint64_t t1 = a1[(uint32_t)4U * i];
      uint64_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, (uint64_t)0U, res_i0);
      uint64_t t10 = a1[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, (uint64_t)0U, res_i1);
      uint64_t t11 = a1[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, (uint64_t)0U, res_i2);
      uint64_t t12 = a1[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, (uint64_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint64_t t1 = a1[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, (uint64_t)0U, res_i);
    }
    uint64_t c10 = c;
    c1 = c10;
  }
  else
  {
    c1 = c0;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *b2 = alloca(nLen * sizeof (uint64_t));
  memset(b2, 0U, nLen * sizeof (uint64_t));
  uint32_t i0 = (uint32_t)0U;
  uint32_t j = (uint32_t)0U;
  b2[i0] = b2[i0] | (uint64_t)1U << j;
  uint64_t acc0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < nLen; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(b2[i], pk_n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(b2[i], pk_n[i]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
  }
  uint64_t res = acc0;
  uint64_t m0 = res;
  uint64_t acc = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < nLen; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(pk_n[i], p_n1[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(pk_n[i], p_n1[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
  }
  uint64_t m1 = acc;
  return m0 & m1;
}

static inline void
ffdhe_compute_exp(uint64_t *p_r2_n, uint64_t *sk_n, uint64_t *b_n, uint8_t *res)
{
  uint32_t nLen = ((uint32_t)512U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint64_t *p_n = p_r2_n;
  uint64_t *r2_n = p_r2_n + nLen;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *res_n = alloca(nLen * sizeof (uint64_t));
  memset(res_n, 0U, nLen * sizeof (uint64_t));
  mod_exp_fw_ct_precompr2(p_n, b_n, (uint32_t)64U * nLen, sk_n, (uint32_t)4U, r2_n, res_n);
  Hacl_Bignum_Convert_bn_to_bytes_be_uint64((uint32_t)512U, res_n, res);
}

uint64_t *Hacl_FFDHE4096_new_ffdhe_precomp_p()
{
  uint32_t nLen = ((uint32_t)512U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen + nLen);
  uint64_t *res = KRML_HOST_CALLOC(nLen + nLen, sizeof (uint64_t));
  if (res == NULL)
  {
    return res;
  }
  uint64_t *res1 = res;
  uint64_t *res2 = res1;
  ffdhe_precomp_p(res2);
  return res2;
}

void Hacl_FFDHE4096_ffdhe_secret_to_public_precomp(uint64_t *p_r2_n, uint8_t *sk, uint8_t *pk)
{
  uint32_t nLen = ((uint32_t)512U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *g_n = alloca(nLen * sizeof (uint64_t));
  memset(g_n, 0U, nLen * sizeof (uint64_t));
  uint8_t g = (uint8_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
  {
    uint8_t *os = &g;
    uint8_t x = Hacl_Impl_FFDHE_Constants_ffdhe_g2[i];
    os[i] = x;
  }
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64((uint32_t)1U, &g, g_n);
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *sk_n = alloca(nLen * sizeof (uint64_t));
  memset(sk_n, 0U, nLen * sizeof (uint64_t));
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64((uint32_t)512U, sk, sk_n);
  ffdhe_compute_exp(p_r2_n, sk_n, g_n, pk);
}

void Hacl_FFDHE4096_ffdhe_secret_to_public(uint8_t *sk, uint8_t *pk)
{
  uint32_t nLen = ((uint32_t)512U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen + nLen);
  uint64_t *p_r2_n = alloca((nLen + nLen) * sizeof (uint64_t));
  memset(p_r2_n, 0U, (nLen + nLen) * sizeof (uint64_t));
  ffdhe_precomp_p(p_r2_n);
  Hacl_FFDHE4096_ffdhe_secret_to_public_precomp(p_r2_n, sk, pk);
}

uint64_t
Hacl_FFDHE4096_ffdhe_shared_secret_precomp(
  uint64_t *p_r2_n,
  uint8_t *sk,
  uint8_t *pk,
  uint8_t *ss
)
{
  uint32_t nLen = ((uint32_t)512U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint64_t *p_n = p_r2_n;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *sk_n = alloca(nLen * sizeof (uint64_t));
  memset(sk_n, 0U, nLen * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *pk_n = alloca(nLen * sizeof (uint64_t));
  memset(pk_n, 0U, nLen * sizeof (uint64_t));
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64((uint32_t)512U, sk, sk_n);
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64((uint32_t)512U, pk, pk_n);
  uint64_t m = ffdhe_check_pk(pk_n, p_n);
  if (m == (uint64_t)0xFFFFFFFFFFFFFFFFU)
  {
    ffdhe_compute_exp(p_r2_n, sk_n, pk_n, ss);
  }
  return m;
}

uint64_t Hacl_FFDHE4096_ffdhe_shared_secret(uint8_t *sk, uint8_t *pk, uint8_t *ss)
{
  uint32_t nLen = ((uint32_t)512U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen + nLen);
  uint64_t *p_n = alloca((nLen + nLen) * sizeof (uint64_t));
  memset(p_n, 0U, (nLen + nLen) * sizeof (uint64_t));
  ffdhe_precomp_p(p_n);
  uint64_t m = Hacl_FFDHE4096_ffdhe_shared_secret_precomp(p_n, sk, pk, ss);
  return m;
}

