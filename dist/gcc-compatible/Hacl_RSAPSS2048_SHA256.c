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


#include "Hacl_RSAPSS2048_SHA256.h"

static inline void add_mod_n(uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t t1 = a[(uint32_t)4U * i];
    uint64_t t20 = b[(uint32_t)4U * i];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, res + (uint32_t)4U * i);
    uint64_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, res + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, res + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, res + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = (uint32_t)32U; i < (uint32_t)32U; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, res + i);
  }
  uint64_t c00 = c0;
  uint64_t tmp[32U] = { 0U };
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t t1 = res[(uint32_t)4U * i];
    uint64_t t20 = n[(uint32_t)4U * i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, tmp + (uint32_t)4U * i);
    uint64_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, tmp + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, tmp + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, tmp + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = (uint32_t)32U; i < (uint32_t)32U; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, tmp + i);
  }
  uint64_t c1 = c;
  uint64_t c2 = c00 - c1;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

static inline void mul(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t tmp[128U] = { 0U };
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64((uint32_t)32U, a, b, tmp, res);
}

static inline void precomp(uint32_t nBits, uint64_t *n, uint64_t *res)
{
  memset(res, 0U, (uint32_t)32U * sizeof (uint64_t));
  uint32_t i = nBits / (uint32_t)64U;
  uint32_t j = nBits % (uint32_t)64U;
  res[i] = res[i] | (uint64_t)1U << j;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4096U - nBits; i0++)
  {
    add_mod_n(n, res, res, res);
  }
}

static inline void reduction(uint64_t *n, uint64_t nInv, uint64_t *c, uint64_t *res)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)32U; i0++)
  {
    uint64_t qj = nInv * c[i0];
    uint64_t *res_ = c + i0;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
    {
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(n[(uint32_t)4U * i], qj, c1, res_ + (uint32_t)4U * i);
      c1 =
        Hacl_Bignum_Base_mul_wide_add2_u64(n[(uint32_t)4U * i + (uint32_t)1U],
          qj,
          c1,
          res_ + (uint32_t)4U * i + (uint32_t)1U);
      c1 =
        Hacl_Bignum_Base_mul_wide_add2_u64(n[(uint32_t)4U * i + (uint32_t)2U],
          qj,
          c1,
          res_ + (uint32_t)4U * i + (uint32_t)2U);
      c1 =
        Hacl_Bignum_Base_mul_wide_add2_u64(n[(uint32_t)4U * i + (uint32_t)3U],
          qj,
          c1,
          res_ + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = (uint32_t)32U; i < (uint32_t)32U; i++)
    {
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(n[i], qj, c1, res_ + i);
    }
    uint64_t r = c1;
    uint64_t c10 = r;
    c0 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c0,
        c10,
        c[(uint32_t)32U + i0],
        c + (uint32_t)32U + i0);
  }
  memcpy(res, c + (uint32_t)32U, (uint32_t)32U * sizeof (uint64_t));
  uint64_t uu____0 = c0;
  uint64_t tmp[32U] = { 0U };
  uint64_t c1 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t t1 = res[(uint32_t)4U * i];
    uint64_t t20 = n[(uint32_t)4U * i];
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tmp + (uint32_t)4U * i);
    uint64_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
    c1 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
        t10,
        t21,
        tmp + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
    c1 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
        t11,
        t22,
        tmp + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t12, t2, tmp + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = (uint32_t)32U; i < (uint32_t)32U; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tmp + i);
  }
  uint64_t c10 = c1;
  uint64_t c2 = uu____0 - c10;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

static inline void
mont_mul(uint64_t *n, uint64_t nInv_u64, uint64_t *aM, uint64_t *bM, uint64_t *resM)
{
  uint64_t c[64U] = { 0U };
  uint64_t tmp[128U] = { 0U };
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64((uint32_t)32U, aM, bM, tmp, c);
  reduction(n, nInv_u64, c, resM);
}

static inline void mont_sqr(uint64_t *n, uint64_t nInv_u64, uint64_t *aM, uint64_t *resM)
{
  uint64_t c[64U] = { 0U };
  uint64_t tmp[128U] = { 0U };
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64((uint32_t)32U, aM, tmp, c);
  reduction(n, nInv_u64, c, resM);
}

static inline void
mod_exp_raw_precompr2(
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *r2,
  uint64_t *res
)
{
  uint64_t nInv = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  uint64_t aM[32U] = { 0U };
  uint64_t accM[32U] = { 0U };
  uint64_t c0[64U] = { 0U };
  mul(a, r2, c0);
  reduction(n, nInv, c0, aM);
  uint64_t one[32U] = { 0U };
  memset(one, 0U, (uint32_t)32U * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  uint64_t c[64U] = { 0U };
  mul(one, r2, c);
  reduction(n, nInv, c, accM);
  for (uint32_t i = (uint32_t)0U; i < bBits; i++)
  {
    uint32_t i1 = i / (uint32_t)64U;
    uint32_t j = i % (uint32_t)64U;
    uint64_t tmp = b[i1];
    uint64_t bit = tmp >> j & (uint64_t)1U;
    if (!(bit == (uint64_t)0U))
    {
      mont_mul(n, nInv, accM, aM, accM);
    }
    mont_sqr(n, nInv, aM, aM);
  }
  uint64_t tmp[64U] = { 0U };
  memcpy(tmp, accM, (uint32_t)32U * sizeof (uint64_t));
  reduction(n, nInv, tmp, res);
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
  uint64_t aM[32U] = { 0U };
  uint64_t accM[32U] = { 0U };
  uint64_t c0[64U] = { 0U };
  mul(a, r2, c0);
  reduction(n, nInv, c0, aM);
  uint64_t one[32U] = { 0U };
  memset(one, 0U, (uint32_t)32U * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  uint64_t c2[64U] = { 0U };
  mul(one, r2, c2);
  reduction(n, nInv, c2, accM);
  uint32_t table_len = (uint32_t)1U << l;
  KRML_CHECK_SIZE(sizeof (uint64_t), table_len * (uint32_t)32U);
  uint64_t table[table_len * (uint32_t)32U];
  memset(table, 0U, table_len * (uint32_t)32U * sizeof (uint64_t));
  memcpy(table, accM, (uint32_t)32U * sizeof (uint64_t));
  uint64_t *t1 = table + (uint32_t)32U;
  memcpy(t1, aM, (uint32_t)32U * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < table_len - (uint32_t)2U; i++)
  {
    uint64_t *t11 = table + (i + (uint32_t)1U) * (uint32_t)32U;
    uint64_t *t2 = table + (i + (uint32_t)2U) * (uint32_t)32U;
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
    uint64_t a_bits_l[32U] = { 0U };
    memcpy(a_bits_l, table, (uint32_t)32U * sizeof (uint64_t));
    for (uint32_t i2 = (uint32_t)0U; i2 < table_len - (uint32_t)1U; i2++)
    {
      uint64_t c = FStar_UInt64_eq_mask(bits_l, (uint64_t)(i2 + (uint32_t)1U));
      uint64_t *res_j = table + (i2 + (uint32_t)1U) * (uint32_t)32U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
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
    uint64_t a_bits_c[32U] = { 0U };
    memcpy(a_bits_c, table, (uint32_t)32U * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < table_len - (uint32_t)1U; i1++)
    {
      uint64_t c1 = FStar_UInt64_eq_mask(bits_c0, (uint64_t)(i1 + (uint32_t)1U));
      uint64_t *res_j = table + (i1 + (uint32_t)1U) * (uint32_t)32U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
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
  uint64_t tmp[64U] = { 0U };
  memcpy(tmp, accM, (uint32_t)32U * sizeof (uint64_t));
  reduction(n, nInv, tmp, res);
}

static inline bool load_pkey(uint32_t eBits, uint8_t *nb, uint8_t *eb, uint64_t *pkey)
{
  uint32_t nbLen = ((uint32_t)2048U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t ebLen = (eBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t nLen = ((uint32_t)2048U - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint64_t *n = pkey;
  uint64_t *r2 = pkey + nLen;
  uint64_t *e = pkey + nLen + nLen;
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(nbLen, nb, n);
  precomp((uint32_t)2047U, n, r2);
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(ebLen, eb, e);
  uint64_t m0 = Hacl_Impl_RSAPSS_Keys_check_modulus_u64((uint32_t)2048U, n);
  uint64_t m1 = Hacl_Impl_RSAPSS_Keys_check_exponent_u64(eBits, e);
  uint64_t m = m0 & m1;
  return m == (uint64_t)0xFFFFFFFFFFFFFFFFU;
}

static inline bool
load_skey(
  uint32_t eBits,
  uint32_t dBits,
  uint8_t *nb,
  uint8_t *eb,
  uint8_t *db,
  uint64_t *skey
)
{
  uint32_t dbLen = (dBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t nLen = ((uint32_t)2048U - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen = (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t pkeyLen = nLen + nLen + eLen;
  uint64_t *pkey = skey;
  uint64_t *d = skey + pkeyLen;
  bool b = load_pkey(eBits, nb, eb, pkey);
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(dbLen, db, d);
  uint64_t m1 = Hacl_Impl_RSAPSS_Keys_check_exponent_u64(dBits, d);
  return b && m1 == (uint64_t)0xFFFFFFFFFFFFFFFFU;
}

bool
Hacl_RSAPSS2048_SHA256_rsapss_sign(
  uint32_t eBits,
  uint32_t dBits,
  uint64_t *skey,
  uint32_t sLen,
  uint8_t *salt,
  uint32_t msgLen,
  uint8_t *msg,
  uint8_t *sgnt
)
{
  uint32_t hLen = Hacl_Impl_RSAPSS_MGF_hash_len(Spec_Hash_Definitions_SHA2_256);
  bool
  b =
    sLen
    <= (uint32_t)0xffffffffU - hLen - (uint32_t)8U
    && sLen + hLen + (uint32_t)2U <= ((uint32_t)2047U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  if (b)
  {
    uint32_t nLen = ((uint32_t)2048U - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
    KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
    uint64_t m[nLen];
    memset(m, 0U, nLen * sizeof (uint64_t));
    uint32_t emBits = (uint32_t)2047U;
    uint32_t emLen = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
    KRML_CHECK_SIZE(sizeof (uint8_t), emLen);
    uint8_t em[emLen];
    memset(em, 0U, emLen * sizeof (uint8_t));
    Hacl_Impl_RSAPSS_Padding_pss_encode(Spec_Hash_Definitions_SHA2_256,
      sLen,
      salt,
      msgLen,
      msg,
      emBits,
      em);
    Hacl_Bignum_Convert_bn_from_bytes_be_uint64(emLen, em, m);
    uint32_t nLen1 = ((uint32_t)2048U - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
    uint32_t k = ((uint32_t)2048U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
    KRML_CHECK_SIZE(sizeof (uint64_t), nLen1);
    uint64_t s[nLen1];
    memset(s, 0U, nLen1 * sizeof (uint64_t));
    KRML_CHECK_SIZE(sizeof (uint64_t), nLen1);
    uint64_t m_[nLen1];
    memset(m_, 0U, nLen1 * sizeof (uint64_t));
    uint32_t nLen2 = ((uint32_t)2048U - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
    uint32_t eLen = (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
    uint64_t *n = skey;
    uint64_t *r2 = skey + nLen2;
    uint64_t *e = skey + nLen2 + nLen2;
    uint64_t *d = skey + nLen2 + nLen2 + eLen;
    mod_exp_fw_ct_precompr2(n, m, dBits, d, (uint32_t)4U, r2, s);
    mod_exp_raw_precompr2(n, s, eBits, e, r2, m_);
    uint64_t mask = (uint64_t)0xFFFFFFFFFFFFFFFFU;
    for (uint32_t i = (uint32_t)0U; i < nLen2; i++)
    {
      uint64_t uu____0 = FStar_UInt64_eq_mask(m[i], m_[i]);
      mask = uu____0 & mask;
    }
    uint64_t mask1 = mask;
    uint64_t eq_m = mask1;
    for (uint32_t i = (uint32_t)0U; i < nLen2; i++)
    {
      uint64_t *os = s;
      uint64_t x = s[i];
      uint64_t x0 = eq_m & x;
      os[i] = x0;
    }
    bool eq_b = eq_m == (uint64_t)0xFFFFFFFFFFFFFFFFU;
    Hacl_Bignum_Convert_bn_to_bytes_be_uint64(k, s, sgnt);
    bool eq_b0 = eq_b;
    return eq_b0;
  }
  return false;
}

bool
Hacl_RSAPSS2048_SHA256_rsapss_verify(
  uint32_t eBits,
  uint64_t *pkey,
  uint32_t sLen,
  uint32_t k,
  uint8_t *sgnt,
  uint32_t msgLen,
  uint8_t *msg
)
{
  uint32_t hLen = Hacl_Impl_RSAPSS_MGF_hash_len(Spec_Hash_Definitions_SHA2_256);
  bool
  b =
    sLen
    <= (uint32_t)0xffffffffU - hLen - (uint32_t)8U
    && k == ((uint32_t)2048U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  if (b)
  {
    uint32_t nLen = ((uint32_t)2048U - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
    KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
    uint64_t m[nLen];
    memset(m, 0U, nLen * sizeof (uint64_t));
    uint32_t nLen1 = ((uint32_t)2048U - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
    uint32_t k1 = ((uint32_t)2048U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
    KRML_CHECK_SIZE(sizeof (uint64_t), nLen1);
    uint64_t s[nLen1];
    memset(s, 0U, nLen1 * sizeof (uint64_t));
    Hacl_Bignum_Convert_bn_from_bytes_be_uint64(k1, sgnt, s);
    uint32_t nLen2 = ((uint32_t)2048U - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
    uint64_t *n = pkey;
    uint64_t *r2 = pkey + nLen2;
    uint64_t *e = pkey + nLen2 + nLen2;
    uint64_t acc = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < nLen2; i++)
    {
      uint64_t beq = FStar_UInt64_eq_mask(s[i], n[i]);
      uint64_t blt = ~FStar_UInt64_gte_mask(s[i], n[i]);
      acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
    }
    uint64_t mask = acc;
    bool res;
    if (mask == (uint64_t)0xFFFFFFFFFFFFFFFFU)
    {
      mod_exp_raw_precompr2(n, s, eBits, e, r2, m);
      bool ite;
      if (!((uint32_t)7U == (uint32_t)0U))
      {
        ite = true;
      }
      else
      {
        uint32_t i = (uint32_t)31U;
        uint32_t j = (uint32_t)63U;
        uint64_t tmp = m[i];
        uint64_t get_bit = tmp >> j & (uint64_t)1U;
        ite = get_bit == (uint64_t)0U;
      }
      if (ite)
      {
        res = true;
      }
      else
      {
        res = false;
      }
    }
    else
    {
      res = false;
    }
    bool b1 = res;
    bool b10 = b1;
    if (b10)
    {
      uint32_t emBits = (uint32_t)2047U;
      uint32_t emLen = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
      KRML_CHECK_SIZE(sizeof (uint8_t), emLen);
      uint8_t em[emLen];
      memset(em, 0U, emLen * sizeof (uint8_t));
      uint64_t *m1 = m;
      Hacl_Bignum_Convert_bn_to_bytes_be_uint64(emLen, m1, em);
      bool
      res0 =
        Hacl_Impl_RSAPSS_Padding_pss_verify(Spec_Hash_Definitions_SHA2_256,
          sLen,
          msgLen,
          msg,
          emBits,
          em);
      return res0;
    }
    return false;
  }
  return false;
}

uint64_t *Hacl_RSAPSS2048_SHA256_new_rsapss_load_pkey(uint32_t eBits, uint8_t *nb, uint8_t *eb)
{
  uint32_t nLen = ((uint32_t)2048U - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen = (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t pkeyLen = nLen + nLen + eLen;
  uint32_t nLen1 = ((uint32_t)2048U - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen1 = (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  if
  (
    !((uint32_t)1U
    < (uint32_t)2048U
    && (uint32_t)0U < eBits
    && nLen1 <= (uint32_t)33554431U
    && eLen1 <= (uint32_t)67108863U
    && nLen1 + nLen1 <= (uint32_t)0xffffffffU - eLen1)
  )
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), pkeyLen);
  uint64_t *pkey = KRML_HOST_CALLOC(pkeyLen, sizeof (uint64_t));
  if (pkey == NULL)
  {
    return pkey;
  }
  uint64_t *pkey1 = pkey;
  uint64_t *pkey2 = pkey1;
  bool b = load_pkey(eBits, nb, eb, pkey2);
  if (b)
  {
    return pkey2;
  }
  return NULL;
}

uint64_t
*Hacl_RSAPSS2048_SHA256_new_rsapss_load_skey(
  uint32_t eBits,
  uint32_t dBits,
  uint8_t *nb,
  uint8_t *eb,
  uint8_t *db
)
{
  uint32_t nLen = ((uint32_t)2048U - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen = (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t dLen = (dBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t skeyLen = nLen + nLen + eLen + dLen;
  uint32_t nLen1 = ((uint32_t)2048U - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen1 = (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t dLen1 = (dBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t nLen2 = ((uint32_t)2048U - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen2 = (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  if
  (
    !((uint32_t)1U
    < (uint32_t)2048U
    && (uint32_t)0U < eBits
    && nLen2 <= (uint32_t)33554431U
    && eLen2 <= (uint32_t)67108863U
    && nLen2 + nLen2 <= (uint32_t)0xffffffffU - eLen2
    && (uint32_t)0U < dBits
    && dLen1 <= (uint32_t)67108863U
    && (uint32_t)2U * nLen1 <= (uint32_t)0xffffffffU - eLen1 - dLen1)
  )
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), skeyLen);
  uint64_t *skey = KRML_HOST_CALLOC(skeyLen, sizeof (uint64_t));
  if (skey == NULL)
  {
    return skey;
  }
  uint64_t *skey1 = skey;
  uint64_t *skey2 = skey1;
  bool b = load_skey(eBits, dBits, nb, eb, db, skey2);
  if (b)
  {
    return skey2;
  }
  return NULL;
}

bool
Hacl_RSAPSS2048_SHA256_rsapss_skey_sign(
  uint32_t eBits,
  uint32_t dBits,
  uint8_t *nb,
  uint8_t *eb,
  uint8_t *db,
  uint32_t sLen,
  uint8_t *salt,
  uint32_t msgLen,
  uint8_t *msg,
  uint8_t *sgnt
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t),
    (uint32_t)2U
    * (((uint32_t)2048U - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U)
    + (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U
    + (dBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U);
  uint64_t
  skey[(uint32_t)2U
  * (((uint32_t)2048U - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U)
  + (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U
  + (dBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U];
  memset(skey,
    0U,
    ((uint32_t)2U
    * (((uint32_t)2048U - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U)
    + (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U
    + (dBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U)
    * sizeof (uint64_t));
  bool b = load_skey(eBits, dBits, nb, eb, db, skey);
  if (b)
  {
    return Hacl_RSAPSS2048_SHA256_rsapss_sign(eBits, dBits, skey, sLen, salt, msgLen, msg, sgnt);
  }
  return false;
}

bool
Hacl_RSAPSS2048_SHA256_rsapss_pkey_verify(
  uint32_t eBits,
  uint8_t *nb,
  uint8_t *eb,
  uint32_t sLen,
  uint32_t k,
  uint8_t *sgnt,
  uint32_t msgLen,
  uint8_t *msg
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t),
    (uint32_t)2U
    * (((uint32_t)2048U - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U)
    + (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U);
  uint64_t
  pkey[(uint32_t)2U
  * (((uint32_t)2048U - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U)
  + (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U];
  memset(pkey,
    0U,
    ((uint32_t)2U
    * (((uint32_t)2048U - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U)
    + (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U)
    * sizeof (uint64_t));
  bool b = load_pkey(eBits, nb, eb, pkey);
  if (b)
  {
    return Hacl_RSAPSS2048_SHA256_rsapss_verify(eBits, pkey, sLen, k, sgnt, msgLen, msg);
  }
  return false;
}

