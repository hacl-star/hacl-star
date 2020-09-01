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


#include "Hacl_RSAPSS.h"

static inline void bn_from_bytes_be(uint32_t len, uint8_t *b, uint64_t *res)
{
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t *tmp = alloca(tmpLen * sizeof (uint8_t));
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp + tmpLen - len, b, len * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    uint64_t *os = res;
    uint64_t u = load64_be(tmp + (bnLen - i - (uint32_t)1U) * (uint32_t)8U);
    uint64_t x = u;
    os[i] = x;
  }
}

static inline void bn_to_bytes_be(uint32_t len, uint64_t *b, uint8_t *res)
{
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t *tmp = alloca(tmpLen * sizeof (uint8_t));
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    store64_be(tmp + i * (uint32_t)8U, b[bnLen - i - (uint32_t)1U]);
  }
  memcpy(res, tmp + tmpLen - len, len * sizeof (uint8_t));
}

static void precomp_runtime(uint32_t len, uint32_t modBits, uint64_t *n, uint64_t *res)
{
  memset(res, 0U, len * sizeof (uint64_t));
  Hacl_Bignum_bn_bit_set(len, res, modBits - (uint32_t)1U);
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)128U * len + (uint32_t)129U - modBits; i0++)
  {
    KRML_CHECK_SIZE(sizeof (uint64_t), len);
    uint64_t *tmp = alloca(len * sizeof (uint64_t));
    memset(tmp, 0U, len * sizeof (uint64_t));
    uint64_t c0 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len; i++)
    {
      uint64_t t1 = res[i];
      uint64_t t2 = res[i];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, res + i);
    }
    uint64_t c00 = c0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len; i++)
    {
      uint64_t t1 = res[i];
      uint64_t t2 = n[i];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, tmp + i);
    }
    uint64_t c1 = c;
    uint64_t c2 = c00 - c1;
    for (uint32_t i = (uint32_t)0U; i < len; i++)
    {
      uint64_t *os = res;
      uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
      os[i] = x;
    }
  }
}

static void
mont_reduction_runtime(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv_u64,
  uint64_t *c,
  uint64_t *res
)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < len + (uint32_t)1U; i0++)
  {
    uint64_t qj = nInv_u64 * c[i0];
    uint64_t *res_ = c + i0;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len; i++)
    {
      c1 = Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c1, n[i], qj, res_ + i);
    }
    uint64_t r0 = c1;
    uint64_t c10 = r0;
    uint64_t c2 = c10;
    uint64_t *res2 = c + i0 + len;
    uint64_t *a0 = res2;
    uint64_t *res0 = res2;
    uint64_t c30 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
    {
      uint64_t t1 = a0[i];
      uint64_t t2 = (&c2)[i];
      c30 = Lib_IntTypes_Intrinsics_add_carry_u64(c30, t1, t2, res0 + i);
    }
    uint64_t c0 = c30;
    uint64_t r;
    if ((uint32_t)1U < len + (uint32_t)1U + len + (uint32_t)1U - i0 - len)
    {
      uint32_t rLen = len + (uint32_t)1U + len + (uint32_t)1U - i0 - len - (uint32_t)1U;
      uint64_t *a1 = res2 + (uint32_t)1U;
      uint64_t *res1 = res2 + (uint32_t)1U;
      uint64_t c3 = c0;
      for (uint32_t i = (uint32_t)0U; i < rLen; i++)
      {
        uint64_t t1 = a1[i];
        c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c3, t1, (uint64_t)0U, res1 + i);
      }
      uint64_t c11 = c3;
      r = c11;
    }
    else
    {
      r = c0;
    }
    uint64_t uu____0 = r;
  }
  memcpy(res,
    c + len + (uint32_t)1U,
    (len + (uint32_t)1U + len + (uint32_t)1U - (len + (uint32_t)1U)) * sizeof (uint64_t));
}

static void
to_runtime(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv_u64,
  uint64_t *r2,
  uint64_t *a,
  uint64_t *aM
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + (uint32_t)1U + len + (uint32_t)1U);
  uint64_t *tmp = alloca((len + (uint32_t)1U + len + (uint32_t)1U) * sizeof (uint64_t));
  memset(tmp, 0U, (len + (uint32_t)1U + len + (uint32_t)1U) * sizeof (uint64_t));
  uint64_t *c = tmp;
  uint32_t resLen = len + len;
  memset(c, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < len; i0++)
  {
    uint64_t uu____0 = r2[i0];
    uint64_t *res_ = c + i0;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len; i++)
    {
      c1 = Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c1, a[i], uu____0, res_ + i);
    }
    uint64_t r = c1;
    c[len + i0] = r;
  }
  mont_reduction_runtime(len, n, nInv_u64, tmp, aM);
}

static void
from_runtime(uint32_t len, uint64_t *n, uint64_t nInv_u64, uint64_t *aM, uint64_t *a)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + (uint32_t)1U + len + (uint32_t)1U);
  uint64_t *tmp = alloca((len + (uint32_t)1U + len + (uint32_t)1U) * sizeof (uint64_t));
  memset(tmp, 0U, (len + (uint32_t)1U + len + (uint32_t)1U) * sizeof (uint64_t));
  memcpy(tmp, aM, (len + (uint32_t)1U) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len + (uint32_t)1U);
  uint64_t *a_ = alloca((len + (uint32_t)1U) * sizeof (uint64_t));
  memset(a_, 0U, (len + (uint32_t)1U) * sizeof (uint64_t));
  mont_reduction_runtime(len, n, nInv_u64, tmp, a_);
  memcpy(a, a_, len * sizeof (uint64_t));
}

static void
mul_runtime(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv_u64,
  uint64_t *aM,
  uint64_t *bM,
  uint64_t *resM
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + (uint32_t)1U + len + (uint32_t)1U);
  uint64_t *c = alloca((len + (uint32_t)1U + len + (uint32_t)1U) * sizeof (uint64_t));
  memset(c, 0U, (len + (uint32_t)1U + len + (uint32_t)1U) * sizeof (uint64_t));
  uint32_t resLen = len + (uint32_t)1U + len + (uint32_t)1U;
  memset(c, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < len + (uint32_t)1U; i0++)
  {
    uint64_t uu____0 = bM[i0];
    uint64_t *res_ = c + i0;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len + (uint32_t)1U; i++)
    {
      c1 = Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c1, aM[i], uu____0, res_ + i);
    }
    uint64_t r = c1;
    c[len + (uint32_t)1U + i0] = r;
  }
  mont_reduction_runtime(len, n, nInv_u64, c, resM);
}

static void hash_sha256(uint8_t *mHash, uint32_t msgLen, uint8_t *msg)
{
  Hacl_Hash_SHA2_hash_256(msg, msgLen, mHash);
}

static inline void mgf_sha256(uint32_t len, uint8_t *mgfseed, uint32_t maskLen, uint8_t *res)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), len + (uint32_t)4U);
  uint8_t *mgfseed_counter = alloca((len + (uint32_t)4U) * sizeof (uint8_t));
  memset(mgfseed_counter, 0U, (len + (uint32_t)4U) * sizeof (uint8_t));
  memcpy(mgfseed_counter, mgfseed, len * sizeof (uint8_t));
  uint32_t n = (maskLen - (uint32_t)1U) / (uint32_t)32U + (uint32_t)1U;
  uint32_t accLen = n * (uint32_t)32U;
  KRML_CHECK_SIZE(sizeof (uint8_t), accLen);
  uint8_t *acc = alloca(accLen * sizeof (uint8_t));
  memset(acc, 0U, accLen * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    uint8_t *uu____0 = acc + i * (uint32_t)32U;
    uint8_t *uu____1 = mgfseed_counter + len;
    uu____1[0U] = (uint8_t)(i >> (uint32_t)24U);
    uu____1[1U] = (uint8_t)(i >> (uint32_t)16U);
    uu____1[2U] = (uint8_t)(i >> (uint32_t)8U);
    uu____1[3U] = (uint8_t)i;
    hash_sha256(uu____0, len + (uint32_t)4U, mgfseed_counter);
  }
  memcpy(res, acc, maskLen * sizeof (uint8_t));
}

static void
bn_mod_exp_loop_runtime(
  uint32_t nLen,
  uint64_t *n,
  uint64_t nInv_u64,
  uint32_t bBits,
  uint32_t bLen,
  uint64_t *b,
  uint64_t *aM,
  uint64_t *accM
)
{
  for (uint32_t i = (uint32_t)0U; i < bBits; i++)
  {
    if (Hacl_Bignum_bn_is_bit_set(bLen, b, i))
    {
      mul_runtime(nLen, n, nInv_u64, aM, accM, accM);
    }
    mul_runtime(nLen, n, nInv_u64, aM, aM, aM);
  }
}

static inline void
bn_mod_exp(
  uint32_t modBits,
  uint32_t nLen,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *acc = alloca(nLen * sizeof (uint64_t));
  memset(acc, 0U, nLen * sizeof (uint64_t));
  memset(acc, 0U, nLen * sizeof (uint64_t));
  acc[0U] = (uint64_t)1U;
  uint32_t rLen = nLen + (uint32_t)1U;
  uint32_t bLen = (bBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint64_t nInv_u64 = Hacl_Bignum_ModInv64_mod_inv_u64(n[0U]);
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *r2 = alloca(nLen * sizeof (uint64_t));
  memset(r2, 0U, nLen * sizeof (uint64_t));
  precomp_runtime(nLen, modBits, n, r2);
  KRML_CHECK_SIZE(sizeof (uint64_t), rLen);
  uint64_t *aM = alloca(rLen * sizeof (uint64_t));
  memset(aM, 0U, rLen * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), rLen);
  uint64_t *accM = alloca(rLen * sizeof (uint64_t));
  memset(accM, 0U, rLen * sizeof (uint64_t));
  to_runtime(nLen, n, nInv_u64, r2, a, aM);
  to_runtime(nLen, n, nInv_u64, r2, acc, accM);
  bn_mod_exp_loop_runtime(nLen, n, nInv_u64, bBits, bLen, b, aM, accM);
  from_runtime(nLen, n, nInv_u64, accM, res);
  uint64_t mask = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *mod_mask = alloca(nLen * sizeof (uint64_t));
  memset(mod_mask, 0U, nLen * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < nLen; i++)
  {
    uint64_t uu____0 = FStar_UInt64_eq_mask(n[i], res[i]);
    mask = uu____0 & mask;
  }
  uint64_t mask1 = mask;
  for (uint32_t i = (uint32_t)0U; i < nLen; i++)
  {
    uint64_t *os = mod_mask;
    uint64_t x = n[i];
    uint64_t x0 = mask1 & x;
    os[i] = x0;
  }
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < nLen; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = mod_mask[i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res + i);
  }
  uint64_t uu____1 = c;
}

static inline void xor_bytes(uint32_t len, uint8_t *b1, uint8_t *b2)
{
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint8_t *os = b1;
    uint8_t x = b1[i] ^ b2[i];
    os[i] = x;
  }
}

static inline void
pss_encode(
  uint32_t sLen,
  uint8_t *salt,
  uint32_t msgLen,
  uint8_t *msg,
  uint32_t emBits,
  uint8_t *em
)
{
  uint8_t m1Hash[32U] = { 0U };
  uint32_t m1Len = (uint32_t)40U + sLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), m1Len);
  uint8_t *m1 = alloca(m1Len * sizeof (uint8_t));
  memset(m1, 0U, m1Len * sizeof (uint8_t));
  hash_sha256(m1 + (uint32_t)8U, msgLen, msg);
  memcpy(m1 + (uint32_t)40U, salt, sLen * sizeof (uint8_t));
  hash_sha256(m1Hash, m1Len, m1);
  uint32_t emLen = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t dbLen = emLen - (uint32_t)32U - (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint8_t), dbLen);
  uint8_t *db = alloca(dbLen * sizeof (uint8_t));
  memset(db, 0U, dbLen * sizeof (uint8_t));
  uint32_t last_before_salt = dbLen - sLen - (uint32_t)1U;
  db[last_before_salt] = (uint8_t)1U;
  memcpy(db + last_before_salt + (uint32_t)1U, salt, sLen * sizeof (uint8_t));
  KRML_CHECK_SIZE(sizeof (uint8_t), dbLen);
  uint8_t *dbMask = alloca(dbLen * sizeof (uint8_t));
  memset(dbMask, 0U, dbLen * sizeof (uint8_t));
  mgf_sha256((uint32_t)32U, m1Hash, dbLen, dbMask);
  xor_bytes(dbLen, db, dbMask);
  uint32_t msBits = emBits % (uint32_t)8U;
  if (msBits > (uint32_t)0U)
  {
    db[0U] = db[0U] & (uint8_t)0xffU >> ((uint32_t)8U - msBits);
  }
  memcpy(em, db, dbLen * sizeof (uint8_t));
  memcpy(em + dbLen, m1Hash, (uint32_t)32U * sizeof (uint8_t));
  em[emLen - (uint32_t)1U] = (uint8_t)0xbcU;
}

static inline bool
pss_verify(uint32_t sLen, uint32_t msgLen, uint8_t *msg, uint32_t emBits, uint8_t *em)
{
  uint32_t emLen = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t msBits = emBits % (uint32_t)8U;
  uint8_t em_0;
  if (msBits > (uint32_t)0U)
  {
    em_0 = em[0U] & (uint8_t)0xffU << msBits;
  }
  else
  {
    em_0 = (uint8_t)0U;
  }
  uint8_t em_last = em[emLen - (uint32_t)1U];
  if (emLen < sLen + (uint32_t)32U + (uint32_t)2U)
  {
    return false;
  }
  if (!(em_last == (uint8_t)0xbcU && em_0 == (uint8_t)0U))
  {
    return false;
  }
  uint32_t emLen1 = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t dbLen = emLen1 - (uint32_t)32U - (uint32_t)1U;
  uint8_t *maskedDB = em;
  uint8_t *m1Hash = em + dbLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), dbLen);
  uint8_t *dbMask = alloca(dbLen * sizeof (uint8_t));
  memset(dbMask, 0U, dbLen * sizeof (uint8_t));
  mgf_sha256((uint32_t)32U, m1Hash, dbLen, dbMask);
  xor_bytes(dbLen, dbMask, maskedDB);
  uint32_t msBits1 = emBits % (uint32_t)8U;
  if (msBits1 > (uint32_t)0U)
  {
    dbMask[0U] = dbMask[0U] & (uint8_t)0xffU >> ((uint32_t)8U - msBits1);
  }
  uint32_t padLen = emLen1 - sLen - (uint32_t)32U - (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint8_t), padLen);
  uint8_t *pad2 = alloca(padLen * sizeof (uint8_t));
  memset(pad2, 0U, padLen * sizeof (uint8_t));
  pad2[padLen - (uint32_t)1U] = (uint8_t)0x01U;
  uint8_t *pad = dbMask;
  uint8_t *salt = dbMask + padLen;
  uint8_t res = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < padLen; i++)
  {
    uint8_t uu____0 = FStar_UInt8_eq_mask(pad[i], pad2[i]);
    res = uu____0 & res;
  }
  uint8_t z = res;
  uint8_t m1Hash0[32U];
  if (!(z == (uint8_t)255U))
  {
    return false;
  }
  uint8_t init = (uint8_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
  {
    m1Hash0[i] = init;
  }
  uint32_t m1Len = (uint32_t)40U + sLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), m1Len);
  uint8_t *m1 = alloca(m1Len * sizeof (uint8_t));
  memset(m1, 0U, m1Len * sizeof (uint8_t));
  hash_sha256(m1 + (uint32_t)8U, msgLen, msg);
  memcpy(m1 + (uint32_t)40U, salt, sLen * sizeof (uint8_t));
  hash_sha256(m1Hash0, m1Len, m1);
  uint8_t res0 = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
  {
    uint8_t uu____1 = FStar_UInt8_eq_mask(m1Hash0[i], m1Hash[i]);
    res0 = uu____1 & res0;
  }
  uint8_t z0 = res0;
  return z0 == (uint8_t)255U;
}

static void
rsapss_sign(
  uint32_t modBits,
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
  uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen = (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint64_t *n = skey;
  uint64_t *d = skey + nLen + eLen;
  uint32_t k = (modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t emBits = modBits - (uint32_t)1U;
  uint32_t emLen = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint8_t), emLen);
  uint8_t *em = alloca(emLen * sizeof (uint8_t));
  memset(em, 0U, emLen * sizeof (uint8_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *m = alloca(nLen * sizeof (uint64_t));
  memset(m, 0U, nLen * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *s = alloca(nLen * sizeof (uint64_t));
  memset(s, 0U, nLen * sizeof (uint64_t));
  pss_encode(sLen, salt, msgLen, msg, emBits, em);
  bn_from_bytes_be(emLen, em, m);
  bn_mod_exp(modBits, nLen, n, m, dBits, d, s);
  bn_to_bytes_be(k, s, sgnt);
}

static bool
rsapss_verify(
  uint32_t modBits,
  uint32_t eBits,
  uint64_t *pkey,
  uint32_t sLen,
  uint8_t *sgnt,
  uint32_t msgLen,
  uint8_t *msg
)
{
  uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint64_t *n = pkey;
  uint64_t *e = pkey + nLen;
  uint32_t k = (modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t emBits = modBits - (uint32_t)1U;
  uint32_t emLen = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint8_t), emLen);
  uint8_t *em = alloca(emLen * sizeof (uint8_t));
  memset(em, 0U, emLen * sizeof (uint8_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *m = alloca(nLen * sizeof (uint64_t));
  memset(m, 0U, nLen * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *s = alloca(nLen * sizeof (uint64_t));
  memset(s, 0U, nLen * sizeof (uint64_t));
  bn_from_bytes_be(k, sgnt, s);
  if (Hacl_Bignum_bn_is_less(nLen, s, n))
  {
    bn_mod_exp(modBits, nLen, n, s, eBits, e, m);
    bool ite;
    if (!((modBits - (uint32_t)1U) % (uint32_t)8U == (uint32_t)0U))
    {
      ite = true;
    }
    else
    {
      ite =
        !Hacl_Bignum_bn_is_bit_set((modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U,
          m,
          modBits - (uint32_t)1U);
    }
    if (ite)
    {
      uint64_t *m1 = m;
      bn_to_bytes_be(emLen, m1, em);
      return pss_verify(sLen, msgLen, msg, emBits, em);
    }
    return false;
  }
  return false;
}

void
Hacl_RSAPSS_rsapss_sign(
  uint32_t modBits,
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
  rsapss_sign(modBits, eBits, dBits, skey, sLen, salt, msgLen, msg, sgnt);
}

bool
Hacl_RSAPSS_rsapss_verify(
  uint32_t modBits,
  uint32_t eBits,
  uint64_t *pkey,
  uint32_t sLen,
  uint8_t *sgnt,
  uint32_t msgLen,
  uint8_t *msg
)
{
  return rsapss_verify(modBits, eBits, pkey, sLen, sgnt, msgLen, msg);
}

