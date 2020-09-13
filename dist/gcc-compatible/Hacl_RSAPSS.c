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
  uint8_t tmp[tmpLen];
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
  uint8_t tmp[tmpLen];
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    store64_be(tmp + i * (uint32_t)8U, b[bnLen - i - (uint32_t)1U]);
  }
  memcpy(res, tmp + tmpLen - len, len * sizeof (uint8_t));
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
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len; i0++)
  {
    uint64_t qj = nInv_u64 * c[i0];
    uint64_t *res_ = c + i0;
    uint64_t c1 = (uint64_t)0U;
    uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      c1 =
        Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c1,
          n[(uint32_t)4U * i],
          qj,
          res_ + (uint32_t)4U * i);
      c1 =
        Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c1,
          n[(uint32_t)4U * i + (uint32_t)1U],
          qj,
          res_ + (uint32_t)4U * i + (uint32_t)1U);
      c1 =
        Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c1,
          n[(uint32_t)4U * i + (uint32_t)2U],
          qj,
          res_ + (uint32_t)4U * i + (uint32_t)2U);
      c1 =
        Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c1,
          n[(uint32_t)4U * i + (uint32_t)3U],
          qj,
          res_ + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < len; i++)
    {
      c1 = Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c1, n[i], qj, res_ + i);
    }
    uint64_t r = c1;
    uint64_t c10 = r;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c10, c[len + i0], c + len + i0);
  }
  memcpy(res, c + len, (len + len - len) * sizeof (uint64_t));
  uint64_t uu____0 = c0;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t tmp[len];
  memset(tmp, 0U, len * sizeof (uint64_t));
  uint64_t c1 = (uint64_t)0U;
  uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
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
  for (uint32_t i = k; i < len; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tmp + i);
  }
  uint64_t c10 = c1;
  uint64_t c2 = uu____0 - c10;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
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
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t c[len + len];
  memset(c, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t tmp[(uint32_t)4U * len];
  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_(len, a, r2, tmp, c);
  mont_reduction_runtime(len, n, nInv_u64, c, aM);
}

static void
from_runtime(uint32_t len, uint64_t *n, uint64_t nInv_u64, uint64_t *aM, uint64_t *a)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t tmp[len + len];
  memset(tmp, 0U, (len + len) * sizeof (uint64_t));
  memcpy(tmp, aM, len * sizeof (uint64_t));
  mont_reduction_runtime(len, n, nInv_u64, tmp, a);
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
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t c[len + len];
  memset(c, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t tmp[(uint32_t)4U * len];
  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_(len, aM, bM, tmp, c);
  mont_reduction_runtime(len, n, nInv_u64, c, resM);
}

static void
sqr_runtime(uint32_t len, uint64_t *n, uint64_t nInv_u64, uint64_t *aM, uint64_t *resM)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t c[len + len];
  memset(c, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t tmp[(uint32_t)4U * len];
  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_(len, aM, tmp, c);
  mont_reduction_runtime(len, n, nInv_u64, c, resM);
}

static inline uint32_t hash_len(Spec_Hash_Definitions_hash_alg a)
{
  switch (a)
  {
    case Spec_Hash_Definitions_MD5:
      {
        return (uint32_t)16U;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        return (uint32_t)20U;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        return (uint32_t)28U;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        return (uint32_t)32U;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        return (uint32_t)48U;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        return (uint32_t)64U;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        return (uint32_t)32U;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        return (uint32_t)64U;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static inline void
hash(Spec_Hash_Definitions_hash_alg a, uint8_t *mHash, uint32_t msgLen, uint8_t *msg)
{
  switch (a)
  {
    case Spec_Hash_Definitions_SHA2_256:
      {
        Hacl_Hash_SHA2_hash_256(msg, msgLen, mHash);
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        Hacl_Hash_SHA2_hash_384(msg, msgLen, mHash);
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        Hacl_Hash_SHA2_hash_512(msg, msgLen, mHash);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static inline void
mgf_hash(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t len,
  uint8_t *mgfseed,
  uint32_t maskLen,
  uint8_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), len + (uint32_t)4U);
  uint8_t mgfseed_counter[len + (uint32_t)4U];
  memset(mgfseed_counter, 0U, (len + (uint32_t)4U) * sizeof (uint8_t));
  memcpy(mgfseed_counter, mgfseed, len * sizeof (uint8_t));
  uint32_t hLen = hash_len(a);
  uint32_t n = (maskLen - (uint32_t)1U) / hLen + (uint32_t)1U;
  uint32_t accLen = n * hLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), accLen);
  uint8_t acc[accLen];
  memset(acc, 0U, accLen * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    uint8_t *uu____0 = acc + i * hLen;
    uint8_t *uu____1 = mgfseed_counter + len;
    uu____1[0U] = (uint8_t)(i >> (uint32_t)24U);
    uu____1[1U] = (uint8_t)(i >> (uint32_t)16U);
    uu____1[2U] = (uint8_t)(i >> (uint32_t)8U);
    uu____1[3U] = (uint8_t)i;
    hash(a, uu____0, len + (uint32_t)4U, mgfseed_counter);
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
    uint64_t get_bit = Hacl_Bignum_bn_get_ith_bit(bLen, b, i);
    if (get_bit == (uint64_t)1U)
    {
      mul_runtime(nLen, n, nInv_u64, aM, accM, accM);
    }
    sqr_runtime(nLen, n, nInv_u64, aM, aM);
  }
}

static inline void
bn_mod_exp_precompr2(
  uint32_t nLen,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *r2,
  uint64_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t acc[nLen];
  memset(acc, 0U, nLen * sizeof (uint64_t));
  memset(acc, 0U, nLen * sizeof (uint64_t));
  acc[0U] = (uint64_t)1U;
  uint32_t bLen = (bBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint64_t nInv_u64 = Hacl_Bignum_ModInv64_mod_inv_u64(n[0U]);
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t aM[nLen];
  memset(aM, 0U, nLen * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t accM[nLen];
  memset(accM, 0U, nLen * sizeof (uint64_t));
  to_runtime(nLen, n, nInv_u64, r2, a, aM);
  to_runtime(nLen, n, nInv_u64, r2, acc, accM);
  bn_mod_exp_loop_runtime(nLen, n, nInv_u64, bBits, bLen, b, aM, accM);
  from_runtime(nLen, n, nInv_u64, accM, res);
}

static void
bn_mod_exp_mont_ladder_loop_runtime(
  uint32_t nLen,
  uint64_t *n,
  uint64_t nInv_u64,
  uint32_t bBits,
  uint32_t bLen,
  uint64_t *b,
  uint64_t *rM0,
  uint64_t *rM1,
  uint64_t *sw
)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < bBits; i0++)
  {
    uint64_t bit = Hacl_Bignum_bn_get_ith_bit(bLen, b, bBits - i0 - (uint32_t)1U);
    uint64_t sw1 = bit ^ sw[0U];
    for (uint32_t i = (uint32_t)0U; i < nLen; i++)
    {
      uint64_t dummy = ((uint64_t)0U - sw1) & (rM0[i] ^ rM1[i]);
      rM0[i] = rM0[i] ^ dummy;
      rM1[i] = rM1[i] ^ dummy;
    }
    mul_runtime(nLen, n, nInv_u64, rM1, rM0, rM1);
    sqr_runtime(nLen, n, nInv_u64, rM0, rM0);
    sw[0U] = bit;
  }
}

static inline void
bn_mod_exp_mont_ladder_precompr2(
  uint32_t nLen,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *r2,
  uint64_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t one[nLen];
  memset(one, 0U, nLen * sizeof (uint64_t));
  memset(one, 0U, nLen * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  uint32_t bLen = (bBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint64_t nInv_u64 = Hacl_Bignum_ModInv64_mod_inv_u64(n[0U]);
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t rM0[nLen];
  memset(rM0, 0U, nLen * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t rM1[nLen];
  memset(rM1, 0U, nLen * sizeof (uint64_t));
  uint64_t sw = (uint64_t)0U;
  to_runtime(nLen, n, nInv_u64, r2, one, rM0);
  to_runtime(nLen, n, nInv_u64, r2, a, rM1);
  bn_mod_exp_mont_ladder_loop_runtime(nLen, n, nInv_u64, bBits, bLen, b, rM0, rM1, &sw);
  uint64_t uu____0 = sw;
  for (uint32_t i = (uint32_t)0U; i < nLen; i++)
  {
    uint64_t dummy = ((uint64_t)0U - uu____0) & (rM0[i] ^ rM1[i]);
    rM0[i] = rM0[i] ^ dummy;
    rM1[i] = rM1[i] ^ dummy;
  }
  from_runtime(nLen, n, nInv_u64, rM0, res);
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
  Spec_Hash_Definitions_hash_alg a,
  uint32_t sLen,
  uint8_t *salt,
  uint32_t msgLen,
  uint8_t *msg,
  uint32_t emBits,
  uint8_t *em
)
{
  uint32_t hLen = hash_len(a);
  KRML_CHECK_SIZE(sizeof (uint8_t), hLen);
  uint8_t m1Hash[hLen];
  memset(m1Hash, 0U, hLen * sizeof (uint8_t));
  uint32_t m1Len = (uint32_t)8U + hLen + sLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), m1Len);
  uint8_t m1[m1Len];
  memset(m1, 0U, m1Len * sizeof (uint8_t));
  hash(a, m1 + (uint32_t)8U, msgLen, msg);
  memcpy(m1 + (uint32_t)8U + hLen, salt, sLen * sizeof (uint8_t));
  hash(a, m1Hash, m1Len, m1);
  uint32_t emLen = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t dbLen = emLen - hLen - (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint8_t), dbLen);
  uint8_t db[dbLen];
  memset(db, 0U, dbLen * sizeof (uint8_t));
  uint32_t last_before_salt = dbLen - sLen - (uint32_t)1U;
  db[last_before_salt] = (uint8_t)1U;
  memcpy(db + last_before_salt + (uint32_t)1U, salt, sLen * sizeof (uint8_t));
  KRML_CHECK_SIZE(sizeof (uint8_t), dbLen);
  uint8_t dbMask[dbLen];
  memset(dbMask, 0U, dbLen * sizeof (uint8_t));
  mgf_hash(a, hLen, m1Hash, dbLen, dbMask);
  xor_bytes(dbLen, db, dbMask);
  uint32_t msBits = emBits % (uint32_t)8U;
  if (msBits > (uint32_t)0U)
  {
    db[0U] = db[0U] & (uint8_t)0xffU >> ((uint32_t)8U - msBits);
  }
  memcpy(em, db, dbLen * sizeof (uint8_t));
  memcpy(em + dbLen, m1Hash, hLen * sizeof (uint8_t));
  em[emLen - (uint32_t)1U] = (uint8_t)0xbcU;
}

static inline bool
pss_verify(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t sLen,
  uint32_t msgLen,
  uint8_t *msg,
  uint32_t emBits,
  uint8_t *em
)
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
  if (emLen < sLen + hash_len(a) + (uint32_t)2U)
  {
    return false;
  }
  if (!(em_last == (uint8_t)0xbcU && em_0 == (uint8_t)0U))
  {
    return false;
  }
  uint32_t emLen1 = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t hLen = hash_len(a);
  KRML_CHECK_SIZE(sizeof (uint8_t), hLen);
  uint8_t m1Hash0[hLen];
  memset(m1Hash0, 0U, hLen * sizeof (uint8_t));
  uint32_t dbLen = emLen1 - hLen - (uint32_t)1U;
  uint8_t *maskedDB = em;
  uint8_t *m1Hash = em + dbLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), dbLen);
  uint8_t dbMask[dbLen];
  memset(dbMask, 0U, dbLen * sizeof (uint8_t));
  mgf_hash(a, hLen, m1Hash, dbLen, dbMask);
  xor_bytes(dbLen, dbMask, maskedDB);
  uint32_t msBits1 = emBits % (uint32_t)8U;
  if (msBits1 > (uint32_t)0U)
  {
    dbMask[0U] = dbMask[0U] & (uint8_t)0xffU >> ((uint32_t)8U - msBits1);
  }
  uint32_t padLen = emLen1 - sLen - hLen - (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint8_t), padLen);
  uint8_t pad2[padLen];
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
  if (!(z == (uint8_t)255U))
  {
    return false;
  }
  uint32_t m1Len = (uint32_t)8U + hLen + sLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), m1Len);
  uint8_t m1[m1Len];
  memset(m1, 0U, m1Len * sizeof (uint8_t));
  hash(a, m1 + (uint32_t)8U, msgLen, msg);
  memcpy(m1 + (uint32_t)8U + hLen, salt, sLen * sizeof (uint8_t));
  hash(a, m1Hash0, m1Len, m1);
  uint8_t res0 = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < hLen; i++)
  {
    uint8_t uu____1 = FStar_UInt8_eq_mask(m1Hash0[i], m1Hash[i]);
    res0 = uu____1 & res0;
  }
  uint8_t z0 = res0;
  return z0 == (uint8_t)255U;
}

void
Hacl_RSAPSS_rsapss_sign(
  Spec_Hash_Definitions_hash_alg a,
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
  uint64_t *r2 = skey + nLen;
  uint64_t *d = skey + nLen + nLen + eLen;
  uint32_t k = (modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t emBits = modBits - (uint32_t)1U;
  uint32_t emLen = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint8_t), emLen);
  uint8_t em[emLen];
  memset(em, 0U, emLen * sizeof (uint8_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t m[nLen];
  memset(m, 0U, nLen * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t s[nLen];
  memset(s, 0U, nLen * sizeof (uint64_t));
  pss_encode(a, sLen, salt, msgLen, msg, emBits, em);
  bn_from_bytes_be(emLen, em, m);
  bn_mod_exp_mont_ladder_precompr2(nLen, n, m, dBits, d, r2, s);
  bn_to_bytes_be(k, s, sgnt);
}

bool
Hacl_RSAPSS_rsapss_verify(
  Spec_Hash_Definitions_hash_alg a,
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
  uint64_t *r2 = pkey + nLen;
  uint64_t *e = pkey + nLen + nLen;
  uint32_t k = (modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t emBits = modBits - (uint32_t)1U;
  uint32_t emLen = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint8_t), emLen);
  uint8_t em[emLen];
  memset(em, 0U, emLen * sizeof (uint8_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t m[nLen];
  memset(m, 0U, nLen * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t s[nLen];
  memset(s, 0U, nLen * sizeof (uint64_t));
  bn_from_bytes_be(k, sgnt, s);
  uint64_t mask = Hacl_Bignum_bn_lt_mask(nLen, s, n);
  if (mask == (uint64_t)0xFFFFFFFFFFFFFFFFU)
  {
    bn_mod_exp_precompr2(nLen, n, s, eBits, e, r2, m);
    bool ite;
    if (!((modBits - (uint32_t)1U) % (uint32_t)8U == (uint32_t)0U))
    {
      ite = true;
    }
    else
    {
      uint64_t
      get_bit =
        Hacl_Bignum_bn_get_ith_bit((modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U,
          m,
          modBits - (uint32_t)1U);
      ite = get_bit == (uint64_t)0U;
    }
    if (ite)
    {
      uint64_t *m1 = m;
      bn_to_bytes_be(emLen, m1, em);
      return pss_verify(a, sLen, msgLen, msg, emBits, em);
    }
    return false;
  }
  return false;
}

uint64_t
*Hacl_RSAPSS_new_rsapss_load_pkey(uint32_t modBits, uint32_t eBits, uint8_t *nb, uint8_t *eb)
{
  uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen = (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t pkeyLen = nLen + nLen + eLen;
  if
  (
    !((uint32_t)1U
    < modBits
    && (uint32_t)0U < eBits
    && nLen <= (uint32_t)33554431U
    && eLen <= (uint32_t)67108863U
    && nLen + nLen <= (uint32_t)0xffffffffU - eLen)
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
  uint32_t nbLen = (modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t ebLen = (eBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t nLen1 = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint64_t *n = pkey2;
  uint64_t *r2 = pkey2 + nLen1;
  uint64_t *e = pkey2 + nLen1 + nLen1;
  bn_from_bytes_be(nbLen, nb, n);
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen1);
  uint64_t bn_zero[nLen1];
  memset(bn_zero, 0U, nLen1 * sizeof (uint64_t));
  uint64_t mask = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  for (uint32_t i = (uint32_t)0U; i < nLen1; i++)
  {
    uint64_t uu____0 = FStar_UInt64_eq_mask(n[i], bn_zero[i]);
    mask = uu____0 & mask;
  }
  uint64_t mask10 = mask;
  uint64_t res = mask10;
  uint64_t mask0 = res;
  uint64_t priv0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < nLen1; i++)
  {
    uint64_t mask1 = FStar_UInt64_eq_mask(n[i], (uint64_t)0U);
    priv0 = (mask1 & priv0) | (~mask1 & (uint64_t)i);
  }
  uint64_t ind = priv0;
  uint64_t uu____1 = n[(uint32_t)ind];
  uint64_t priv = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t bit_i = uu____1 >> i & (uint64_t)1U;
    uint64_t mask1 = FStar_UInt64_eq_mask(bit_i, (uint64_t)1U);
    priv = (mask1 & (uint64_t)i) | (~mask1 & priv);
  }
  uint64_t bits = priv;
  uint64_t bits0 = (uint64_t)64U * ind + bits;
  uint64_t bits00 = ~mask0 & bits0;
  uint32_t b = (uint32_t)bits00;
  memset(r2, 0U, nLen1 * sizeof (uint64_t));
  Hacl_Bignum_bn_set_ith_bit(nLen1, r2, b);
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)128U * nLen1 - b; i0++)
  {
    uint64_t c0 = (uint64_t)0U;
    uint32_t k0 = nLen1 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
    {
      uint64_t t1 = r2[(uint32_t)4U * i];
      uint64_t t20 = r2[(uint32_t)4U * i];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, r2 + (uint32_t)4U * i);
      uint64_t t10 = r2[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = r2[(uint32_t)4U * i + (uint32_t)1U];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, r2 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = r2[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = r2[(uint32_t)4U * i + (uint32_t)2U];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, r2 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = r2[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = r2[(uint32_t)4U * i + (uint32_t)3U];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, r2 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k0; i < nLen1; i++)
    {
      uint64_t t1 = r2[i];
      uint64_t t2 = r2[i];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, r2 + i);
    }
    uint64_t c00 = c0;
    KRML_CHECK_SIZE(sizeof (uint64_t), nLen1);
    uint64_t tmp[nLen1];
    memset(tmp, 0U, nLen1 * sizeof (uint64_t));
    uint64_t c = (uint64_t)0U;
    uint32_t k = nLen1 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      uint64_t t1 = r2[(uint32_t)4U * i];
      uint64_t t20 = n[(uint32_t)4U * i];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, tmp + (uint32_t)4U * i);
      uint64_t t10 = r2[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, tmp + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = r2[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, tmp + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = r2[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, tmp + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < nLen1; i++)
    {
      uint64_t t1 = r2[i];
      uint64_t t2 = n[i];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, tmp + i);
    }
    uint64_t c1 = c;
    uint64_t c2 = c00 - c1;
    for (uint32_t i = (uint32_t)0U; i < nLen1; i++)
    {
      uint64_t *os = r2;
      uint64_t x = (c2 & r2[i]) | (~c2 & tmp[i]);
      os[i] = x;
    }
  }
  bn_from_bytes_be(ebLen, eb, e);
  return pkey2;
}

uint64_t
*Hacl_RSAPSS_new_rsapss_load_skey(
  uint32_t modBits,
  uint32_t eBits,
  uint32_t dBits,
  uint8_t *nb,
  uint8_t *eb,
  uint8_t *db
)
{
  uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen = (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t dLen = (dBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t skeyLen = nLen + nLen + eLen + dLen;
  if
  (
    !((uint32_t)1U
    < modBits
    && (uint32_t)0U < eBits
    && (uint32_t)0U < dBits
    && nLen <= (uint32_t)33554431U
    && eLen <= (uint32_t)67108863U
    && dLen <= (uint32_t)67108863U
    && nLen + nLen <= (uint32_t)0xffffffffU - eLen - dLen)
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
  uint32_t dbLen = (dBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t nLen1 = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen1 = (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t pkeyLen = nLen1 + nLen1 + eLen1;
  uint64_t *pkey = skey2;
  uint64_t *d = skey2 + pkeyLen;
  uint32_t nbLen1 = (modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t ebLen1 = (eBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t nLen2 = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint64_t *n = pkey;
  uint64_t *r2 = pkey + nLen2;
  uint64_t *e = pkey + nLen2 + nLen2;
  bn_from_bytes_be(nbLen1, nb, n);
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen2);
  uint64_t bn_zero[nLen2];
  memset(bn_zero, 0U, nLen2 * sizeof (uint64_t));
  uint64_t mask = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  for (uint32_t i = (uint32_t)0U; i < nLen2; i++)
  {
    uint64_t uu____0 = FStar_UInt64_eq_mask(n[i], bn_zero[i]);
    mask = uu____0 & mask;
  }
  uint64_t mask10 = mask;
  uint64_t res = mask10;
  uint64_t mask0 = res;
  uint64_t priv0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < nLen2; i++)
  {
    uint64_t mask1 = FStar_UInt64_eq_mask(n[i], (uint64_t)0U);
    priv0 = (mask1 & priv0) | (~mask1 & (uint64_t)i);
  }
  uint64_t ind = priv0;
  uint64_t uu____1 = n[(uint32_t)ind];
  uint64_t priv = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t bit_i = uu____1 >> i & (uint64_t)1U;
    uint64_t mask1 = FStar_UInt64_eq_mask(bit_i, (uint64_t)1U);
    priv = (mask1 & (uint64_t)i) | (~mask1 & priv);
  }
  uint64_t bits = priv;
  uint64_t bits0 = (uint64_t)64U * ind + bits;
  uint64_t bits00 = ~mask0 & bits0;
  uint32_t b = (uint32_t)bits00;
  memset(r2, 0U, nLen2 * sizeof (uint64_t));
  Hacl_Bignum_bn_set_ith_bit(nLen2, r2, b);
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)128U * nLen2 - b; i0++)
  {
    uint64_t c0 = (uint64_t)0U;
    uint32_t k0 = nLen2 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
    {
      uint64_t t1 = r2[(uint32_t)4U * i];
      uint64_t t20 = r2[(uint32_t)4U * i];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, r2 + (uint32_t)4U * i);
      uint64_t t10 = r2[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = r2[(uint32_t)4U * i + (uint32_t)1U];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, r2 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = r2[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = r2[(uint32_t)4U * i + (uint32_t)2U];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, r2 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = r2[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = r2[(uint32_t)4U * i + (uint32_t)3U];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, r2 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k0; i < nLen2; i++)
    {
      uint64_t t1 = r2[i];
      uint64_t t2 = r2[i];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, r2 + i);
    }
    uint64_t c00 = c0;
    KRML_CHECK_SIZE(sizeof (uint64_t), nLen2);
    uint64_t tmp[nLen2];
    memset(tmp, 0U, nLen2 * sizeof (uint64_t));
    uint64_t c = (uint64_t)0U;
    uint32_t k = nLen2 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      uint64_t t1 = r2[(uint32_t)4U * i];
      uint64_t t20 = n[(uint32_t)4U * i];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, tmp + (uint32_t)4U * i);
      uint64_t t10 = r2[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, tmp + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = r2[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, tmp + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = r2[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, tmp + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < nLen2; i++)
    {
      uint64_t t1 = r2[i];
      uint64_t t2 = n[i];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, tmp + i);
    }
    uint64_t c1 = c;
    uint64_t c2 = c00 - c1;
    for (uint32_t i = (uint32_t)0U; i < nLen2; i++)
    {
      uint64_t *os = r2;
      uint64_t x = (c2 & r2[i]) | (~c2 & tmp[i]);
      os[i] = x;
    }
  }
  bn_from_bytes_be(ebLen1, eb, e);
  bn_from_bytes_be(dbLen, db, d);
  return skey2;
}

