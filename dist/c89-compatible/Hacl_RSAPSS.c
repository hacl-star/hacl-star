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

inline uint32_t Hacl_Impl_RSAPSS_MGF_hash_len(Spec_Hash_Definitions_hash_alg a)
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
        KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
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
        KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
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
  {
    uint8_t mgfseed_counter[len + (uint32_t)4U];
    memset(mgfseed_counter, 0U, (len + (uint32_t)4U) * sizeof (uint8_t));
    {
      uint32_t hLen;
      uint32_t n;
      uint32_t accLen;
      memcpy(mgfseed_counter, mgfseed, len * sizeof (uint8_t));
      hLen = Hacl_Impl_RSAPSS_MGF_hash_len(a);
      n = (maskLen - (uint32_t)1U) / hLen + (uint32_t)1U;
      accLen = n * hLen;
      KRML_CHECK_SIZE(sizeof (uint8_t), accLen);
      {
        uint8_t acc[accLen];
        memset(acc, 0U, accLen * sizeof (uint8_t));
        {
          uint32_t i;
          for (i = (uint32_t)0U; i < n; i++)
          {
            uint8_t *uu____0 = acc + i * hLen;
            uint8_t *uu____1 = mgfseed_counter + len;
            uu____1[0U] = (uint8_t)(i >> (uint32_t)24U);
            uu____1[1U] = (uint8_t)(i >> (uint32_t)16U);
            uu____1[2U] = (uint8_t)(i >> (uint32_t)8U);
            uu____1[3U] = (uint8_t)i;
            hash(a, uu____0, len + (uint32_t)4U, mgfseed_counter);
          }
        }
        memcpy(res, acc, maskLen * sizeof (uint8_t));
      }
    }
  }
}

static inline uint64_t check_num_bits_u64(uint32_t bs, uint64_t *b)
{
  uint32_t bLen = (bs - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  if (bs == (uint32_t)64U * bLen)
  {
    return (uint64_t)0xFFFFFFFFFFFFFFFFU;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), bLen);
  {
    uint64_t b2[bLen];
    memset(b2, 0U, bLen * sizeof (uint64_t));
    {
      uint32_t i0 = bs / (uint32_t)64U;
      uint32_t j = bs % (uint32_t)64U;
      b2[i0] = b2[i0] | (uint64_t)1U << j;
      {
        uint64_t acc = (uint64_t)0U;
        {
          uint32_t i;
          for (i = (uint32_t)0U; i < bLen; i++)
          {
            uint64_t beq = FStar_UInt64_eq_mask(b[i], b2[i]);
            uint64_t blt = ~FStar_UInt64_gte_mask(b[i], b2[i]);
            acc =
              (beq & acc)
              | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
          }
        }
        {
          uint64_t res = acc;
          return res;
        }
      }
    }
  }
}

inline uint64_t Hacl_Impl_RSAPSS_Keys_check_modulus_u64(uint32_t modBits, uint64_t *n)
{
  uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint64_t bits0 = n[0U] & (uint64_t)1U;
  uint64_t m0 = (uint64_t)0U - bits0;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  {
    uint64_t b2[nLen];
    memset(b2, 0U, nLen * sizeof (uint64_t));
    {
      uint32_t i = (modBits - (uint32_t)1U) / (uint32_t)64U;
      uint32_t j = (modBits - (uint32_t)1U) % (uint32_t)64U;
      b2[i] = b2[i] | (uint64_t)1U << j;
      {
        uint64_t acc = (uint64_t)0U;
        uint64_t res;
        uint64_t m1;
        uint64_t m2;
        {
          uint32_t i0;
          for (i0 = (uint32_t)0U; i0 < nLen; i0++)
          {
            uint64_t beq = FStar_UInt64_eq_mask(b2[i0], n[i0]);
            uint64_t blt = ~FStar_UInt64_gte_mask(b2[i0], n[i0]);
            acc =
              (beq & acc)
              | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
          }
        }
        res = acc;
        m1 = res;
        m2 = check_num_bits_u64(modBits, n);
        return m0 & (m1 & m2);
      }
    }
  }
}

inline uint64_t Hacl_Impl_RSAPSS_Keys_check_exponent_u64(uint32_t eBits, uint64_t *e)
{
  uint32_t eLen = (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), eLen);
  {
    uint64_t bn_zero[eLen];
    memset(bn_zero, 0U, eLen * sizeof (uint64_t));
    {
      uint64_t mask = (uint64_t)0xFFFFFFFFFFFFFFFFU;
      uint64_t mask1;
      uint64_t res;
      uint64_t m0;
      uint64_t m1;
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < eLen; i++)
        {
          uint64_t uu____0 = FStar_UInt64_eq_mask(e[i], bn_zero[i]);
          mask = uu____0 & mask;
        }
      }
      mask1 = mask;
      res = mask1;
      m0 = res;
      m1 = check_num_bits_u64(eBits, e);
      return ~m0 & m1;
    }
  }
}

inline void
Hacl_Impl_RSAPSS_Padding_pss_encode(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t sLen,
  uint8_t *salt,
  uint32_t msgLen,
  uint8_t *msg,
  uint32_t emBits,
  uint8_t *em
)
{
  uint32_t hLen = Hacl_Impl_RSAPSS_MGF_hash_len(a);
  KRML_CHECK_SIZE(sizeof (uint8_t), hLen);
  {
    uint8_t m1Hash[hLen];
    memset(m1Hash, 0U, hLen * sizeof (uint8_t));
    {
      uint32_t m1Len = (uint32_t)8U + hLen + sLen;
      KRML_CHECK_SIZE(sizeof (uint8_t), m1Len);
      {
        uint8_t m1[m1Len];
        memset(m1, 0U, m1Len * sizeof (uint8_t));
        {
          uint32_t emLen;
          uint32_t dbLen;
          hash(a, m1 + (uint32_t)8U, msgLen, msg);
          memcpy(m1 + (uint32_t)8U + hLen, salt, sLen * sizeof (uint8_t));
          hash(a, m1Hash, m1Len, m1);
          emLen = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
          dbLen = emLen - hLen - (uint32_t)1U;
          KRML_CHECK_SIZE(sizeof (uint8_t), dbLen);
          {
            uint8_t db[dbLen];
            memset(db, 0U, dbLen * sizeof (uint8_t));
            {
              uint32_t last_before_salt = dbLen - sLen - (uint32_t)1U;
              db[last_before_salt] = (uint8_t)1U;
              memcpy(db + last_before_salt + (uint32_t)1U, salt, sLen * sizeof (uint8_t));
              KRML_CHECK_SIZE(sizeof (uint8_t), dbLen);
              {
                uint8_t dbMask[dbLen];
                memset(dbMask, 0U, dbLen * sizeof (uint8_t));
                {
                  uint32_t msBits;
                  mgf_hash(a, hLen, m1Hash, dbLen, dbMask);
                  {
                    uint32_t i;
                    for (i = (uint32_t)0U; i < dbLen; i++)
                    {
                      uint8_t *os = db;
                      uint8_t x = db[i] ^ dbMask[i];
                      os[i] = x;
                    }
                  }
                  msBits = emBits % (uint32_t)8U;
                  if (msBits > (uint32_t)0U)
                  {
                    db[0U] = db[0U] & (uint8_t)0xffU >> ((uint32_t)8U - msBits);
                  }
                  memcpy(em, db, dbLen * sizeof (uint8_t));
                  memcpy(em + dbLen, m1Hash, hLen * sizeof (uint8_t));
                  em[emLen - (uint32_t)1U] = (uint8_t)0xbcU;
                }
              }
            }
          }
        }
      }
    }
  }
}

inline bool
Hacl_Impl_RSAPSS_Padding_pss_verify(
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
  {
    uint8_t em_last = em[emLen - (uint32_t)1U];
    if (emLen < sLen + Hacl_Impl_RSAPSS_MGF_hash_len(a) + (uint32_t)2U)
    {
      return false;
    }
    if (!(em_last == (uint8_t)0xbcU && em_0 == (uint8_t)0U))
    {
      return false;
    }
    {
      uint32_t emLen1 = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
      uint32_t hLen = Hacl_Impl_RSAPSS_MGF_hash_len(a);
      KRML_CHECK_SIZE(sizeof (uint8_t), hLen);
      {
        uint8_t m1Hash0[hLen];
        memset(m1Hash0, 0U, hLen * sizeof (uint8_t));
        {
          uint32_t dbLen = emLen1 - hLen - (uint32_t)1U;
          uint8_t *maskedDB = em;
          uint8_t *m1Hash = em + dbLen;
          KRML_CHECK_SIZE(sizeof (uint8_t), dbLen);
          {
            uint8_t dbMask[dbLen];
            memset(dbMask, 0U, dbLen * sizeof (uint8_t));
            mgf_hash(a, hLen, m1Hash, dbLen, dbMask);
            {
              uint32_t i;
              for (i = (uint32_t)0U; i < dbLen; i++)
              {
                uint8_t *os = dbMask;
                uint8_t x = dbMask[i] ^ maskedDB[i];
                os[i] = x;
              }
            }
            {
              uint32_t msBits1 = emBits % (uint32_t)8U;
              if (msBits1 > (uint32_t)0U)
              {
                dbMask[0U] = dbMask[0U] & (uint8_t)0xffU >> ((uint32_t)8U - msBits1);
              }
              {
                uint32_t padLen = emLen1 - sLen - hLen - (uint32_t)1U;
                KRML_CHECK_SIZE(sizeof (uint8_t), padLen);
                {
                  uint8_t pad2[padLen];
                  memset(pad2, 0U, padLen * sizeof (uint8_t));
                  pad2[padLen - (uint32_t)1U] = (uint8_t)0x01U;
                  {
                    uint8_t *pad = dbMask;
                    uint8_t *salt = dbMask + padLen;
                    uint8_t res = (uint8_t)255U;
                    {
                      uint32_t i;
                      for (i = (uint32_t)0U; i < padLen; i++)
                      {
                        uint8_t uu____0 = FStar_UInt8_eq_mask(pad[i], pad2[i]);
                        res = uu____0 & res;
                      }
                    }
                    {
                      uint8_t z = res;
                      if (!(z == (uint8_t)255U))
                      {
                        return false;
                      }
                      {
                        uint32_t m1Len = (uint32_t)8U + hLen + sLen;
                        KRML_CHECK_SIZE(sizeof (uint8_t), m1Len);
                        {
                          uint8_t m1[m1Len];
                          memset(m1, 0U, m1Len * sizeof (uint8_t));
                          hash(a, m1 + (uint32_t)8U, msgLen, msg);
                          memcpy(m1 + (uint32_t)8U + hLen, salt, sLen * sizeof (uint8_t));
                          hash(a, m1Hash0, m1Len, m1);
                          {
                            uint8_t res0 = (uint8_t)255U;
                            {
                              uint32_t i;
                              for (i = (uint32_t)0U; i < hLen; i++)
                              {
                                uint8_t uu____1 = FStar_UInt8_eq_mask(m1Hash0[i], m1Hash[i]);
                                res0 = uu____1 & res0;
                              }
                            }
                            {
                              uint8_t z0 = res0;
                              return z0 == (uint8_t)255U;
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
        }
      }
    }
  }
}

static inline bool
load_pkey(uint32_t modBits, uint32_t eBits, uint8_t *nb, uint8_t *eb, uint64_t *pkey)
{
  uint32_t nbLen = (modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t ebLen = (eBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint64_t *n = pkey;
  uint64_t *r2 = pkey + nLen;
  uint64_t *e = pkey + nLen + nLen;
  uint64_t m0;
  uint64_t m1;
  uint64_t m;
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(nbLen, nb, n);
  Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64((modBits - (uint32_t)1U)
    / (uint32_t)64U
    + (uint32_t)1U,
    modBits - (uint32_t)1U,
    n,
    r2);
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(ebLen, eb, e);
  m0 = Hacl_Impl_RSAPSS_Keys_check_modulus_u64(modBits, n);
  m1 = Hacl_Impl_RSAPSS_Keys_check_exponent_u64(eBits, e);
  m = m0 & m1;
  return m == (uint64_t)0xFFFFFFFFFFFFFFFFU;
}

static inline bool
load_skey(
  uint32_t modBits,
  uint32_t eBits,
  uint32_t dBits,
  uint8_t *nb,
  uint8_t *eb,
  uint8_t *db,
  uint64_t *skey
)
{
  uint32_t dbLen = (dBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen = (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t pkeyLen = nLen + nLen + eLen;
  uint64_t *pkey = skey;
  uint64_t *d = skey + pkeyLen;
  bool b = load_pkey(modBits, eBits, nb, eb, pkey);
  uint64_t m1;
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(dbLen, db, d);
  m1 = Hacl_Impl_RSAPSS_Keys_check_exponent_u64(dBits, d);
  return b && m1 == (uint64_t)0xFFFFFFFFFFFFFFFFU;
}

bool
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
  uint32_t hLen = Hacl_Impl_RSAPSS_MGF_hash_len(a);
  bool
  b =
    sLen
    <= (uint32_t)0xffffffffU - hLen - (uint32_t)8U
    &&
      sLen
      + hLen
      + (uint32_t)2U
      <= (modBits - (uint32_t)1U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  if (b)
  {
    uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
    KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
    {
      uint64_t m[nLen];
      memset(m, 0U, nLen * sizeof (uint64_t));
      {
        uint32_t emBits = modBits - (uint32_t)1U;
        uint32_t emLen = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
        KRML_CHECK_SIZE(sizeof (uint8_t), emLen);
        {
          uint8_t em[emLen];
          memset(em, 0U, emLen * sizeof (uint8_t));
          Hacl_Impl_RSAPSS_Padding_pss_encode(a, sLen, salt, msgLen, msg, emBits, em);
          Hacl_Bignum_Convert_bn_from_bytes_be_uint64(emLen, em, m);
          {
            uint32_t nLen1 = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
            uint32_t k = (modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
            KRML_CHECK_SIZE(sizeof (uint64_t), nLen1);
            {
              uint64_t s[nLen1];
              memset(s, 0U, nLen1 * sizeof (uint64_t));
              KRML_CHECK_SIZE(sizeof (uint64_t), nLen1);
              {
                uint64_t m_[nLen1];
                memset(m_, 0U, nLen1 * sizeof (uint64_t));
                {
                  uint32_t nLen2 = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
                  uint32_t eLen = (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
                  uint64_t *n = skey;
                  uint64_t *r2 = skey + nLen2;
                  uint64_t *e = skey + nLen2 + nLen2;
                  uint64_t *d = skey + nLen2 + nLen2 + eLen;
                  Hacl_Bignum_Exponentiation_bn_mod_exp_fw_ct_precompr2_u64((modBits - (uint32_t)1U)
                    / (uint32_t)64U
                    + (uint32_t)1U,
                    n,
                    m,
                    dBits,
                    d,
                    (uint32_t)4U,
                    r2,
                    s);
                  Hacl_Bignum_Exponentiation_bn_mod_exp_raw_precompr2_u64((modBits - (uint32_t)1U)
                    / (uint32_t)64U
                    + (uint32_t)1U,
                    n,
                    s,
                    eBits,
                    e,
                    r2,
                    m_);
                  {
                    uint64_t mask = (uint64_t)0xFFFFFFFFFFFFFFFFU;
                    {
                      uint32_t i;
                      for (i = (uint32_t)0U; i < nLen2; i++)
                      {
                        uint64_t uu____0 = FStar_UInt64_eq_mask(m[i], m_[i]);
                        mask = uu____0 & mask;
                      }
                    }
                    {
                      uint64_t mask1 = mask;
                      uint64_t eq_m = mask1;
                      {
                        uint32_t i;
                        for (i = (uint32_t)0U; i < nLen2; i++)
                        {
                          uint64_t *os = s;
                          uint64_t x = s[i];
                          uint64_t x0 = eq_m & x;
                          os[i] = x0;
                        }
                      }
                      {
                        bool eq_b = eq_m == (uint64_t)0xFFFFFFFFFFFFFFFFU;
                        Hacl_Bignum_Convert_bn_to_bytes_be_uint64(k, s, sgnt);
                        {
                          bool eq_b0 = eq_b;
                          return eq_b0;
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
    }
  }
  return false;
}

bool
Hacl_RSAPSS_rsapss_verify(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t modBits,
  uint32_t eBits,
  uint64_t *pkey,
  uint32_t sLen,
  uint32_t k,
  uint8_t *sgnt,
  uint32_t msgLen,
  uint8_t *msg
)
{
  uint32_t hLen = Hacl_Impl_RSAPSS_MGF_hash_len(a);
  bool
  b =
    sLen
    <= (uint32_t)0xffffffffU - hLen - (uint32_t)8U
    && k == (modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  if (b)
  {
    uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
    KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
    {
      uint64_t m[nLen];
      memset(m, 0U, nLen * sizeof (uint64_t));
      {
        uint32_t nLen1 = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
        uint32_t k1 = (modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
        KRML_CHECK_SIZE(sizeof (uint64_t), nLen1);
        {
          uint64_t s[nLen1];
          memset(s, 0U, nLen1 * sizeof (uint64_t));
          Hacl_Bignum_Convert_bn_from_bytes_be_uint64(k1, sgnt, s);
          {
            uint32_t nLen2 = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
            uint64_t *n = pkey;
            uint64_t *r2 = pkey + nLen2;
            uint64_t *e = pkey + nLen2 + nLen2;
            uint64_t acc = (uint64_t)0U;
            {
              uint32_t i;
              for (i = (uint32_t)0U; i < nLen2; i++)
              {
                uint64_t beq = FStar_UInt64_eq_mask(s[i], n[i]);
                uint64_t blt = ~FStar_UInt64_gte_mask(s[i], n[i]);
                acc =
                  (beq & acc)
                  | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
              }
            }
            {
              uint64_t mask = acc;
              bool res;
              if (mask == (uint64_t)0xFFFFFFFFFFFFFFFFU)
              {
                Hacl_Bignum_Exponentiation_bn_mod_exp_raw_precompr2_u64((modBits - (uint32_t)1U)
                  / (uint32_t)64U
                  + (uint32_t)1U,
                  n,
                  s,
                  eBits,
                  e,
                  r2,
                  m);
                {
                  bool ite;
                  if (!((modBits - (uint32_t)1U) % (uint32_t)8U == (uint32_t)0U))
                  {
                    ite = true;
                  }
                  else
                  {
                    uint32_t i = (modBits - (uint32_t)1U) / (uint32_t)64U;
                    uint32_t j = (modBits - (uint32_t)1U) % (uint32_t)64U;
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
              }
              else
              {
                res = false;
              }
              {
                bool b1 = res;
                bool b10 = b1;
                if (b10)
                {
                  uint32_t emBits = modBits - (uint32_t)1U;
                  uint32_t emLen = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
                  KRML_CHECK_SIZE(sizeof (uint8_t), emLen);
                  {
                    uint8_t em[emLen];
                    memset(em, 0U, emLen * sizeof (uint8_t));
                    {
                      uint64_t *m1 = m;
                      Hacl_Bignum_Convert_bn_to_bytes_be_uint64(emLen, m1, em);
                      {
                        bool
                        res0 = Hacl_Impl_RSAPSS_Padding_pss_verify(a, sLen, msgLen, msg, emBits, em);
                        return res0;
                      }
                    }
                  }
                }
                return false;
              }
            }
          }
        }
      }
    }
  }
  return false;
}

uint64_t
*Hacl_RSAPSS_new_rsapss_load_pkey(uint32_t modBits, uint32_t eBits, uint8_t *nb, uint8_t *eb)
{
  uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen = (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t pkeyLen = nLen + nLen + eLen;
  uint32_t nLen1 = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen1 = (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  if
  (
    !((uint32_t)1U
    < modBits
    && (uint32_t)0U < eBits
    && nLen1 <= (uint32_t)33554431U
    && eLen1 <= (uint32_t)67108863U
    && nLen1 + nLen1 <= (uint32_t)0xffffffffU - eLen1)
  )
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), pkeyLen);
  {
    uint64_t *pkey = KRML_HOST_CALLOC(pkeyLen, sizeof (uint64_t));
    if (pkey == NULL)
    {
      return pkey;
    }
    {
      uint64_t *pkey1 = pkey;
      uint64_t *pkey2 = pkey1;
      bool b = load_pkey(modBits, eBits, nb, eb, pkey2);
      if (b)
      {
        return pkey2;
      }
      return NULL;
    }
  }
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
  uint32_t nLen1 = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen1 = (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t dLen1 = (dBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t nLen2 = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen2 = (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  if
  (
    !((uint32_t)1U
    < modBits
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
  {
    uint64_t *skey = KRML_HOST_CALLOC(skeyLen, sizeof (uint64_t));
    if (skey == NULL)
    {
      return skey;
    }
    {
      uint64_t *skey1 = skey;
      uint64_t *skey2 = skey1;
      bool b = load_skey(modBits, eBits, dBits, nb, eb, db, skey2);
      if (b)
      {
        return skey2;
      }
      return NULL;
    }
  }
}

bool
Hacl_RSAPSS_rsapss_skey_sign(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t modBits,
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
    * ((modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U)
    + (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U
    + (dBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U);
  {
    uint64_t
    skey[(uint32_t)2U
    * ((modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U)
    + (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U
    + (dBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U];
    memset(skey,
      0U,
      ((uint32_t)2U
      * ((modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U)
      + (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U
      + (dBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U)
      * sizeof (uint64_t));
    {
      bool b = load_skey(modBits, eBits, dBits, nb, eb, db, skey);
      if (b)
      {
        return
          Hacl_RSAPSS_rsapss_sign(a,
            modBits,
            eBits,
            dBits,
            skey,
            sLen,
            salt,
            msgLen,
            msg,
            sgnt);
      }
      return false;
    }
  }
}

bool
Hacl_RSAPSS_rsapss_pkey_verify(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t modBits,
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
    * ((modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U)
    + (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U);
  {
    uint64_t
    pkey[(uint32_t)2U
    * ((modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U)
    + (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U];
    memset(pkey,
      0U,
      ((uint32_t)2U
      * ((modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U)
      + (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U)
      * sizeof (uint64_t));
    {
      bool b = load_pkey(modBits, eBits, nb, eb, pkey);
      if (b)
      {
        return Hacl_RSAPSS_rsapss_verify(a, modBits, eBits, pkey, sLen, k, sgnt, msgLen, msg);
      }
      return false;
    }
  }
}

