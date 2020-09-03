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

static inline void bn_from_bytes_be(u32 len, u8 *b, u64 *res)
{
  u32 bnLen = (len - (u32)1U) / (u32)8U + (u32)1U;
  u32 tmpLen = (u32)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (u8), tmpLen);
  {
    u8 tmp[tmpLen];
    memset(tmp, 0U, tmpLen * sizeof (u8));
    memcpy(tmp + tmpLen - len, b, len * sizeof (u8));
    {
      u32 i;
      for (i = (u32)0U; i < bnLen; i++)
      {
        u64 *os = res;
        u64 u = load64_be(tmp + (bnLen - i - (u32)1U) * (u32)8U);
        u64 x = u;
        os[i] = x;
      }
    }
  }
}

static inline void bn_to_bytes_be(u32 len, u64 *b, u8 *res)
{
  u32 bnLen = (len - (u32)1U) / (u32)8U + (u32)1U;
  u32 tmpLen = (u32)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (u8), tmpLen);
  {
    u8 tmp[tmpLen];
    memset(tmp, 0U, tmpLen * sizeof (u8));
    {
      u32 i;
      for (i = (u32)0U; i < bnLen; i++)
        store64_be(tmp + i * (u32)8U, b[bnLen - i - (u32)1U]);
    }
    memcpy(res, tmp + tmpLen - len, len * sizeof (u8));
  }
}

static void precomp_runtime(u32 len, u32 modBits, u64 *n, u64 *res)
{
  u32 i0;
  memset(res, 0U, len * sizeof (u64));
  Hacl_Bignum_bn_bit_set(len, res, modBits - (u32)1U);
  for (i0 = (u32)0U; i0 < (u32)128U * len + (u32)129U - modBits; i0++)
  {
    KRML_CHECK_SIZE(sizeof (u64), len);
    {
      u64 tmp[len];
      memset(tmp, 0U, len * sizeof (u64));
      {
        u64 c2 = (u64)0U;
        u64 c0;
        {
          u32 i;
          for (i = (u32)0U; i < len; i++)
          {
            u64 t1 = res[i];
            u64 t2 = res[i];
            c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t1, t2, res + i);
          }
        }
        c0 = c2;
        {
          u64 c3 = (u64)0U;
          u64 c1;
          u64 c;
          {
            u32 i;
            for (i = (u32)0U; i < len; i++)
            {
              u64 t1 = res[i];
              u64 t2 = n[i];
              c3 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c3, t1, t2, tmp + i);
            }
          }
          c1 = c3;
          c = c0 - c1;
          {
            u32 i;
            for (i = (u32)0U; i < len; i++)
            {
              u64 *os = res;
              u64 x = (c & res[i]) | (~c & tmp[i]);
              os[i] = x;
            }
          }
        }
      }
    }
  }
}

static void mont_reduction_runtime(u32 len, u64 *n, u64 nInv_u64, u64 *c, u64 *res)
{
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < len + (u32)1U; i0++)
    {
      u64 qj = nInv_u64 * c[i0];
      u64 *res_ = c + i0;
      u64 c1 = (u64)0U;
      {
        u32 i;
        for (i = (u32)0U; i < len; i++)
          c1 = Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c1, n[i], qj, res_ + i);
      }
      {
        u64 r0 = c1;
        u64 c10 = r0;
        u64 c2 = c10;
        u64 *res2 = c + i0 + len;
        u64 *a0 = res2;
        u64 *res0 = res2;
        u64 c30 = (u64)0U;
        {
          u32 i;
          for (i = (u32)0U; i < (u32)1U; i++)
          {
            u64 t1 = a0[i];
            u64 t2 = (&c2)[i];
            c30 = Lib_IntTypes_Intrinsics_add_carry_u64(c30, t1, t2, res0 + i);
          }
        }
        {
          u64 c0 = c30;
          u64 r;
          if ((u32)1U < len + (u32)1U + len + (u32)1U - i0 - len)
          {
            u32 rLen = len + (u32)1U + len + (u32)1U - i0 - len - (u32)1U;
            u64 *a1 = res2 + (u32)1U;
            u64 *res1 = res2 + (u32)1U;
            u64 c3 = c0;
            {
              u32 i;
              for (i = (u32)0U; i < rLen; i++)
              {
                u64 t1 = a1[i];
                c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c3, t1, (u64)0U, res1 + i);
              }
            }
            {
              u64 c11 = c3;
              r = c11;
            }
          }
          else
            r = c0;
          {
            u64 uu____0 = r;
          }
        }
      }
    }
  }
  memcpy(res,
    c + len + (u32)1U,
    (len + (u32)1U + len + (u32)1U - (len + (u32)1U)) * sizeof (u64));
}

static void to_runtime(u32 len, u64 *n, u64 nInv_u64, u64 *r2, u64 *a, u64 *aM)
{
  KRML_CHECK_SIZE(sizeof (u64), len + (u32)1U + len + (u32)1U);
  {
    u64 tmp[len + (u32)1U + len + (u32)1U];
    memset(tmp, 0U, (len + (u32)1U + len + (u32)1U) * sizeof (u64));
    {
      u64 *c = tmp;
      u32 resLen = len + len;
      memset(c, 0U, resLen * sizeof (u64));
      {
        u32 i0;
        for (i0 = (u32)0U; i0 < len; i0++)
        {
          u64 uu____0 = r2[i0];
          u64 *res_ = c + i0;
          u64 c1 = (u64)0U;
          {
            u32 i;
            for (i = (u32)0U; i < len; i++)
              c1 = Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c1, a[i], uu____0, res_ + i);
          }
          {
            u64 r = c1;
            c[len + i0] = r;
          }
        }
      }
      mont_reduction_runtime(len, n, nInv_u64, tmp, aM);
    }
  }
}

static void from_runtime(u32 len, u64 *n, u64 nInv_u64, u64 *aM, u64 *a)
{
  KRML_CHECK_SIZE(sizeof (u64), len + (u32)1U + len + (u32)1U);
  {
    u64 tmp[len + (u32)1U + len + (u32)1U];
    memset(tmp, 0U, (len + (u32)1U + len + (u32)1U) * sizeof (u64));
    memcpy(tmp, aM, (len + (u32)1U) * sizeof (u64));
    KRML_CHECK_SIZE(sizeof (u64), len + (u32)1U);
    {
      u64 a_[len + (u32)1U];
      memset(a_, 0U, (len + (u32)1U) * sizeof (u64));
      mont_reduction_runtime(len, n, nInv_u64, tmp, a_);
      memcpy(a, a_, len * sizeof (u64));
    }
  }
}

static void mul_runtime(u32 len, u64 *n, u64 nInv_u64, u64 *aM, u64 *bM, u64 *resM)
{
  KRML_CHECK_SIZE(sizeof (u64), len + (u32)1U + len + (u32)1U);
  {
    u64 c[len + (u32)1U + len + (u32)1U];
    memset(c, 0U, (len + (u32)1U + len + (u32)1U) * sizeof (u64));
    {
      u32 resLen = len + (u32)1U + len + (u32)1U;
      memset(c, 0U, resLen * sizeof (u64));
      {
        u32 i0;
        for (i0 = (u32)0U; i0 < len + (u32)1U; i0++)
        {
          u64 uu____0 = bM[i0];
          u64 *res_ = c + i0;
          u64 c1 = (u64)0U;
          {
            u32 i;
            for (i = (u32)0U; i < len + (u32)1U; i++)
              c1 = Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c1, aM[i], uu____0, res_ + i);
          }
          {
            u64 r = c1;
            c[len + (u32)1U + i0] = r;
          }
        }
      }
      mont_reduction_runtime(len, n, nInv_u64, c, resM);
    }
  }
}

static void hash_sha256(u8 *mHash, u32 msgLen, u8 *msg)
{
  Hacl_Hash_SHA2_hash_256(msg, msgLen, mHash);
}

static inline void mgf_sha256(u32 len, u8 *mgfseed, u32 maskLen, u8 *res)
{
  KRML_CHECK_SIZE(sizeof (u8), len + (u32)4U);
  {
    u8 mgfseed_counter[len + (u32)4U];
    memset(mgfseed_counter, 0U, (len + (u32)4U) * sizeof (u8));
    {
      u32 n;
      u32 accLen;
      memcpy(mgfseed_counter, mgfseed, len * sizeof (u8));
      n = (maskLen - (u32)1U) / (u32)32U + (u32)1U;
      accLen = n * (u32)32U;
      KRML_CHECK_SIZE(sizeof (u8), accLen);
      {
        u8 acc[accLen];
        memset(acc, 0U, accLen * sizeof (u8));
        {
          u32 i;
          for (i = (u32)0U; i < n; i++)
          {
            u8 *uu____0 = acc + i * (u32)32U;
            u8 *uu____1 = mgfseed_counter + len;
            uu____1[0U] = (u8)(i >> (u32)24U);
            uu____1[1U] = (u8)(i >> (u32)16U);
            uu____1[2U] = (u8)(i >> (u32)8U);
            uu____1[3U] = (u8)i;
            hash_sha256(uu____0, len + (u32)4U, mgfseed_counter);
          }
        }
        memcpy(res, acc, maskLen * sizeof (u8));
      }
    }
  }
}

static void
bn_mod_exp_loop_runtime(
  u32 nLen,
  u64 *n,
  u64 nInv_u64,
  u32 bBits,
  u32 bLen,
  u64 *b,
  u64 *aM,
  u64 *accM
)
{
  u32 i;
  for (i = (u32)0U; i < bBits; i++)
  {
    if (Hacl_Bignum_bn_is_bit_set(bLen, b, i))
      mul_runtime(nLen, n, nInv_u64, aM, accM, accM);
    mul_runtime(nLen, n, nInv_u64, aM, aM, aM);
  }
}

static inline void
bn_mod_exp(u32 modBits, u32 nLen, u64 *n, u64 *a, u32 bBits, u64 *b, u64 *res)
{
  KRML_CHECK_SIZE(sizeof (u64), nLen);
  {
    u64 acc[nLen];
    memset(acc, 0U, nLen * sizeof (u64));
    memset(acc, 0U, nLen * sizeof (u64));
    acc[0U] = (u64)1U;
    {
      u32 rLen = nLen + (u32)1U;
      u32 bLen = (bBits - (u32)1U) / (u32)64U + (u32)1U;
      u64 nInv_u64 = Hacl_Bignum_ModInv64_mod_inv_u64(n[0U]);
      KRML_CHECK_SIZE(sizeof (u64), nLen);
      {
        u64 r2[nLen];
        memset(r2, 0U, nLen * sizeof (u64));
        precomp_runtime(nLen, modBits, n, r2);
        KRML_CHECK_SIZE(sizeof (u64), rLen);
        {
          u64 aM[rLen];
          memset(aM, 0U, rLen * sizeof (u64));
          KRML_CHECK_SIZE(sizeof (u64), rLen);
          {
            u64 accM[rLen];
            memset(accM, 0U, rLen * sizeof (u64));
            to_runtime(nLen, n, nInv_u64, r2, a, aM);
            to_runtime(nLen, n, nInv_u64, r2, acc, accM);
            bn_mod_exp_loop_runtime(nLen, n, nInv_u64, bBits, bLen, b, aM, accM);
            from_runtime(nLen, n, nInv_u64, accM, res);
            {
              u64 mask = (u64)0xFFFFFFFFFFFFFFFFU;
              KRML_CHECK_SIZE(sizeof (u64), nLen);
              {
                u64 mod_mask[nLen];
                memset(mod_mask, 0U, nLen * sizeof (u64));
                {
                  u64 mask1;
                  {
                    u32 i;
                    for (i = (u32)0U; i < nLen; i++)
                    {
                      u64 uu____0 = FStar_UInt64_eq_mask(n[i], res[i]);
                      mask = uu____0 & mask;
                    }
                  }
                  mask1 = mask;
                  {
                    u32 i;
                    for (i = (u32)0U; i < nLen; i++)
                    {
                      u64 *os = mod_mask;
                      u64 x = n[i];
                      u64 x0 = mask1 & x;
                      os[i] = x0;
                    }
                  }
                  {
                    u64 c = (u64)0U;
                    u64 uu____1;
                    {
                      u32 i;
                      for (i = (u32)0U; i < nLen; i++)
                      {
                        u64 t1 = res[i];
                        u64 t2 = mod_mask[i];
                        c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res + i);
                      }
                    }
                    uu____1 = c;
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

static inline void xor_bytes(u32 len, u8 *b1, u8 *b2)
{
  u32 i;
  for (i = (u32)0U; i < len; i++)
  {
    u8 *os = b1;
    u8 x = b1[i] ^ b2[i];
    os[i] = x;
  }
}

static inline void pss_encode(u32 sLen, u8 *salt, u32 msgLen, u8 *msg, u32 emBits, u8 *em)
{
  u8 m1Hash[32U] = { 0U };
  u32 m1Len = (u32)40U + sLen;
  KRML_CHECK_SIZE(sizeof (u8), m1Len);
  {
    u8 m1[m1Len];
    memset(m1, 0U, m1Len * sizeof (u8));
    {
      u32 emLen;
      u32 dbLen;
      hash_sha256(m1 + (u32)8U, msgLen, msg);
      memcpy(m1 + (u32)40U, salt, sLen * sizeof (u8));
      hash_sha256(m1Hash, m1Len, m1);
      emLen = (emBits - (u32)1U) / (u32)8U + (u32)1U;
      dbLen = emLen - (u32)32U - (u32)1U;
      KRML_CHECK_SIZE(sizeof (u8), dbLen);
      {
        u8 db[dbLen];
        memset(db, 0U, dbLen * sizeof (u8));
        {
          u32 last_before_salt = dbLen - sLen - (u32)1U;
          db[last_before_salt] = (u8)1U;
          memcpy(db + last_before_salt + (u32)1U, salt, sLen * sizeof (u8));
          KRML_CHECK_SIZE(sizeof (u8), dbLen);
          {
            u8 dbMask[dbLen];
            memset(dbMask, 0U, dbLen * sizeof (u8));
            {
              u32 msBits;
              mgf_sha256((u32)32U, m1Hash, dbLen, dbMask);
              xor_bytes(dbLen, db, dbMask);
              msBits = emBits % (u32)8U;
              if (msBits > (u32)0U)
                db[0U] = db[0U] & (u8)0xffU >> ((u32)8U - msBits);
              memcpy(em, db, dbLen * sizeof (u8));
              memcpy(em + dbLen, m1Hash, (u32)32U * sizeof (u8));
              em[emLen - (u32)1U] = (u8)0xbcU;
            }
          }
        }
      }
    }
  }
}

static inline bool pss_verify(u32 sLen, u32 msgLen, u8 *msg, u32 emBits, u8 *em)
{
  u32 emLen = (emBits - (u32)1U) / (u32)8U + (u32)1U;
  u32 msBits = emBits % (u32)8U;
  u8 em_0;
  if (msBits > (u32)0U)
    em_0 = em[0U] & (u8)0xffU << msBits;
  else
    em_0 = (u8)0U;
  {
    u8 em_last = em[emLen - (u32)1U];
    if (emLen < sLen + (u32)32U + (u32)2U)
      return false;
    if (!(em_last == (u8)0xbcU && em_0 == (u8)0U))
      return false;
    {
      u32 emLen1 = (emBits - (u32)1U) / (u32)8U + (u32)1U;
      u32 dbLen = emLen1 - (u32)32U - (u32)1U;
      u8 *maskedDB = em;
      u8 *m1Hash = em + dbLen;
      KRML_CHECK_SIZE(sizeof (u8), dbLen);
      {
        u8 dbMask[dbLen];
        memset(dbMask, 0U, dbLen * sizeof (u8));
        mgf_sha256((u32)32U, m1Hash, dbLen, dbMask);
        xor_bytes(dbLen, dbMask, maskedDB);
        {
          u32 msBits1 = emBits % (u32)8U;
          if (msBits1 > (u32)0U)
            dbMask[0U] = dbMask[0U] & (u8)0xffU >> ((u32)8U - msBits1);
          {
            u32 padLen = emLen1 - sLen - (u32)32U - (u32)1U;
            KRML_CHECK_SIZE(sizeof (u8), padLen);
            {
              u8 pad2[padLen];
              memset(pad2, 0U, padLen * sizeof (u8));
              pad2[padLen - (u32)1U] = (u8)0x01U;
              {
                u8 *pad = dbMask;
                u8 *salt = dbMask + padLen;
                u8 res = (u8)255U;
                {
                  u32 i;
                  for (i = (u32)0U; i < padLen; i++)
                  {
                    u8 uu____0 = FStar_UInt8_eq_mask(pad[i], pad2[i]);
                    res = uu____0 & res;
                  }
                }
                {
                  u8 z = res;
                  u8 m1Hash0[32U];
                  if (!(z == (u8)255U))
                    return false;
                  {
                    u8 init = (u8)0U;
                    {
                      u32 i;
                      for (i = (u32)0U; i < (u32)32U; i++)
                        m1Hash0[i] = init;
                    }
                    {
                      u32 m1Len = (u32)40U + sLen;
                      KRML_CHECK_SIZE(sizeof (u8), m1Len);
                      {
                        u8 m1[m1Len];
                        memset(m1, 0U, m1Len * sizeof (u8));
                        hash_sha256(m1 + (u32)8U, msgLen, msg);
                        memcpy(m1 + (u32)40U, salt, sLen * sizeof (u8));
                        hash_sha256(m1Hash0, m1Len, m1);
                        {
                          u8 res0 = (u8)255U;
                          {
                            u32 i;
                            for (i = (u32)0U; i < (u32)32U; i++)
                            {
                              u8 uu____1 = FStar_UInt8_eq_mask(m1Hash0[i], m1Hash[i]);
                              res0 = uu____1 & res0;
                            }
                          }
                          {
                            u8 z0 = res0;
                            return z0 == (u8)255U;
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

static void
rsapss_sign(
  u32 modBits,
  u32 eBits,
  u32 dBits,
  u64 *skey,
  u32 sLen,
  u8 *salt,
  u32 msgLen,
  u8 *msg,
  u8 *sgnt
)
{
  u32 nLen = (modBits - (u32)1U) / (u32)64U + (u32)1U;
  u32 eLen = (eBits - (u32)1U) / (u32)64U + (u32)1U;
  u64 *n = skey;
  u64 *d = skey + nLen + eLen;
  u32 k = (modBits - (u32)1U) / (u32)8U + (u32)1U;
  u32 emBits = modBits - (u32)1U;
  u32 emLen = (emBits - (u32)1U) / (u32)8U + (u32)1U;
  KRML_CHECK_SIZE(sizeof (u8), emLen);
  {
    u8 em[emLen];
    memset(em, 0U, emLen * sizeof (u8));
    KRML_CHECK_SIZE(sizeof (u64), nLen);
    {
      u64 m[nLen];
      memset(m, 0U, nLen * sizeof (u64));
      KRML_CHECK_SIZE(sizeof (u64), nLen);
      {
        u64 s[nLen];
        memset(s, 0U, nLen * sizeof (u64));
        pss_encode(sLen, salt, msgLen, msg, emBits, em);
        bn_from_bytes_be(emLen, em, m);
        bn_mod_exp(modBits, nLen, n, m, dBits, d, s);
        bn_to_bytes_be(k, s, sgnt);
      }
    }
  }
}

static bool
rsapss_verify(u32 modBits, u32 eBits, u64 *pkey, u32 sLen, u8 *sgnt, u32 msgLen, u8 *msg)
{
  u32 nLen = (modBits - (u32)1U) / (u32)64U + (u32)1U;
  u64 *n = pkey;
  u64 *e = pkey + nLen;
  u32 k = (modBits - (u32)1U) / (u32)8U + (u32)1U;
  u32 emBits = modBits - (u32)1U;
  u32 emLen = (emBits - (u32)1U) / (u32)8U + (u32)1U;
  KRML_CHECK_SIZE(sizeof (u8), emLen);
  {
    u8 em[emLen];
    memset(em, 0U, emLen * sizeof (u8));
    KRML_CHECK_SIZE(sizeof (u64), nLen);
    {
      u64 m[nLen];
      memset(m, 0U, nLen * sizeof (u64));
      KRML_CHECK_SIZE(sizeof (u64), nLen);
      {
        u64 s[nLen];
        memset(s, 0U, nLen * sizeof (u64));
        {
          bool res;
          bn_from_bytes_be(k, sgnt, s);
          if (Hacl_Bignum_bn_is_less(nLen, s, n))
          {
            bn_mod_exp(modBits, nLen, n, s, eBits, e, m);
            {
              bool ite;
              if (!((modBits - (u32)1U) % (u32)8U == (u32)0U))
                ite = true;
              else
                ite =
                  !Hacl_Bignum_bn_is_bit_set((modBits - (u32)1U) / (u32)64U + (u32)1U,
                    m,
                    modBits - (u32)1U);
              if (ite)
              {
                u64 *m1 = m;
                bn_to_bytes_be(emLen, m1, em);
                res = pss_verify(sLen, msgLen, msg, emBits, em);
              }
              else
                res = false;
            }
          }
          else
            res = false;
          return res;
        }
      }
    }
  }
}

void
Hacl_RSAPSS_rsapss_sign(
  u32 modBits,
  u32 eBits,
  u32 dBits,
  u64 *skey,
  u32 sLen,
  u8 *salt,
  u32 msgLen,
  u8 *msg,
  u8 *sgnt
)
{
  rsapss_sign(modBits, eBits, dBits, skey, sLen, salt, msgLen, msg, sgnt);
}

bool
Hacl_RSAPSS_rsapss_verify(
  u32 modBits,
  u32 eBits,
  u64 *pkey,
  u32 sLen,
  u8 *sgnt,
  u32 msgLen,
  u8 *msg
)
{
  return rsapss_verify(modBits, eBits, pkey, sLen, sgnt, msgLen, msg);
}

