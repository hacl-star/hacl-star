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

static inline void bn_from_bytes_be_uint64(uint32_t len, uint8_t *b, uint64_t *res)
{
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  {
    uint8_t tmp[tmpLen];
    memset(tmp, 0U, tmpLen * sizeof (uint8_t));
    memcpy(tmp + tmpLen - len, b, len * sizeof (uint8_t));
    {
      uint32_t i;
      for (i = (uint32_t)0U; i < bnLen; i++)
      {
        uint64_t *os = res;
        uint64_t u = load64_be(tmp + (bnLen - i - (uint32_t)1U) * (uint32_t)8U);
        uint64_t x = u;
        os[i] = x;
      }
    }
  }
}

static inline void bn_to_bytes_be_uint64(uint32_t len, uint64_t *b, uint8_t *res)
{
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  {
    uint8_t tmp[tmpLen];
    memset(tmp, 0U, tmpLen * sizeof (uint8_t));
    {
      uint32_t numb = (uint32_t)8U;
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < bnLen; i++)
        {
          store64_be(tmp + i * numb, b[bnLen - i - (uint32_t)1U]);
        }
      }
      memcpy(res, tmp + tmpLen - len, len * sizeof (uint8_t));
    }
  }
}

static void
bn_mont_reduction_u64(uint32_t len, uint64_t *n, uint64_t nInv, uint64_t *c, uint64_t *res)
{
  uint64_t c0 = (uint64_t)0U;
  uint64_t uu____0;
  {
    uint32_t i0;
    for (i0 = (uint32_t)0U; i0 < len; i0++)
    {
      uint64_t qj = nInv * c[i0];
      uint64_t *res_ = c + i0;
      uint64_t c1 = (uint64_t)0U;
      uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t uu____1 = n[(uint32_t)4U * i];
          uint64_t uu____2 = c1;
          uint64_t *uu____3 = res_ + (uint32_t)4U * i;
          FStar_UInt128_uint128 uu____4 = FStar_UInt128_uint64_to_uint128(uu____3[0U]);
          FStar_UInt128_uint128
          res1 =
            FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(uu____1, qj),
                FStar_UInt128_uint64_to_uint128(uu____2)),
              uu____4);
          uu____3[0U] = FStar_UInt128_uint128_to_uint64(res1);
          c1 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res1, (uint32_t)64U));
          {
            uint64_t uu____5 = n[(uint32_t)4U * i + (uint32_t)1U];
            uint64_t uu____6 = c1;
            uint64_t *uu____7 = res_ + (uint32_t)4U * i + (uint32_t)1U;
            FStar_UInt128_uint128 uu____8 = FStar_UInt128_uint64_to_uint128(uu____7[0U]);
            FStar_UInt128_uint128
            res10 =
              FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(uu____5, qj),
                  FStar_UInt128_uint64_to_uint128(uu____6)),
                uu____8);
            uu____7[0U] = FStar_UInt128_uint128_to_uint64(res10);
            c1 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res10, (uint32_t)64U));
            {
              uint64_t uu____9 = n[(uint32_t)4U * i + (uint32_t)2U];
              uint64_t uu____10 = c1;
              uint64_t *uu____11 = res_ + (uint32_t)4U * i + (uint32_t)2U;
              FStar_UInt128_uint128 uu____12 = FStar_UInt128_uint64_to_uint128(uu____11[0U]);
              FStar_UInt128_uint128
              res11 =
                FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(uu____9, qj),
                    FStar_UInt128_uint64_to_uint128(uu____10)),
                  uu____12);
              uu____11[0U] = FStar_UInt128_uint128_to_uint64(res11);
              c1 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res11, (uint32_t)64U));
              {
                uint64_t uu____13 = n[(uint32_t)4U * i + (uint32_t)3U];
                uint64_t uu____14 = c1;
                uint64_t *uu____15 = res_ + (uint32_t)4U * i + (uint32_t)3U;
                FStar_UInt128_uint128 uu____16 = FStar_UInt128_uint64_to_uint128(uu____15[0U]);
                FStar_UInt128_uint128
                res12 =
                  FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(uu____13, qj),
                      FStar_UInt128_uint64_to_uint128(uu____14)),
                    uu____16);
                uu____15[0U] = FStar_UInt128_uint128_to_uint64(res12);
                c1 =
                  FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res12, (uint32_t)64U));
              }
            }
          }
        }
      }
      {
        uint32_t i;
        for (i = k; i < len; i++)
        {
          uint64_t uu____17 = n[i];
          uint64_t uu____18 = c1;
          uint64_t *uu____19 = res_ + i;
          FStar_UInt128_uint128 uu____20 = FStar_UInt128_uint64_to_uint128(uu____19[0U]);
          FStar_UInt128_uint128
          res1 =
            FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(uu____17, qj),
                FStar_UInt128_uint64_to_uint128(uu____18)),
              uu____20);
          uu____19[0U] = FStar_UInt128_uint128_to_uint64(res1);
          c1 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res1, (uint32_t)64U));
        }
      }
      {
        uint64_t r = c1;
        uint64_t c10 = r;
        c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c10, c[len + i0], c + len + i0);
      }
    }
  }
  memcpy(res, c + len, (len + len - len) * sizeof (uint64_t));
  uu____0 = c0;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  {
    uint64_t tmp[len];
    memset(tmp, 0U, len * sizeof (uint64_t));
    {
      uint64_t c10 = (uint64_t)0U;
      uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
      uint64_t c1;
      uint64_t c2;
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = res[(uint32_t)4U * i];
          uint64_t t20 = n[(uint32_t)4U * i];
          c10 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c10, t1, t20, tmp + (uint32_t)4U * i);
          {
            uint64_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
            uint64_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
            c10 =
              Lib_IntTypes_Intrinsics_sub_borrow_u64(c10,
                t10,
                t21,
                tmp + (uint32_t)4U * i + (uint32_t)1U);
            {
              uint64_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
              uint64_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
              c10 =
                Lib_IntTypes_Intrinsics_sub_borrow_u64(c10,
                  t11,
                  t22,
                  tmp + (uint32_t)4U * i + (uint32_t)2U);
              {
                uint64_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
                uint64_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
                c10 =
                  Lib_IntTypes_Intrinsics_sub_borrow_u64(c10,
                    t12,
                    t2,
                    tmp + (uint32_t)4U * i + (uint32_t)3U);
              }
            }
          }
        }
      }
      {
        uint32_t i;
        for (i = k; i < len; i++)
        {
          uint64_t t1 = res[i];
          uint64_t t2 = n[i];
          c10 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c10, t1, t2, tmp + i);
        }
      }
      c1 = c10;
      c2 = uu____0 - c1;
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < len; i++)
        {
          uint64_t *os = res;
          uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
          os[i] = x;
        }
      }
    }
  }
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
      hLen = hash_len(a);
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

static void
bn_mod_exp_precompr2_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *r2,
  uint64_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  {
    uint64_t acc[len];
    memset(acc, 0U, len * sizeof (uint64_t));
    memset(acc, 0U, len * sizeof (uint64_t));
    acc[0U] = (uint64_t)1U;
    {
      uint64_t nInv = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
      KRML_CHECK_SIZE(sizeof (uint64_t), len);
      {
        uint64_t aM[len];
        memset(aM, 0U, len * sizeof (uint64_t));
        KRML_CHECK_SIZE(sizeof (uint64_t), len);
        {
          uint64_t accM[len];
          memset(accM, 0U, len * sizeof (uint64_t));
          KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
          {
            uint64_t c[len + len];
            memset(c, 0U, (len + len) * sizeof (uint64_t));
            KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
            {
              uint64_t tmp0[(uint32_t)4U * len];
              memset(tmp0, 0U, (uint32_t)4U * len * sizeof (uint64_t));
              Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, a, r2, tmp0, c);
              bn_mont_reduction_u64(len, n, nInv, c, aM);
              KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
              {
                uint64_t c0[len + len];
                memset(c0, 0U, (len + len) * sizeof (uint64_t));
                KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
                {
                  uint64_t tmp1[(uint32_t)4U * len];
                  memset(tmp1, 0U, (uint32_t)4U * len * sizeof (uint64_t));
                  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, acc, r2, tmp1, c0);
                  bn_mont_reduction_u64(len, n, nInv, c0, accM);
                  {
                    uint32_t i;
                    for (i = (uint32_t)0U; i < bBits; i++)
                    {
                      uint32_t i1 = i / (uint32_t)64U;
                      uint32_t j = i % (uint32_t)64U;
                      uint64_t tmp2 = b[i1];
                      uint64_t get_bit = tmp2 >> j & (uint64_t)1U;
                      if (!(get_bit == (uint64_t)0U))
                      {
                        KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
                        {
                          uint64_t c1[len + len];
                          memset(c1, 0U, (len + len) * sizeof (uint64_t));
                          KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
                          {
                            uint64_t tmp[(uint32_t)4U * len];
                            memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint64_t));
                            Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, aM, accM, tmp, c1);
                            bn_mont_reduction_u64(len, n, nInv, c1, accM);
                          }
                        }
                      }
                      KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
                      {
                        uint64_t c1[len + len];
                        memset(c1, 0U, (len + len) * sizeof (uint64_t));
                        KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
                        {
                          uint64_t tmp[(uint32_t)4U * len];
                          memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint64_t));
                          Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len, aM, tmp, c1);
                          bn_mont_reduction_u64(len, n, nInv, c1, aM);
                        }
                      }
                    }
                  }
                  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
                  {
                    uint64_t tmp[len + len];
                    memset(tmp, 0U, (len + len) * sizeof (uint64_t));
                    memcpy(tmp, accM, len * sizeof (uint64_t));
                    bn_mont_reduction_u64(len, n, nInv, tmp, res);
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
bn_mod_exp_mont_ladder_precompr2_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *r2,
  uint64_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  {
    uint64_t one[len];
    memset(one, 0U, len * sizeof (uint64_t));
    memset(one, 0U, len * sizeof (uint64_t));
    one[0U] = (uint64_t)1U;
    {
      uint64_t nInv = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
      KRML_CHECK_SIZE(sizeof (uint64_t), len);
      {
        uint64_t rM0[len];
        memset(rM0, 0U, len * sizeof (uint64_t));
        KRML_CHECK_SIZE(sizeof (uint64_t), len);
        {
          uint64_t rM1[len];
          memset(rM1, 0U, len * sizeof (uint64_t));
          {
            uint64_t sw = (uint64_t)0U;
            KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
            {
              uint64_t c[len + len];
              memset(c, 0U, (len + len) * sizeof (uint64_t));
              KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
              {
                uint64_t tmp0[(uint32_t)4U * len];
                memset(tmp0, 0U, (uint32_t)4U * len * sizeof (uint64_t));
                Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, one, r2, tmp0, c);
                bn_mont_reduction_u64(len, n, nInv, c, rM0);
                KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
                {
                  uint64_t c0[len + len];
                  memset(c0, 0U, (len + len) * sizeof (uint64_t));
                  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
                  {
                    uint64_t tmp1[(uint32_t)4U * len];
                    memset(tmp1, 0U, (uint32_t)4U * len * sizeof (uint64_t));
                    {
                      uint64_t uu____0;
                      Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, a, r2, tmp1, c0);
                      bn_mont_reduction_u64(len, n, nInv, c0, rM1);
                      {
                        uint32_t i0;
                        for (i0 = (uint32_t)0U; i0 < bBits; i0++)
                        {
                          uint32_t i1 = (bBits - i0 - (uint32_t)1U) / (uint32_t)64U;
                          uint32_t j = (bBits - i0 - (uint32_t)1U) % (uint32_t)64U;
                          uint64_t tmp2 = b[i1];
                          uint64_t bit = tmp2 >> j & (uint64_t)1U;
                          uint64_t sw1 = bit ^ sw;
                          {
                            uint32_t i;
                            for (i = (uint32_t)0U; i < len; i++)
                            {
                              uint64_t dummy = ((uint64_t)0U - sw1) & (rM0[i] ^ rM1[i]);
                              rM0[i] = rM0[i] ^ dummy;
                              rM1[i] = rM1[i] ^ dummy;
                            }
                          }
                          KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
                          {
                            uint64_t c1[len + len];
                            memset(c1, 0U, (len + len) * sizeof (uint64_t));
                            KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
                            {
                              uint64_t tmp3[(uint32_t)4U * len];
                              memset(tmp3, 0U, (uint32_t)4U * len * sizeof (uint64_t));
                              Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len,
                                rM1,
                                rM0,
                                tmp3,
                                c1);
                              bn_mont_reduction_u64(len, n, nInv, c1, rM1);
                              KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
                              {
                                uint64_t c2[len + len];
                                memset(c2, 0U, (len + len) * sizeof (uint64_t));
                                KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
                                {
                                  uint64_t tmp[(uint32_t)4U * len];
                                  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint64_t));
                                  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len, rM0, tmp, c2);
                                  bn_mont_reduction_u64(len, n, nInv, c2, rM0);
                                  sw = bit;
                                }
                              }
                            }
                          }
                        }
                      }
                      uu____0 = sw;
                      {
                        uint32_t i;
                        for (i = (uint32_t)0U; i < len; i++)
                        {
                          uint64_t dummy = ((uint64_t)0U - uu____0) & (rM0[i] ^ rM1[i]);
                          rM0[i] = rM0[i] ^ dummy;
                          rM1[i] = rM1[i] ^ dummy;
                        }
                      }
                      KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
                      {
                        uint64_t tmp[len + len];
                        memset(tmp, 0U, (len + len) * sizeof (uint64_t));
                        memcpy(tmp, rM0, len * sizeof (uint64_t));
                        bn_mont_reduction_u64(len, n, nInv, tmp, res);
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

static uint64_t check_num_bits_u64(uint32_t bs, uint64_t *b)
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

static uint64_t check_modulus_u64(uint32_t modBits, uint64_t *n)
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

static uint64_t check_exponent_u64(uint32_t eBits, uint64_t *e)
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
  {
    uint8_t em_last = em[emLen - (uint32_t)1U];
    if (emLen < sLen + hash_len(a) + (uint32_t)2U)
    {
      return false;
    }
    if (!(em_last == (uint8_t)0xbcU && em_0 == (uint8_t)0U))
    {
      return false;
    }
    {
      uint32_t emLen1 = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
      uint32_t hLen = hash_len(a);
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
  bn_from_bytes_be_uint64(nbLen, nb, n);
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  {
    uint64_t bn_zero[nLen];
    memset(bn_zero, 0U, nLen * sizeof (uint64_t));
    {
      uint64_t mask0 = (uint64_t)0xFFFFFFFFFFFFFFFFU;
      uint64_t mask10;
      uint64_t res;
      uint64_t mask;
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < nLen; i++)
        {
          uint64_t uu____0 = FStar_UInt64_eq_mask(n[i], bn_zero[i]);
          mask0 = uu____0 & mask0;
        }
      }
      mask10 = mask0;
      res = mask10;
      mask = res;
      {
        uint64_t priv0 = (uint64_t)0U;
        uint64_t ind;
        uint64_t uu____1;
        {
          uint32_t i;
          for (i = (uint32_t)0U; i < nLen; i++)
          {
            uint64_t mask1 = FStar_UInt64_eq_mask(n[i], (uint64_t)0U);
            priv0 = (mask1 & priv0) | (~mask1 & (uint64_t)i);
          }
        }
        ind = priv0;
        uu____1 = n[(uint32_t)ind];
        {
          uint64_t priv = (uint64_t)0U;
          uint64_t bs1;
          uint64_t bs;
          uint64_t bs0;
          uint32_t b;
          uint32_t i0;
          uint32_t j;
          uint64_t m0;
          uint64_t m1;
          uint64_t m;
          {
            uint32_t i;
            for (i = (uint32_t)0U; i < (uint32_t)64U; i++)
            {
              uint64_t bit_i = uu____1 >> i & (uint64_t)1U;
              uint64_t mask1 = FStar_UInt64_eq_mask(bit_i, (uint64_t)1U);
              priv = (mask1 & (uint64_t)i) | (~mask1 & priv);
            }
          }
          bs1 = priv;
          bs = (uint64_t)64U * ind + bs1;
          bs0 = ~mask & bs;
          b = (uint32_t)bs0;
          memset(r2, 0U, nLen * sizeof (uint64_t));
          i0 = b / (uint32_t)64U;
          j = b % (uint32_t)64U;
          r2[i0] = r2[i0] | (uint64_t)1U << j;
          {
            uint32_t i1;
            for (i1 = (uint32_t)0U; i1 < (uint32_t)128U * nLen - b; i1++)
            {
              uint64_t c0 = (uint64_t)0U;
              uint32_t k0 = nLen / (uint32_t)4U * (uint32_t)4U;
              {
                uint32_t i;
                for (i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
                {
                  uint64_t t1 = r2[(uint32_t)4U * i];
                  uint64_t t20 = r2[(uint32_t)4U * i];
                  c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, r2 + (uint32_t)4U * i);
                  {
                    uint64_t t10 = r2[(uint32_t)4U * i + (uint32_t)1U];
                    uint64_t t21 = r2[(uint32_t)4U * i + (uint32_t)1U];
                    c0 =
                      Lib_IntTypes_Intrinsics_add_carry_u64(c0,
                        t10,
                        t21,
                        r2 + (uint32_t)4U * i + (uint32_t)1U);
                    {
                      uint64_t t11 = r2[(uint32_t)4U * i + (uint32_t)2U];
                      uint64_t t22 = r2[(uint32_t)4U * i + (uint32_t)2U];
                      c0 =
                        Lib_IntTypes_Intrinsics_add_carry_u64(c0,
                          t11,
                          t22,
                          r2 + (uint32_t)4U * i + (uint32_t)2U);
                      {
                        uint64_t t12 = r2[(uint32_t)4U * i + (uint32_t)3U];
                        uint64_t t2 = r2[(uint32_t)4U * i + (uint32_t)3U];
                        c0 =
                          Lib_IntTypes_Intrinsics_add_carry_u64(c0,
                            t12,
                            t2,
                            r2 + (uint32_t)4U * i + (uint32_t)3U);
                      }
                    }
                  }
                }
              }
              {
                uint32_t i;
                for (i = k0; i < nLen; i++)
                {
                  uint64_t t1 = r2[i];
                  uint64_t t2 = r2[i];
                  c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, r2 + i);
                }
              }
              {
                uint64_t c00 = c0;
                KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
                {
                  uint64_t tmp[nLen];
                  memset(tmp, 0U, nLen * sizeof (uint64_t));
                  {
                    uint64_t c = (uint64_t)0U;
                    uint32_t k = nLen / (uint32_t)4U * (uint32_t)4U;
                    {
                      uint32_t i;
                      for (i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
                      {
                        uint64_t t1 = r2[(uint32_t)4U * i];
                        uint64_t t20 = n[(uint32_t)4U * i];
                        c =
                          Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
                            t1,
                            t20,
                            tmp + (uint32_t)4U * i);
                        {
                          uint64_t t10 = r2[(uint32_t)4U * i + (uint32_t)1U];
                          uint64_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
                          c =
                            Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
                              t10,
                              t21,
                              tmp + (uint32_t)4U * i + (uint32_t)1U);
                          {
                            uint64_t t11 = r2[(uint32_t)4U * i + (uint32_t)2U];
                            uint64_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
                            c =
                              Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
                                t11,
                                t22,
                                tmp + (uint32_t)4U * i + (uint32_t)2U);
                            {
                              uint64_t t12 = r2[(uint32_t)4U * i + (uint32_t)3U];
                              uint64_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
                              c =
                                Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
                                  t12,
                                  t2,
                                  tmp + (uint32_t)4U * i + (uint32_t)3U);
                            }
                          }
                        }
                      }
                    }
                    {
                      uint32_t i;
                      for (i = k; i < nLen; i++)
                      {
                        uint64_t t1 = r2[i];
                        uint64_t t2 = n[i];
                        c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, tmp + i);
                      }
                    }
                    {
                      uint64_t c1 = c;
                      uint64_t c2 = c00 - c1;
                      {
                        uint32_t i;
                        for (i = (uint32_t)0U; i < nLen; i++)
                        {
                          uint64_t *os = r2;
                          uint64_t x = (c2 & r2[i]) | (~c2 & tmp[i]);
                          os[i] = x;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          bn_from_bytes_be_uint64(ebLen, eb, e);
          m0 = check_modulus_u64(modBits, n);
          m1 = check_exponent_u64(eBits, e);
          m = m0 & m1;
          return m == (uint64_t)0xFFFFFFFFFFFFFFFFU;
        }
      }
    }
  }
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
  bn_from_bytes_be_uint64(dbLen, db, d);
  m1 = check_exponent_u64(dBits, d);
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
  uint32_t len = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t hLen = hash_len(a);
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
    uint32_t k = (modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
    uint32_t emBits = modBits - (uint32_t)1U;
    uint32_t emLen = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
    KRML_CHECK_SIZE(sizeof (uint8_t), emLen);
    {
      uint8_t em[emLen];
      memset(em, 0U, emLen * sizeof (uint8_t));
      KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
      {
        uint64_t m[nLen];
        memset(m, 0U, nLen * sizeof (uint64_t));
        KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
        {
          uint64_t m_[nLen];
          memset(m_, 0U, nLen * sizeof (uint64_t));
          KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
          {
            uint64_t s[nLen];
            memset(s, 0U, nLen * sizeof (uint64_t));
            pss_encode(a, sLen, salt, msgLen, msg, emBits, em);
            bn_from_bytes_be_uint64(emLen, em, m);
            {
              uint32_t nLen1 = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
              uint32_t eLen = (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
              uint64_t *n = skey;
              uint64_t *r2 = skey + nLen1;
              uint64_t *e = skey + nLen1 + nLen1;
              uint64_t *d = skey + nLen1 + nLen1 + eLen;
              bn_mod_exp_mont_ladder_precompr2_u64(len, n, m, dBits, d, r2, s);
              bn_mod_exp_precompr2_u64(len, n, s, eBits, e, r2, m_);
              {
                uint64_t mask = (uint64_t)0xFFFFFFFFFFFFFFFFU;
                {
                  uint32_t i;
                  for (i = (uint32_t)0U; i < nLen1; i++)
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
                    for (i = (uint32_t)0U; i < nLen1; i++)
                    {
                      uint64_t *os = s;
                      uint64_t x = s[i];
                      uint64_t x0 = eq_m & x;
                      os[i] = x0;
                    }
                  }
                  {
                    bool eq_b = eq_m == (uint64_t)0xFFFFFFFFFFFFFFFFU;
                    bn_to_bytes_be_uint64(k, s, sgnt);
                    return eq_b;
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
  uint32_t len = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t hLen = hash_len(a);
  bool
  b =
    sLen
    <= (uint32_t)0xffffffffU - hLen - (uint32_t)8U
    && k == (modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  if (b)
  {
    uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
    uint32_t k1 = (modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
    uint32_t emBits = modBits - (uint32_t)1U;
    uint32_t emLen = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
    KRML_CHECK_SIZE(sizeof (uint8_t), emLen);
    {
      uint8_t em[emLen];
      memset(em, 0U, emLen * sizeof (uint8_t));
      KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
      {
        uint64_t m[nLen];
        memset(m, 0U, nLen * sizeof (uint64_t));
        KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
        {
          uint64_t s[nLen];
          memset(s, 0U, nLen * sizeof (uint64_t));
          bn_from_bytes_be_uint64(k1, sgnt, s);
          {
            uint32_t nLen1 = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
            uint64_t *n = pkey;
            uint64_t *r2 = pkey + nLen1;
            uint64_t *e = pkey + nLen1 + nLen1;
            uint64_t acc = (uint64_t)0U;
            {
              uint32_t i;
              for (i = (uint32_t)0U; i < nLen1; i++)
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
                bn_mod_exp_precompr2_u64(len, n, s, eBits, e, r2, m);
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
                if (b1)
                {
                  uint64_t *m1 = m;
                  bn_to_bytes_be_uint64(emLen, m1, em);
                  return pss_verify(a, sLen, msgLen, msg, emBits, em);
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

