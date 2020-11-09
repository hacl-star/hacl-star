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


#include "Hacl_FFDHE.h"

inline uint32_t Hacl_Impl_FFDHE_ffdhe_len(Spec_FFDHE_ffdhe_alg a)
{
  switch (a)
  {
    case Spec_FFDHE_FFDHE2048:
      {
        return (uint32_t)256U;
      }
    case Spec_FFDHE_FFDHE3072:
      {
        return (uint32_t)384U;
      }
    case Spec_FFDHE_FFDHE4096:
      {
        return (uint32_t)512U;
      }
    case Spec_FFDHE_FFDHE6144:
      {
        return (uint32_t)768U;
      }
    case Spec_FFDHE_FFDHE8192:
      {
        return (uint32_t)1024U;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static inline uint64_t ffdhe_check_pk(Spec_FFDHE_ffdhe_alg a, uint64_t *pk_n, uint64_t *p_n)
{
  uint32_t nLen = (Hacl_Impl_FFDHE_ffdhe_len(a) - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t p_n1[nLen];
  memset(p_n1, 0U, nLen * sizeof (uint64_t));
  uint64_t b1 = (uint64_t)0U;
  b1 = (uint64_t)1U;
  uint64_t *a0 = p_n;
  uint64_t *res0 = p_n1;
  uint64_t c0 = (uint64_t)0U;
  uint32_t k0 = (uint32_t)0U;
  for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
  {
    uint64_t t1 = a0[(uint32_t)4U * i];
    uint64_t t20 = (&b1)[(uint32_t)4U * i];
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, res0 + (uint32_t)4U * i);
    uint64_t t10 = a0[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = (&b1)[(uint32_t)4U * i + (uint32_t)1U];
    c0 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
        t10,
        t21,
        res0 + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = a0[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = (&b1)[(uint32_t)4U * i + (uint32_t)2U];
    c0 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
        t11,
        t22,
        res0 + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = a0[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = (&b1)[(uint32_t)4U * i + (uint32_t)3U];
    c0 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
        t12,
        t2,
        res0 + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k0; i < (uint32_t)1U; i++)
  {
    uint64_t t1 = a0[i];
    uint64_t t2 = (&b1)[i];
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t2, res0 + i);
  }
  uint64_t c00 = c0;
  uint64_t uu____0;
  if ((uint32_t)1U < nLen)
  {
    uint32_t rLen = nLen - (uint32_t)1U;
    uint64_t *a1 = p_n + (uint32_t)1U;
    uint64_t *res1 = p_n1 + (uint32_t)1U;
    uint64_t c = c00;
    uint32_t k = rLen / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      uint64_t t1 = a1[(uint32_t)4U * i];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, (uint64_t)0U, res1 + (uint32_t)4U * i);
      uint64_t t10 = a1[(uint32_t)4U * i + (uint32_t)1U];
      c =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
          t10,
          (uint64_t)0U,
          res1 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = a1[(uint32_t)4U * i + (uint32_t)2U];
      c =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
          t11,
          (uint64_t)0U,
          res1 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = a1[(uint32_t)4U * i + (uint32_t)3U];
      c =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
          t12,
          (uint64_t)0U,
          res1 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < rLen; i++)
    {
      uint64_t t1 = a1[i];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, (uint64_t)0U, res1 + i);
    }
    uint64_t c1 = c;
    uu____0 = c1;
  }
  else
  {
    uu____0 = c00;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t b2[nLen];
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
ffdhe_compute_exp(
  Spec_FFDHE_ffdhe_alg a,
  uint64_t *p_n,
  uint64_t *sk_n,
  uint64_t *b_n,
  uint8_t *res
)
{
  uint32_t nLen = (Hacl_Impl_FFDHE_ffdhe_len(a) - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t r2_n[nLen];
  memset(r2_n, 0U, nLen * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64((Hacl_Impl_FFDHE_ffdhe_len(a) - (uint32_t)1U)
    / (uint32_t)8U
    + (uint32_t)1U,
    p_n,
    r2_n);
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t res_n[nLen];
  memset(res_n, 0U, nLen * sizeof (uint64_t));
  Hacl_Bignum_Exponentiation_bn_mod_exp_mont_ladder_precompr2_u64((Hacl_Impl_FFDHE_ffdhe_len(a)
    - (uint32_t)1U)
    / (uint32_t)8U
    + (uint32_t)1U,
    p_n,
    b_n,
    (uint32_t)64U * nLen,
    sk_n,
    r2_n,
    res_n);
  Hacl_Bignum_Convert_bn_to_bytes_be_uint64(Hacl_Impl_FFDHE_ffdhe_len(a), res_n, res);
}

uint32_t Hacl_FFDHE_ffdhe_len(Spec_FFDHE_ffdhe_alg a)
{
  return Hacl_Impl_FFDHE_ffdhe_len(a);
}

void Hacl_FFDHE_ffdhe_secret_to_public(Spec_FFDHE_ffdhe_alg a, uint8_t *sk, uint8_t *pk)
{
  uint32_t len = Hacl_Impl_FFDHE_ffdhe_len(a);
  uint32_t nLen = (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t g_n[nLen];
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
  uint64_t p_n[nLen];
  memset(p_n, 0U, nLen * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint8_t), len);
  uint8_t p_s[len];
  memset(p_s, 0U, len * sizeof (uint8_t));
  const uint8_t *p;
  switch (a)
  {
    case Spec_FFDHE_FFDHE2048:
      {
        p = Hacl_Impl_FFDHE_Constants_ffdhe_p2048;
        break;
      }
    case Spec_FFDHE_FFDHE3072:
      {
        p = Hacl_Impl_FFDHE_Constants_ffdhe_p3072;
        break;
      }
    case Spec_FFDHE_FFDHE4096:
      {
        p = Hacl_Impl_FFDHE_Constants_ffdhe_p4096;
        break;
      }
    case Spec_FFDHE_FFDHE6144:
      {
        p = Hacl_Impl_FFDHE_Constants_ffdhe_p6144;
        break;
      }
    case Spec_FFDHE_FFDHE8192:
      {
        p = Hacl_Impl_FFDHE_Constants_ffdhe_p8192;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t len1 = Hacl_Impl_FFDHE_ffdhe_len(a);
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint8_t *os = p_s;
    uint8_t x = p[i];
    os[i] = x;
  }
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(len, p_s, p_n);
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t sk_n[nLen];
  memset(sk_n, 0U, nLen * sizeof (uint64_t));
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(len, sk, sk_n);
  ffdhe_compute_exp(a, p_n, sk_n, g_n, pk);
}

uint64_t
Hacl_FFDHE_ffdhe_shared_secret(Spec_FFDHE_ffdhe_alg a, uint8_t *sk, uint8_t *pk, uint8_t *ss)
{
  uint32_t len = Hacl_Impl_FFDHE_ffdhe_len(a);
  uint32_t nLen = (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t p_n[nLen];
  memset(p_n, 0U, nLen * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint8_t), len);
  uint8_t p_s[len];
  memset(p_s, 0U, len * sizeof (uint8_t));
  const uint8_t *p;
  switch (a)
  {
    case Spec_FFDHE_FFDHE2048:
      {
        p = Hacl_Impl_FFDHE_Constants_ffdhe_p2048;
        break;
      }
    case Spec_FFDHE_FFDHE3072:
      {
        p = Hacl_Impl_FFDHE_Constants_ffdhe_p3072;
        break;
      }
    case Spec_FFDHE_FFDHE4096:
      {
        p = Hacl_Impl_FFDHE_Constants_ffdhe_p4096;
        break;
      }
    case Spec_FFDHE_FFDHE6144:
      {
        p = Hacl_Impl_FFDHE_Constants_ffdhe_p6144;
        break;
      }
    case Spec_FFDHE_FFDHE8192:
      {
        p = Hacl_Impl_FFDHE_Constants_ffdhe_p8192;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t len1 = Hacl_Impl_FFDHE_ffdhe_len(a);
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint8_t *os = p_s;
    uint8_t x = p[i];
    os[i] = x;
  }
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(len, p_s, p_n);
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t sk_n[nLen];
  memset(sk_n, 0U, nLen * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t pk_n[nLen];
  memset(pk_n, 0U, nLen * sizeof (uint64_t));
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(len, sk, sk_n);
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(len, pk, pk_n);
  uint64_t m = ffdhe_check_pk(a, pk_n, p_n);
  if (m == (uint64_t)0xFFFFFFFFFFFFFFFFU)
  {
    ffdhe_compute_exp(a, p_n, sk_n, pk_n, ss);
  }
  return m;
}

