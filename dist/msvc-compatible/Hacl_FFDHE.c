/* MIT License
 *
 * Copyright (c) 2016-2022 INRIA, CMU and Microsoft Corporation
 * Copyright (c) 2022-2023 HACL* Contributors
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

#include "internal/Hacl_Impl_FFDHE_Constants.h"
#include "internal/Hacl_Bignum_Base.h"
#include "internal/Hacl_Bignum.h"

static inline uint32_t ffdhe_len(Spec_FFDHE_ffdhe_alg a)
{
  switch (a)
  {
    case Spec_FFDHE_FFDHE2048:
      {
        return 256U;
      }
    case Spec_FFDHE_FFDHE3072:
      {
        return 384U;
      }
    case Spec_FFDHE_FFDHE4096:
      {
        return 512U;
      }
    case Spec_FFDHE_FFDHE6144:
      {
        return 768U;
      }
    case Spec_FFDHE_FFDHE8192:
      {
        return 1024U;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static inline void ffdhe_precomp_p(Spec_FFDHE_ffdhe_alg a, uint64_t *p_r2_n)
{
  uint32_t nLen = (ffdhe_len(a) - 1U) / 8U + 1U;
  uint64_t *p_n = p_r2_n;
  uint64_t *r2_n = p_r2_n + nLen;
  uint32_t sw;
  switch (a)
  {
    case Spec_FFDHE_FFDHE2048:
      {
        sw = 256U;
        break;
      }
    case Spec_FFDHE_FFDHE3072:
      {
        sw = 384U;
        break;
      }
    case Spec_FFDHE_FFDHE4096:
      {
        sw = 512U;
        break;
      }
    case Spec_FFDHE_FFDHE6144:
      {
        sw = 768U;
        break;
      }
    case Spec_FFDHE_FFDHE8192:
      {
        sw = 1024U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), sw);
  uint8_t *p_s = (uint8_t *)alloca(sw * sizeof (uint8_t));
  memset(p_s, 0U, sw * sizeof (uint8_t));
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
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t len = ffdhe_len(a);
  for (uint32_t i = 0U; i < len; i++)
  {
    uint8_t *os = p_s;
    uint8_t x = p[i];
    os[i] = x;
  }
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(ffdhe_len(a), p_s, p_n);
  Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64((ffdhe_len(a) - 1U) / 8U + 1U,
    8U * ffdhe_len(a) - 1U,
    p_n,
    r2_n);
}

static inline uint64_t ffdhe_check_pk(Spec_FFDHE_ffdhe_alg a, uint64_t *pk_n, uint64_t *p_n)
{
  uint32_t nLen = (ffdhe_len(a) - 1U) / 8U + 1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *p_n1 = (uint64_t *)alloca(nLen * sizeof (uint64_t));
  memset(p_n1, 0U, nLen * sizeof (uint64_t));
  uint64_t c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(0ULL, p_n[0U], 1ULL, p_n1);
  if (1U < nLen)
  {
    uint64_t *a1 = p_n + 1U;
    uint64_t *res1 = p_n1 + 1U;
    uint64_t c = c0;
    for (uint32_t i = 0U; i < (nLen - 1U) / 4U; i++)
    {
      uint64_t t1 = a1[4U * i];
      uint64_t *res_i0 = res1 + 4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, 0ULL, res_i0);
      uint64_t t10 = a1[4U * i + 1U];
      uint64_t *res_i1 = res1 + 4U * i + 1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, 0ULL, res_i1);
      uint64_t t11 = a1[4U * i + 2U];
      uint64_t *res_i2 = res1 + 4U * i + 2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, 0ULL, res_i2);
      uint64_t t12 = a1[4U * i + 3U];
      uint64_t *res_i = res1 + 4U * i + 3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, 0ULL, res_i);
    }
    for (uint32_t i = (nLen - 1U) / 4U * 4U; i < nLen - 1U; i++)
    {
      uint64_t t1 = a1[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, 0ULL, res_i);
    }
    uint64_t c1 = c;
    KRML_MAYBE_UNUSED_VAR(c1);
  }
  else
  {
    KRML_MAYBE_UNUSED_VAR(c0);
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *b2 = (uint64_t *)alloca(nLen * sizeof (uint64_t));
  memset(b2, 0U, nLen * sizeof (uint64_t));
  uint32_t i0 = 0U;
  uint32_t j = 0U;
  b2[i0] = b2[i0] | 1ULL << j;
  uint64_t acc0 = 0ULL;
  for (uint32_t i = 0U; i < nLen; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(b2[i], pk_n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(b2[i], pk_n[i]);
    acc0 = (beq & acc0) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL)));
  }
  uint64_t res = acc0;
  uint64_t m0 = res;
  uint64_t acc = 0ULL;
  for (uint32_t i = 0U; i < nLen; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(pk_n[i], p_n1[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(pk_n[i], p_n1[i]);
    acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL)));
  }
  uint64_t m1 = acc;
  return m0 & m1;
}

static inline void
ffdhe_compute_exp(
  Spec_FFDHE_ffdhe_alg a,
  uint64_t *p_r2_n,
  uint64_t *sk_n,
  uint64_t *b_n,
  uint8_t *res
)
{
  uint32_t nLen = (ffdhe_len(a) - 1U) / 8U + 1U;
  uint64_t *p_n = p_r2_n;
  uint64_t *r2_n = p_r2_n + nLen;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *res_n = (uint64_t *)alloca(nLen * sizeof (uint64_t));
  memset(res_n, 0U, nLen * sizeof (uint64_t));
  uint64_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint64(p_n[0U]);
  Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u64((ffdhe_len(a) - 1U) / 8U + 1U,
    p_n,
    mu,
    r2_n,
    b_n,
    64U * nLen,
    sk_n,
    res_n);
  Hacl_Bignum_Convert_bn_to_bytes_be_uint64(ffdhe_len(a), res_n, res);
}

uint32_t Hacl_FFDHE_ffdhe_len(Spec_FFDHE_ffdhe_alg a)
{
  return ffdhe_len(a);
}

uint64_t *Hacl_FFDHE_new_ffdhe_precomp_p(Spec_FFDHE_ffdhe_alg a)
{
  uint32_t nLen = (ffdhe_len(a) - 1U) / 8U + 1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen + nLen);
  uint64_t *res = (uint64_t *)KRML_HOST_CALLOC(nLen + nLen, sizeof (uint64_t));
  if (res == NULL)
  {
    return res;
  }
  uint64_t *res1 = res;
  uint64_t *res2 = res1;
  ffdhe_precomp_p(a, res2);
  return res2;
}

void
Hacl_FFDHE_ffdhe_secret_to_public_precomp(
  Spec_FFDHE_ffdhe_alg a,
  uint64_t *p_r2_n,
  uint8_t *sk,
  uint8_t *pk
)
{
  uint32_t len = ffdhe_len(a);
  uint32_t nLen = (len - 1U) / 8U + 1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *g_n = (uint64_t *)alloca(nLen * sizeof (uint64_t));
  memset(g_n, 0U, nLen * sizeof (uint64_t));
  uint8_t g = 0U;
  {
    uint8_t *os = &g;
    uint8_t x = Hacl_Impl_FFDHE_Constants_ffdhe_g2[0U];
    os[0U] = x;
  }
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(1U, &g, g_n);
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *sk_n = (uint64_t *)alloca(nLen * sizeof (uint64_t));
  memset(sk_n, 0U, nLen * sizeof (uint64_t));
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(len, sk, sk_n);
  ffdhe_compute_exp(a, p_r2_n, sk_n, g_n, pk);
}

void Hacl_FFDHE_ffdhe_secret_to_public(Spec_FFDHE_ffdhe_alg a, uint8_t *sk, uint8_t *pk)
{
  uint32_t len = ffdhe_len(a);
  uint32_t nLen = (len - 1U) / 8U + 1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen + nLen);
  uint64_t *p_r2_n = (uint64_t *)alloca((nLen + nLen) * sizeof (uint64_t));
  memset(p_r2_n, 0U, (nLen + nLen) * sizeof (uint64_t));
  ffdhe_precomp_p(a, p_r2_n);
  Hacl_FFDHE_ffdhe_secret_to_public_precomp(a, p_r2_n, sk, pk);
}

uint64_t
Hacl_FFDHE_ffdhe_shared_secret_precomp(
  Spec_FFDHE_ffdhe_alg a,
  uint64_t *p_r2_n,
  uint8_t *sk,
  uint8_t *pk,
  uint8_t *ss
)
{
  uint32_t len = ffdhe_len(a);
  uint32_t nLen = (len - 1U) / 8U + 1U;
  uint64_t *p_n = p_r2_n;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *sk_n = (uint64_t *)alloca(nLen * sizeof (uint64_t));
  memset(sk_n, 0U, nLen * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *pk_n = (uint64_t *)alloca(nLen * sizeof (uint64_t));
  memset(pk_n, 0U, nLen * sizeof (uint64_t));
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(len, sk, sk_n);
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(len, pk, pk_n);
  uint64_t m = ffdhe_check_pk(a, pk_n, p_n);
  if (m == 0xFFFFFFFFFFFFFFFFULL)
  {
    ffdhe_compute_exp(a, p_r2_n, sk_n, pk_n, ss);
  }
  return m;
}

uint64_t
Hacl_FFDHE_ffdhe_shared_secret(Spec_FFDHE_ffdhe_alg a, uint8_t *sk, uint8_t *pk, uint8_t *ss)
{
  uint32_t len = ffdhe_len(a);
  uint32_t nLen = (len - 1U) / 8U + 1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen + nLen);
  uint64_t *p_n = (uint64_t *)alloca((nLen + nLen) * sizeof (uint64_t));
  memset(p_n, 0U, (nLen + nLen) * sizeof (uint64_t));
  ffdhe_precomp_p(a, p_n);
  uint64_t m = Hacl_FFDHE_ffdhe_shared_secret_precomp(a, p_n, sk, pk, ss);
  return m;
}

