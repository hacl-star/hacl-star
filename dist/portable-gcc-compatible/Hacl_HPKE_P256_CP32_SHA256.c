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


#include "Hacl_HPKE_P256_CP32_SHA256.h"

#include "internal/Hacl_P256.h"

/* SNIPPET_START: Hacl_HPKE_P256_CP32_SHA256_setupBaseS */

uint32_t
Hacl_HPKE_P256_CP32_SHA256_setupBaseS(
  uint8_t *o_pkE,
  Hacl_Impl_HPKE_context_s o_ctx,
  uint8_t *skE,
  uint8_t *pkR,
  uint32_t infolen,
  uint8_t *info
)
{
  uint8_t o_shared[32U] = { 0U };
  uint8_t *o_pkE1 = o_pkE + (uint32_t)1U;
  bool res0 = Hacl_Impl_P256_DH_ecp256dh_i(o_pkE1, skE);
  uint32_t res1;
  if (res0)
  {
    res1 = (uint32_t)0U;
  }
  else
  {
    res1 = (uint32_t)1U;
  }
  uint32_t res3;
  if (res1 == (uint32_t)0U)
  {
    o_pkE[0U] = (uint8_t)4U;
    uint8_t o_dh[64U] = { 0U };
    uint8_t tmp0[64U] = { 0U };
    bool res = Hacl_Impl_P256_DH_ecp256dh_r(tmp0, pkR, skE);
    memcpy(o_dh, tmp0, (uint32_t)64U * sizeof (uint8_t));
    uint32_t res2;
    if (res)
    {
      res2 = (uint32_t)0U;
    }
    else
    {
      res2 = (uint32_t)1U;
    }
    uint8_t o_kemcontext[130U] = { 0U };
    if (res2 == (uint32_t)0U)
    {
      memcpy(o_kemcontext, o_pkE, (uint32_t)65U * sizeof (uint8_t));
      uint8_t *o_pkRm = o_kemcontext + (uint32_t)65U;
      uint8_t *o_pkR = o_pkRm + (uint32_t)1U;
      memcpy(o_pkR, pkR, (uint32_t)64U * sizeof (uint8_t));
      o_pkRm[0U] = (uint8_t)4U;
      uint8_t *o_dhm = o_dh;
      uint8_t o_eae_prk[32U] = { 0U };
      uint8_t suite_id_kem[5U] = { 0U };
      uint8_t *uu____0 = suite_id_kem;
      uu____0[0U] = (uint8_t)0x4bU;
      uu____0[1U] = (uint8_t)0x45U;
      uu____0[2U] = (uint8_t)0x4dU;
      uint8_t *uu____1 = suite_id_kem + (uint32_t)3U;
      uu____1[0U] = (uint8_t)0U;
      uu____1[1U] = (uint8_t)16U;
      uint8_t *empty = suite_id_kem;
      uint8_t
      label_eae_prk[7U] =
        {
          (uint8_t)0x65U, (uint8_t)0x61U, (uint8_t)0x65U, (uint8_t)0x5fU, (uint8_t)0x70U,
          (uint8_t)0x72U, (uint8_t)0x6bU
        };
      uint32_t len0 = (uint32_t)51U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len0);
      uint8_t tmp1[len0];
      memset(tmp1, 0U, len0 * sizeof (uint8_t));
      uint8_t *uu____2 = tmp1;
      uu____2[0U] = (uint8_t)0x48U;
      uu____2[1U] = (uint8_t)0x50U;
      uu____2[2U] = (uint8_t)0x4bU;
      uu____2[3U] = (uint8_t)0x45U;
      uu____2[4U] = (uint8_t)0x2dU;
      uu____2[5U] = (uint8_t)0x76U;
      uu____2[6U] = (uint8_t)0x31U;
      memcpy(tmp1 + (uint32_t)7U, suite_id_kem, (uint32_t)5U * sizeof (uint8_t));
      memcpy(tmp1 + (uint32_t)12U, label_eae_prk, (uint32_t)7U * sizeof (uint8_t));
      memcpy(tmp1 + (uint32_t)19U, o_dhm, (uint32_t)32U * sizeof (uint8_t));
      Hacl_HKDF_extract_sha2_256(o_eae_prk, empty, (uint32_t)0U, tmp1, len0);
      uint8_t
      label_shared_secret[13U] =
        {
          (uint8_t)0x73U, (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x72U, (uint8_t)0x65U,
          (uint8_t)0x64U, (uint8_t)0x5fU, (uint8_t)0x73U, (uint8_t)0x65U, (uint8_t)0x63U,
          (uint8_t)0x72U, (uint8_t)0x65U, (uint8_t)0x74U
        };
      uint32_t len = (uint32_t)157U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len);
      uint8_t tmp[len];
      memset(tmp, 0U, len * sizeof (uint8_t));
      store16_be(tmp, (uint16_t)(uint32_t)32U);
      uint8_t *uu____3 = tmp + (uint32_t)2U;
      uu____3[0U] = (uint8_t)0x48U;
      uu____3[1U] = (uint8_t)0x50U;
      uu____3[2U] = (uint8_t)0x4bU;
      uu____3[3U] = (uint8_t)0x45U;
      uu____3[4U] = (uint8_t)0x2dU;
      uu____3[5U] = (uint8_t)0x76U;
      uu____3[6U] = (uint8_t)0x31U;
      memcpy(tmp + (uint32_t)9U, suite_id_kem, (uint32_t)5U * sizeof (uint8_t));
      memcpy(tmp + (uint32_t)14U, label_shared_secret, (uint32_t)13U * sizeof (uint8_t));
      memcpy(tmp + (uint32_t)27U, o_kemcontext, (uint32_t)130U * sizeof (uint8_t));
      Hacl_HKDF_expand_sha2_256(o_shared, o_eae_prk, (uint32_t)32U, tmp, len, (uint32_t)32U);
      res3 = (uint32_t)0U;
    }
    else
    {
      res3 = (uint32_t)1U;
    }
  }
  else
  {
    res3 = (uint32_t)1U;
  }
  if (res3 == (uint32_t)0U)
  {
    uint8_t o_context[65U] = { 0U };
    uint8_t o_secret[32U] = { 0U };
    uint8_t suite_id[10U] = { 0U };
    uint8_t *uu____4 = suite_id;
    uu____4[0U] = (uint8_t)0x48U;
    uu____4[1U] = (uint8_t)0x50U;
    uu____4[2U] = (uint8_t)0x4bU;
    uu____4[3U] = (uint8_t)0x45U;
    uint8_t *uu____5 = suite_id + (uint32_t)4U;
    uu____5[0U] = (uint8_t)0U;
    uu____5[1U] = (uint8_t)16U;
    uint8_t *uu____6 = suite_id + (uint32_t)6U;
    uu____6[0U] = (uint8_t)0U;
    uu____6[1U] = (uint8_t)1U;
    uint8_t *uu____7 = suite_id + (uint32_t)8U;
    uu____7[0U] = (uint8_t)0U;
    uu____7[1U] = (uint8_t)3U;
    uint8_t
    label_psk_id_hash[11U] =
      {
        (uint8_t)0x70U, (uint8_t)0x73U, (uint8_t)0x6bU, (uint8_t)0x5fU, (uint8_t)0x69U,
        (uint8_t)0x64U, (uint8_t)0x5fU, (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x73U,
        (uint8_t)0x68U
      };
    uint8_t o_psk_id_hash[32U] = { 0U };
    uint8_t *empty = suite_id;
    uint32_t len0 = (uint32_t)28U;
    KRML_CHECK_SIZE(sizeof (uint8_t), len0);
    uint8_t tmp0[len0];
    memset(tmp0, 0U, len0 * sizeof (uint8_t));
    uint8_t *uu____8 = tmp0;
    uu____8[0U] = (uint8_t)0x48U;
    uu____8[1U] = (uint8_t)0x50U;
    uu____8[2U] = (uint8_t)0x4bU;
    uu____8[3U] = (uint8_t)0x45U;
    uu____8[4U] = (uint8_t)0x2dU;
    uu____8[5U] = (uint8_t)0x76U;
    uu____8[6U] = (uint8_t)0x31U;
    memcpy(tmp0 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
    memcpy(tmp0 + (uint32_t)17U, label_psk_id_hash, (uint32_t)11U * sizeof (uint8_t));
    memcpy(tmp0 + (uint32_t)28U, empty, (uint32_t)0U * sizeof (uint8_t));
    Hacl_HKDF_extract_sha2_256(o_psk_id_hash, empty, (uint32_t)0U, tmp0, len0);
    uint8_t
    label_info_hash[9U] =
      {
        (uint8_t)0x69U, (uint8_t)0x6eU, (uint8_t)0x66U, (uint8_t)0x6fU, (uint8_t)0x5fU,
        (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x73U, (uint8_t)0x68U
      };
    uint8_t o_info_hash[32U] = { 0U };
    uint32_t len1 = (uint32_t)26U + infolen;
    KRML_CHECK_SIZE(sizeof (uint8_t), len1);
    uint8_t tmp1[len1];
    memset(tmp1, 0U, len1 * sizeof (uint8_t));
    uint8_t *uu____9 = tmp1;
    uu____9[0U] = (uint8_t)0x48U;
    uu____9[1U] = (uint8_t)0x50U;
    uu____9[2U] = (uint8_t)0x4bU;
    uu____9[3U] = (uint8_t)0x45U;
    uu____9[4U] = (uint8_t)0x2dU;
    uu____9[5U] = (uint8_t)0x76U;
    uu____9[6U] = (uint8_t)0x31U;
    memcpy(tmp1 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
    memcpy(tmp1 + (uint32_t)17U, label_info_hash, (uint32_t)9U * sizeof (uint8_t));
    memcpy(tmp1 + (uint32_t)26U, info, infolen * sizeof (uint8_t));
    Hacl_HKDF_extract_sha2_256(o_info_hash, empty, (uint32_t)0U, tmp1, len1);
    o_context[0U] = (uint8_t)0U;
    memcpy(o_context + (uint32_t)1U, o_psk_id_hash, (uint32_t)32U * sizeof (uint8_t));
    memcpy(o_context + (uint32_t)33U, o_info_hash, (uint32_t)32U * sizeof (uint8_t));
    uint8_t
    label_secret[6U] =
      {
        (uint8_t)0x73U, (uint8_t)0x65U, (uint8_t)0x63U, (uint8_t)0x72U, (uint8_t)0x65U,
        (uint8_t)0x74U
      };
    uint32_t len2 = (uint32_t)23U;
    KRML_CHECK_SIZE(sizeof (uint8_t), len2);
    uint8_t tmp2[len2];
    memset(tmp2, 0U, len2 * sizeof (uint8_t));
    uint8_t *uu____10 = tmp2;
    uu____10[0U] = (uint8_t)0x48U;
    uu____10[1U] = (uint8_t)0x50U;
    uu____10[2U] = (uint8_t)0x4bU;
    uu____10[3U] = (uint8_t)0x45U;
    uu____10[4U] = (uint8_t)0x2dU;
    uu____10[5U] = (uint8_t)0x76U;
    uu____10[6U] = (uint8_t)0x31U;
    memcpy(tmp2 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
    memcpy(tmp2 + (uint32_t)17U, label_secret, (uint32_t)6U * sizeof (uint8_t));
    memcpy(tmp2 + (uint32_t)23U, empty, (uint32_t)0U * sizeof (uint8_t));
    Hacl_HKDF_extract_sha2_256(o_secret, o_shared, (uint32_t)32U, tmp2, len2);
    uint8_t label_exp[3U] = { (uint8_t)0x65U, (uint8_t)0x78U, (uint8_t)0x70U };
    uint32_t len3 = (uint32_t)87U;
    KRML_CHECK_SIZE(sizeof (uint8_t), len3);
    uint8_t tmp3[len3];
    memset(tmp3, 0U, len3 * sizeof (uint8_t));
    store16_be(tmp3, (uint16_t)(uint32_t)32U);
    uint8_t *uu____11 = tmp3 + (uint32_t)2U;
    uu____11[0U] = (uint8_t)0x48U;
    uu____11[1U] = (uint8_t)0x50U;
    uu____11[2U] = (uint8_t)0x4bU;
    uu____11[3U] = (uint8_t)0x45U;
    uu____11[4U] = (uint8_t)0x2dU;
    uu____11[5U] = (uint8_t)0x76U;
    uu____11[6U] = (uint8_t)0x31U;
    memcpy(tmp3 + (uint32_t)9U, suite_id, (uint32_t)10U * sizeof (uint8_t));
    memcpy(tmp3 + (uint32_t)19U, label_exp, (uint32_t)3U * sizeof (uint8_t));
    memcpy(tmp3 + (uint32_t)22U, o_context, (uint32_t)65U * sizeof (uint8_t));
    Hacl_HKDF_expand_sha2_256(o_ctx.ctx_exporter,
      o_secret,
      (uint32_t)32U,
      tmp3,
      len3,
      (uint32_t)32U);
    uint8_t label_key[3U] = { (uint8_t)0x6bU, (uint8_t)0x65U, (uint8_t)0x79U };
    uint32_t len4 = (uint32_t)87U;
    KRML_CHECK_SIZE(sizeof (uint8_t), len4);
    uint8_t tmp4[len4];
    memset(tmp4, 0U, len4 * sizeof (uint8_t));
    store16_be(tmp4, (uint16_t)(uint32_t)32U);
    uint8_t *uu____12 = tmp4 + (uint32_t)2U;
    uu____12[0U] = (uint8_t)0x48U;
    uu____12[1U] = (uint8_t)0x50U;
    uu____12[2U] = (uint8_t)0x4bU;
    uu____12[3U] = (uint8_t)0x45U;
    uu____12[4U] = (uint8_t)0x2dU;
    uu____12[5U] = (uint8_t)0x76U;
    uu____12[6U] = (uint8_t)0x31U;
    memcpy(tmp4 + (uint32_t)9U, suite_id, (uint32_t)10U * sizeof (uint8_t));
    memcpy(tmp4 + (uint32_t)19U, label_key, (uint32_t)3U * sizeof (uint8_t));
    memcpy(tmp4 + (uint32_t)22U, o_context, (uint32_t)65U * sizeof (uint8_t));
    Hacl_HKDF_expand_sha2_256(o_ctx.ctx_key, o_secret, (uint32_t)32U, tmp4, len4, (uint32_t)32U);
    uint8_t
    label_base_nonce[10U] =
      {
        (uint8_t)0x62U, (uint8_t)0x61U, (uint8_t)0x73U, (uint8_t)0x65U, (uint8_t)0x5fU,
        (uint8_t)0x6eU, (uint8_t)0x6fU, (uint8_t)0x6eU, (uint8_t)0x63U, (uint8_t)0x65U
      };
    uint32_t len = (uint32_t)94U;
    KRML_CHECK_SIZE(sizeof (uint8_t), len);
    uint8_t tmp[len];
    memset(tmp, 0U, len * sizeof (uint8_t));
    store16_be(tmp, (uint16_t)(uint32_t)12U);
    uint8_t *uu____13 = tmp + (uint32_t)2U;
    uu____13[0U] = (uint8_t)0x48U;
    uu____13[1U] = (uint8_t)0x50U;
    uu____13[2U] = (uint8_t)0x4bU;
    uu____13[3U] = (uint8_t)0x45U;
    uu____13[4U] = (uint8_t)0x2dU;
    uu____13[5U] = (uint8_t)0x76U;
    uu____13[6U] = (uint8_t)0x31U;
    memcpy(tmp + (uint32_t)9U, suite_id, (uint32_t)10U * sizeof (uint8_t));
    memcpy(tmp + (uint32_t)19U, label_base_nonce, (uint32_t)10U * sizeof (uint8_t));
    memcpy(tmp + (uint32_t)29U, o_context, (uint32_t)65U * sizeof (uint8_t));
    Hacl_HKDF_expand_sha2_256(o_ctx.ctx_nonce, o_secret, (uint32_t)32U, tmp, len, (uint32_t)12U);
    o_ctx.ctx_seq[0U] = (uint64_t)0U;
    return res3;
  }
  return res3;
}

/* SNIPPET_END: Hacl_HPKE_P256_CP32_SHA256_setupBaseS */

/* SNIPPET_START: Hacl_HPKE_P256_CP32_SHA256_setupBaseR */

uint32_t
Hacl_HPKE_P256_CP32_SHA256_setupBaseR(
  Hacl_Impl_HPKE_context_s o_ctx,
  uint8_t *enc,
  uint8_t *skR,
  uint32_t infolen,
  uint8_t *info
)
{
  uint8_t pkR[64U] = { 0U };
  bool res0 = Hacl_Impl_P256_DH_ecp256dh_i(pkR, skR);
  uint32_t res1;
  if (res0)
  {
    res1 = (uint32_t)0U;
  }
  else
  {
    res1 = (uint32_t)1U;
  }
  uint8_t shared[32U] = { 0U };
  if (res1 == (uint32_t)0U)
  {
    uint8_t *pkE = enc + (uint32_t)1U;
    uint8_t dh[64U] = { 0U };
    uint8_t tmp0[64U] = { 0U };
    bool res = Hacl_Impl_P256_DH_ecp256dh_r(tmp0, pkE, skR);
    memcpy(dh, tmp0, (uint32_t)64U * sizeof (uint8_t));
    uint32_t res11;
    if (res)
    {
      res11 = (uint32_t)0U;
    }
    else
    {
      res11 = (uint32_t)1U;
    }
    uint32_t res20;
    uint8_t kemcontext[130U] = { 0U };
    if (res11 == (uint32_t)0U)
    {
      uint8_t *pkRm = kemcontext + (uint32_t)65U;
      uint8_t *pkR1 = pkRm + (uint32_t)1U;
      bool res3 = Hacl_Impl_P256_DH_ecp256dh_i(pkR1, skR);
      uint32_t res2;
      if (res3)
      {
        res2 = (uint32_t)0U;
      }
      else
      {
        res2 = (uint32_t)1U;
      }
      if (res2 == (uint32_t)0U)
      {
        memcpy(kemcontext, enc, (uint32_t)65U * sizeof (uint8_t));
        pkRm[0U] = (uint8_t)4U;
        uint8_t *dhm = dh;
        uint8_t o_eae_prk[32U] = { 0U };
        uint8_t suite_id_kem[5U] = { 0U };
        uint8_t *uu____0 = suite_id_kem;
        uu____0[0U] = (uint8_t)0x4bU;
        uu____0[1U] = (uint8_t)0x45U;
        uu____0[2U] = (uint8_t)0x4dU;
        uint8_t *uu____1 = suite_id_kem + (uint32_t)3U;
        uu____1[0U] = (uint8_t)0U;
        uu____1[1U] = (uint8_t)16U;
        uint8_t *empty = suite_id_kem;
        uint8_t
        label_eae_prk[7U] =
          {
            (uint8_t)0x65U, (uint8_t)0x61U, (uint8_t)0x65U, (uint8_t)0x5fU, (uint8_t)0x70U,
            (uint8_t)0x72U, (uint8_t)0x6bU
          };
        uint32_t len0 = (uint32_t)51U;
        KRML_CHECK_SIZE(sizeof (uint8_t), len0);
        uint8_t tmp1[len0];
        memset(tmp1, 0U, len0 * sizeof (uint8_t));
        uint8_t *uu____2 = tmp1;
        uu____2[0U] = (uint8_t)0x48U;
        uu____2[1U] = (uint8_t)0x50U;
        uu____2[2U] = (uint8_t)0x4bU;
        uu____2[3U] = (uint8_t)0x45U;
        uu____2[4U] = (uint8_t)0x2dU;
        uu____2[5U] = (uint8_t)0x76U;
        uu____2[6U] = (uint8_t)0x31U;
        memcpy(tmp1 + (uint32_t)7U, suite_id_kem, (uint32_t)5U * sizeof (uint8_t));
        memcpy(tmp1 + (uint32_t)12U, label_eae_prk, (uint32_t)7U * sizeof (uint8_t));
        memcpy(tmp1 + (uint32_t)19U, dhm, (uint32_t)32U * sizeof (uint8_t));
        Hacl_HKDF_extract_sha2_256(o_eae_prk, empty, (uint32_t)0U, tmp1, len0);
        uint8_t
        label_shared_secret[13U] =
          {
            (uint8_t)0x73U, (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x72U, (uint8_t)0x65U,
            (uint8_t)0x64U, (uint8_t)0x5fU, (uint8_t)0x73U, (uint8_t)0x65U, (uint8_t)0x63U,
            (uint8_t)0x72U, (uint8_t)0x65U, (uint8_t)0x74U
          };
        uint32_t len = (uint32_t)157U;
        KRML_CHECK_SIZE(sizeof (uint8_t), len);
        uint8_t tmp[len];
        memset(tmp, 0U, len * sizeof (uint8_t));
        store16_be(tmp, (uint16_t)(uint32_t)32U);
        uint8_t *uu____3 = tmp + (uint32_t)2U;
        uu____3[0U] = (uint8_t)0x48U;
        uu____3[1U] = (uint8_t)0x50U;
        uu____3[2U] = (uint8_t)0x4bU;
        uu____3[3U] = (uint8_t)0x45U;
        uu____3[4U] = (uint8_t)0x2dU;
        uu____3[5U] = (uint8_t)0x76U;
        uu____3[6U] = (uint8_t)0x31U;
        memcpy(tmp + (uint32_t)9U, suite_id_kem, (uint32_t)5U * sizeof (uint8_t));
        memcpy(tmp + (uint32_t)14U, label_shared_secret, (uint32_t)13U * sizeof (uint8_t));
        memcpy(tmp + (uint32_t)27U, kemcontext, (uint32_t)130U * sizeof (uint8_t));
        Hacl_HKDF_expand_sha2_256(shared, o_eae_prk, (uint32_t)32U, tmp, len, (uint32_t)32U);
        res20 = (uint32_t)0U;
      }
      else
      {
        res20 = (uint32_t)1U;
      }
    }
    else
    {
      res20 = (uint32_t)1U;
    }
    if (res20 == (uint32_t)0U)
    {
      uint8_t o_context[65U] = { 0U };
      uint8_t o_secret[32U] = { 0U };
      uint8_t suite_id[10U] = { 0U };
      uint8_t *uu____4 = suite_id;
      uu____4[0U] = (uint8_t)0x48U;
      uu____4[1U] = (uint8_t)0x50U;
      uu____4[2U] = (uint8_t)0x4bU;
      uu____4[3U] = (uint8_t)0x45U;
      uint8_t *uu____5 = suite_id + (uint32_t)4U;
      uu____5[0U] = (uint8_t)0U;
      uu____5[1U] = (uint8_t)16U;
      uint8_t *uu____6 = suite_id + (uint32_t)6U;
      uu____6[0U] = (uint8_t)0U;
      uu____6[1U] = (uint8_t)1U;
      uint8_t *uu____7 = suite_id + (uint32_t)8U;
      uu____7[0U] = (uint8_t)0U;
      uu____7[1U] = (uint8_t)3U;
      uint8_t
      label_psk_id_hash[11U] =
        {
          (uint8_t)0x70U, (uint8_t)0x73U, (uint8_t)0x6bU, (uint8_t)0x5fU, (uint8_t)0x69U,
          (uint8_t)0x64U, (uint8_t)0x5fU, (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x73U,
          (uint8_t)0x68U
        };
      uint8_t o_psk_id_hash[32U] = { 0U };
      uint8_t *empty = suite_id;
      uint32_t len0 = (uint32_t)28U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len0);
      uint8_t tmp1[len0];
      memset(tmp1, 0U, len0 * sizeof (uint8_t));
      uint8_t *uu____8 = tmp1;
      uu____8[0U] = (uint8_t)0x48U;
      uu____8[1U] = (uint8_t)0x50U;
      uu____8[2U] = (uint8_t)0x4bU;
      uu____8[3U] = (uint8_t)0x45U;
      uu____8[4U] = (uint8_t)0x2dU;
      uu____8[5U] = (uint8_t)0x76U;
      uu____8[6U] = (uint8_t)0x31U;
      memcpy(tmp1 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
      memcpy(tmp1 + (uint32_t)17U, label_psk_id_hash, (uint32_t)11U * sizeof (uint8_t));
      memcpy(tmp1 + (uint32_t)28U, empty, (uint32_t)0U * sizeof (uint8_t));
      Hacl_HKDF_extract_sha2_256(o_psk_id_hash, empty, (uint32_t)0U, tmp1, len0);
      uint8_t
      label_info_hash[9U] =
        {
          (uint8_t)0x69U, (uint8_t)0x6eU, (uint8_t)0x66U, (uint8_t)0x6fU, (uint8_t)0x5fU,
          (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x73U, (uint8_t)0x68U
        };
      uint8_t o_info_hash[32U] = { 0U };
      uint32_t len1 = (uint32_t)26U + infolen;
      KRML_CHECK_SIZE(sizeof (uint8_t), len1);
      uint8_t tmp2[len1];
      memset(tmp2, 0U, len1 * sizeof (uint8_t));
      uint8_t *uu____9 = tmp2;
      uu____9[0U] = (uint8_t)0x48U;
      uu____9[1U] = (uint8_t)0x50U;
      uu____9[2U] = (uint8_t)0x4bU;
      uu____9[3U] = (uint8_t)0x45U;
      uu____9[4U] = (uint8_t)0x2dU;
      uu____9[5U] = (uint8_t)0x76U;
      uu____9[6U] = (uint8_t)0x31U;
      memcpy(tmp2 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
      memcpy(tmp2 + (uint32_t)17U, label_info_hash, (uint32_t)9U * sizeof (uint8_t));
      memcpy(tmp2 + (uint32_t)26U, info, infolen * sizeof (uint8_t));
      Hacl_HKDF_extract_sha2_256(o_info_hash, empty, (uint32_t)0U, tmp2, len1);
      o_context[0U] = (uint8_t)0U;
      memcpy(o_context + (uint32_t)1U, o_psk_id_hash, (uint32_t)32U * sizeof (uint8_t));
      memcpy(o_context + (uint32_t)33U, o_info_hash, (uint32_t)32U * sizeof (uint8_t));
      uint8_t
      label_secret[6U] =
        {
          (uint8_t)0x73U, (uint8_t)0x65U, (uint8_t)0x63U, (uint8_t)0x72U, (uint8_t)0x65U,
          (uint8_t)0x74U
        };
      uint32_t len2 = (uint32_t)23U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len2);
      uint8_t tmp3[len2];
      memset(tmp3, 0U, len2 * sizeof (uint8_t));
      uint8_t *uu____10 = tmp3;
      uu____10[0U] = (uint8_t)0x48U;
      uu____10[1U] = (uint8_t)0x50U;
      uu____10[2U] = (uint8_t)0x4bU;
      uu____10[3U] = (uint8_t)0x45U;
      uu____10[4U] = (uint8_t)0x2dU;
      uu____10[5U] = (uint8_t)0x76U;
      uu____10[6U] = (uint8_t)0x31U;
      memcpy(tmp3 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
      memcpy(tmp3 + (uint32_t)17U, label_secret, (uint32_t)6U * sizeof (uint8_t));
      memcpy(tmp3 + (uint32_t)23U, empty, (uint32_t)0U * sizeof (uint8_t));
      Hacl_HKDF_extract_sha2_256(o_secret, shared, (uint32_t)32U, tmp3, len2);
      uint8_t label_exp[3U] = { (uint8_t)0x65U, (uint8_t)0x78U, (uint8_t)0x70U };
      uint32_t len3 = (uint32_t)87U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len3);
      uint8_t tmp4[len3];
      memset(tmp4, 0U, len3 * sizeof (uint8_t));
      store16_be(tmp4, (uint16_t)(uint32_t)32U);
      uint8_t *uu____11 = tmp4 + (uint32_t)2U;
      uu____11[0U] = (uint8_t)0x48U;
      uu____11[1U] = (uint8_t)0x50U;
      uu____11[2U] = (uint8_t)0x4bU;
      uu____11[3U] = (uint8_t)0x45U;
      uu____11[4U] = (uint8_t)0x2dU;
      uu____11[5U] = (uint8_t)0x76U;
      uu____11[6U] = (uint8_t)0x31U;
      memcpy(tmp4 + (uint32_t)9U, suite_id, (uint32_t)10U * sizeof (uint8_t));
      memcpy(tmp4 + (uint32_t)19U, label_exp, (uint32_t)3U * sizeof (uint8_t));
      memcpy(tmp4 + (uint32_t)22U, o_context, (uint32_t)65U * sizeof (uint8_t));
      Hacl_HKDF_expand_sha2_256(o_ctx.ctx_exporter,
        o_secret,
        (uint32_t)32U,
        tmp4,
        len3,
        (uint32_t)32U);
      uint8_t label_key[3U] = { (uint8_t)0x6bU, (uint8_t)0x65U, (uint8_t)0x79U };
      uint32_t len4 = (uint32_t)87U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len4);
      uint8_t tmp5[len4];
      memset(tmp5, 0U, len4 * sizeof (uint8_t));
      store16_be(tmp5, (uint16_t)(uint32_t)32U);
      uint8_t *uu____12 = tmp5 + (uint32_t)2U;
      uu____12[0U] = (uint8_t)0x48U;
      uu____12[1U] = (uint8_t)0x50U;
      uu____12[2U] = (uint8_t)0x4bU;
      uu____12[3U] = (uint8_t)0x45U;
      uu____12[4U] = (uint8_t)0x2dU;
      uu____12[5U] = (uint8_t)0x76U;
      uu____12[6U] = (uint8_t)0x31U;
      memcpy(tmp5 + (uint32_t)9U, suite_id, (uint32_t)10U * sizeof (uint8_t));
      memcpy(tmp5 + (uint32_t)19U, label_key, (uint32_t)3U * sizeof (uint8_t));
      memcpy(tmp5 + (uint32_t)22U, o_context, (uint32_t)65U * sizeof (uint8_t));
      Hacl_HKDF_expand_sha2_256(o_ctx.ctx_key, o_secret, (uint32_t)32U, tmp5, len4, (uint32_t)32U);
      uint8_t
      label_base_nonce[10U] =
        {
          (uint8_t)0x62U, (uint8_t)0x61U, (uint8_t)0x73U, (uint8_t)0x65U, (uint8_t)0x5fU,
          (uint8_t)0x6eU, (uint8_t)0x6fU, (uint8_t)0x6eU, (uint8_t)0x63U, (uint8_t)0x65U
        };
      uint32_t len = (uint32_t)94U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len);
      uint8_t tmp[len];
      memset(tmp, 0U, len * sizeof (uint8_t));
      store16_be(tmp, (uint16_t)(uint32_t)12U);
      uint8_t *uu____13 = tmp + (uint32_t)2U;
      uu____13[0U] = (uint8_t)0x48U;
      uu____13[1U] = (uint8_t)0x50U;
      uu____13[2U] = (uint8_t)0x4bU;
      uu____13[3U] = (uint8_t)0x45U;
      uu____13[4U] = (uint8_t)0x2dU;
      uu____13[5U] = (uint8_t)0x76U;
      uu____13[6U] = (uint8_t)0x31U;
      memcpy(tmp + (uint32_t)9U, suite_id, (uint32_t)10U * sizeof (uint8_t));
      memcpy(tmp + (uint32_t)19U, label_base_nonce, (uint32_t)10U * sizeof (uint8_t));
      memcpy(tmp + (uint32_t)29U, o_context, (uint32_t)65U * sizeof (uint8_t));
      Hacl_HKDF_expand_sha2_256(o_ctx.ctx_nonce, o_secret, (uint32_t)32U, tmp, len, (uint32_t)12U);
      o_ctx.ctx_seq[0U] = (uint64_t)0U;
      return (uint32_t)0U;
    }
    return (uint32_t)1U;
  }
  return (uint32_t)1U;
}

/* SNIPPET_END: Hacl_HPKE_P256_CP32_SHA256_setupBaseR */

/* SNIPPET_START: Hacl_HPKE_P256_CP32_SHA256_sealBase */

uint32_t
Hacl_HPKE_P256_CP32_SHA256_sealBase(
  uint8_t *skE,
  uint8_t *pkR,
  uint32_t infolen,
  uint8_t *info,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t plainlen,
  uint8_t *plain,
  uint8_t *o_enc,
  uint8_t *o_ct
)
{
  uint8_t ctx_key[32U] = { 0U };
  uint8_t ctx_nonce[12U] = { 0U };
  uint64_t ctx_seq = (uint64_t)0U;
  uint8_t ctx_exporter[32U] = { 0U };
  Hacl_Impl_HPKE_context_s
  o_ctx =
    {
      .ctx_key = ctx_key,
      .ctx_nonce = ctx_nonce,
      .ctx_seq = &ctx_seq,
      .ctx_exporter = ctx_exporter
    };
  uint32_t res = Hacl_HPKE_P256_CP32_SHA256_setupBaseS(o_enc, o_ctx, skE, pkR, infolen, info);
  if (res == (uint32_t)0U)
  {
    uint8_t nonce[12U] = { 0U };
    uint64_t s = o_ctx.ctx_seq[0U];
    uint8_t enc[12U] = { 0U };
    store64_be(enc + (uint32_t)4U, s);
    KRML_MAYBE_FOR12(i,
      (uint32_t)0U,
      (uint32_t)12U,
      (uint32_t)1U,
      uint8_t xi = enc[i];
      uint8_t yi = o_ctx.ctx_nonce[i];
      nonce[i] = xi ^ yi;);
    Hacl_Chacha20Poly1305_32_aead_encrypt(o_ctx.ctx_key,
      nonce,
      aadlen,
      aad,
      plainlen,
      plain,
      o_ct,
      o_ct + plainlen);
    uint64_t s1 = o_ctx.ctx_seq[0U];
    uint32_t res1;
    if (s1 == (uint64_t)18446744073709551615U)
    {
      res1 = (uint32_t)1U;
    }
    else
    {
      uint64_t s_ = s1 + (uint64_t)1U;
      o_ctx.ctx_seq[0U] = s_;
      res1 = (uint32_t)0U;
    }
    uint32_t res10 = res1;
    return res10;
  }
  return (uint32_t)1U;
}

/* SNIPPET_END: Hacl_HPKE_P256_CP32_SHA256_sealBase */

/* SNIPPET_START: Hacl_HPKE_P256_CP32_SHA256_openBase */

uint32_t
Hacl_HPKE_P256_CP32_SHA256_openBase(
  uint8_t *pkE,
  uint8_t *skR,
  uint32_t infolen,
  uint8_t *info,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t ctlen,
  uint8_t *ct,
  uint8_t *o_pt
)
{
  uint8_t ctx_key[32U] = { 0U };
  uint8_t ctx_nonce[12U] = { 0U };
  uint64_t ctx_seq = (uint64_t)0U;
  uint8_t ctx_exporter[32U] = { 0U };
  Hacl_Impl_HPKE_context_s
  o_ctx =
    {
      .ctx_key = ctx_key,
      .ctx_nonce = ctx_nonce,
      .ctx_seq = &ctx_seq,
      .ctx_exporter = ctx_exporter
    };
  uint32_t res = Hacl_HPKE_P256_CP32_SHA256_setupBaseR(o_ctx, pkE, skR, infolen, info);
  if (res == (uint32_t)0U)
  {
    uint8_t nonce[12U] = { 0U };
    uint64_t s = o_ctx.ctx_seq[0U];
    uint8_t enc[12U] = { 0U };
    store64_be(enc + (uint32_t)4U, s);
    KRML_MAYBE_FOR12(i,
      (uint32_t)0U,
      (uint32_t)12U,
      (uint32_t)1U,
      uint8_t xi = enc[i];
      uint8_t yi = o_ctx.ctx_nonce[i];
      nonce[i] = xi ^ yi;);
    uint32_t
    res1 =
      Hacl_Chacha20Poly1305_32_aead_decrypt(o_ctx.ctx_key,
        nonce,
        aadlen,
        aad,
        ctlen - (uint32_t)16U,
        o_pt,
        ct,
        ct + ctlen - (uint32_t)16U);
    if (res1 == (uint32_t)0U)
    {
      uint64_t s1 = o_ctx.ctx_seq[0U];
      if (s1 == (uint64_t)18446744073709551615U)
      {
        return (uint32_t)1U;
      }
      uint64_t s_ = s1 + (uint64_t)1U;
      o_ctx.ctx_seq[0U] = s_;
      return (uint32_t)0U;
    }
    return (uint32_t)1U;
  }
  return (uint32_t)1U;
}

/* SNIPPET_END: Hacl_HPKE_P256_CP32_SHA256_openBase */

