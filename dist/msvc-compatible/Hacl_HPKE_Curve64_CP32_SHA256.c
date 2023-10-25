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


#include "Hacl_HPKE_Curve64_CP32_SHA256.h"

#include "internal/Hacl_Krmllib.h"

uint32_t
Hacl_HPKE_Curve64_CP32_SHA256_setupBaseS(
  uint8_t *o_pkE,
  Hacl_Impl_HPKE_context_s o_ctx,
  uint8_t *skE,
  uint8_t *pkR,
  uint32_t infolen,
  uint8_t *info
)
{
  uint8_t o_shared[32U] = { 0U };
  uint8_t *o_pkE1 = o_pkE;
  Hacl_Curve25519_64_secret_to_public(o_pkE1, skE);
  uint32_t res1 = 0U;
  uint32_t res0;
  if (res1 == 0U)
  {
    uint8_t o_dh[32U] = { 0U };
    uint8_t zeros[32U] = { 0U };
    Hacl_Curve25519_64_scalarmult(o_dh, skE, pkR);
    uint8_t res2 = 255U;
    for (uint32_t i = 0U; i < 32U; i++)
    {
      uint8_t uu____0 = FStar_UInt8_eq_mask(o_dh[i], zeros[i]);
      res2 = (uint32_t)uu____0 & (uint32_t)res2;
    }
    uint8_t z = res2;
    uint32_t res;
    if (z == 255U)
    {
      res = 1U;
    }
    else
    {
      res = 0U;
    }
    uint32_t res20 = res;
    uint8_t o_kemcontext[64U] = { 0U };
    if (res20 == 0U)
    {
      memcpy(o_kemcontext, o_pkE, 32U * sizeof (uint8_t));
      uint8_t *o_pkRm = o_kemcontext + 32U;
      uint8_t *o_pkR = o_pkRm;
      memcpy(o_pkR, pkR, 32U * sizeof (uint8_t));
      uint8_t *o_dhm = o_dh;
      uint8_t o_eae_prk[32U] = { 0U };
      uint8_t suite_id_kem[5U] = { 0U };
      uint8_t *uu____1 = suite_id_kem;
      uu____1[0U] = 0x4bU;
      uu____1[1U] = 0x45U;
      uu____1[2U] = 0x4dU;
      uint8_t *uu____2 = suite_id_kem + 3U;
      uu____2[0U] = 0U;
      uu____2[1U] = 32U;
      uint8_t *empty = suite_id_kem;
      uint8_t label_eae_prk[7U] = { 0x65U, 0x61U, 0x65U, 0x5fU, 0x70U, 0x72U, 0x6bU };
      uint32_t len0 = 51U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len0);
      uint8_t *tmp0 = (uint8_t *)alloca(len0 * sizeof (uint8_t));
      memset(tmp0, 0U, len0 * sizeof (uint8_t));
      uint8_t *uu____3 = tmp0;
      uu____3[0U] = 0x48U;
      uu____3[1U] = 0x50U;
      uu____3[2U] = 0x4bU;
      uu____3[3U] = 0x45U;
      uu____3[4U] = 0x2dU;
      uu____3[5U] = 0x76U;
      uu____3[6U] = 0x31U;
      memcpy(tmp0 + 7U, suite_id_kem, 5U * sizeof (uint8_t));
      memcpy(tmp0 + 12U, label_eae_prk, 7U * sizeof (uint8_t));
      memcpy(tmp0 + 19U, o_dhm, 32U * sizeof (uint8_t));
      Hacl_HKDF_extract_sha2_256(o_eae_prk, empty, 0U, tmp0, len0);
      uint8_t
      label_shared_secret[13U] =
        {
          0x73U, 0x68U, 0x61U, 0x72U, 0x65U, 0x64U, 0x5fU, 0x73U, 0x65U, 0x63U, 0x72U, 0x65U, 0x74U
        };
      uint32_t len = 91U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len);
      uint8_t *tmp = (uint8_t *)alloca(len * sizeof (uint8_t));
      memset(tmp, 0U, len * sizeof (uint8_t));
      store16_be(tmp, (uint16_t)32U);
      uint8_t *uu____4 = tmp + 2U;
      uu____4[0U] = 0x48U;
      uu____4[1U] = 0x50U;
      uu____4[2U] = 0x4bU;
      uu____4[3U] = 0x45U;
      uu____4[4U] = 0x2dU;
      uu____4[5U] = 0x76U;
      uu____4[6U] = 0x31U;
      memcpy(tmp + 9U, suite_id_kem, 5U * sizeof (uint8_t));
      memcpy(tmp + 14U, label_shared_secret, 13U * sizeof (uint8_t));
      memcpy(tmp + 27U, o_kemcontext, 64U * sizeof (uint8_t));
      Hacl_HKDF_expand_sha2_256(o_shared, o_eae_prk, 32U, tmp, len, 32U);
      res0 = 0U;
    }
    else
    {
      res0 = 1U;
    }
  }
  else
  {
    res0 = 1U;
  }
  if (res0 == 0U)
  {
    uint8_t o_context[65U] = { 0U };
    uint8_t o_secret[32U] = { 0U };
    uint8_t suite_id[10U] = { 0U };
    uint8_t *uu____5 = suite_id;
    uu____5[0U] = 0x48U;
    uu____5[1U] = 0x50U;
    uu____5[2U] = 0x4bU;
    uu____5[3U] = 0x45U;
    uint8_t *uu____6 = suite_id + 4U;
    uu____6[0U] = 0U;
    uu____6[1U] = 32U;
    uint8_t *uu____7 = suite_id + 6U;
    uu____7[0U] = 0U;
    uu____7[1U] = 1U;
    uint8_t *uu____8 = suite_id + 8U;
    uu____8[0U] = 0U;
    uu____8[1U] = 3U;
    uint8_t
    label_psk_id_hash[11U] =
      { 0x70U, 0x73U, 0x6bU, 0x5fU, 0x69U, 0x64U, 0x5fU, 0x68U, 0x61U, 0x73U, 0x68U };
    uint8_t o_psk_id_hash[32U] = { 0U };
    uint8_t *empty = suite_id;
    uint32_t len0 = 28U;
    KRML_CHECK_SIZE(sizeof (uint8_t), len0);
    uint8_t *tmp0 = (uint8_t *)alloca(len0 * sizeof (uint8_t));
    memset(tmp0, 0U, len0 * sizeof (uint8_t));
    uint8_t *uu____9 = tmp0;
    uu____9[0U] = 0x48U;
    uu____9[1U] = 0x50U;
    uu____9[2U] = 0x4bU;
    uu____9[3U] = 0x45U;
    uu____9[4U] = 0x2dU;
    uu____9[5U] = 0x76U;
    uu____9[6U] = 0x31U;
    memcpy(tmp0 + 7U, suite_id, 10U * sizeof (uint8_t));
    memcpy(tmp0 + 17U, label_psk_id_hash, 11U * sizeof (uint8_t));
    memcpy(tmp0 + 28U, empty, 0U * sizeof (uint8_t));
    Hacl_HKDF_extract_sha2_256(o_psk_id_hash, empty, 0U, tmp0, len0);
    uint8_t
    label_info_hash[9U] = { 0x69U, 0x6eU, 0x66U, 0x6fU, 0x5fU, 0x68U, 0x61U, 0x73U, 0x68U };
    uint8_t o_info_hash[32U] = { 0U };
    uint32_t len1 = 26U + infolen;
    KRML_CHECK_SIZE(sizeof (uint8_t), len1);
    uint8_t *tmp1 = (uint8_t *)alloca(len1 * sizeof (uint8_t));
    memset(tmp1, 0U, len1 * sizeof (uint8_t));
    uint8_t *uu____10 = tmp1;
    uu____10[0U] = 0x48U;
    uu____10[1U] = 0x50U;
    uu____10[2U] = 0x4bU;
    uu____10[3U] = 0x45U;
    uu____10[4U] = 0x2dU;
    uu____10[5U] = 0x76U;
    uu____10[6U] = 0x31U;
    memcpy(tmp1 + 7U, suite_id, 10U * sizeof (uint8_t));
    memcpy(tmp1 + 17U, label_info_hash, 9U * sizeof (uint8_t));
    memcpy(tmp1 + 26U, info, infolen * sizeof (uint8_t));
    Hacl_HKDF_extract_sha2_256(o_info_hash, empty, 0U, tmp1, len1);
    o_context[0U] = 0U;
    memcpy(o_context + 1U, o_psk_id_hash, 32U * sizeof (uint8_t));
    memcpy(o_context + 33U, o_info_hash, 32U * sizeof (uint8_t));
    uint8_t label_secret[6U] = { 0x73U, 0x65U, 0x63U, 0x72U, 0x65U, 0x74U };
    uint32_t len2 = 23U;
    KRML_CHECK_SIZE(sizeof (uint8_t), len2);
    uint8_t *tmp2 = (uint8_t *)alloca(len2 * sizeof (uint8_t));
    memset(tmp2, 0U, len2 * sizeof (uint8_t));
    uint8_t *uu____11 = tmp2;
    uu____11[0U] = 0x48U;
    uu____11[1U] = 0x50U;
    uu____11[2U] = 0x4bU;
    uu____11[3U] = 0x45U;
    uu____11[4U] = 0x2dU;
    uu____11[5U] = 0x76U;
    uu____11[6U] = 0x31U;
    memcpy(tmp2 + 7U, suite_id, 10U * sizeof (uint8_t));
    memcpy(tmp2 + 17U, label_secret, 6U * sizeof (uint8_t));
    memcpy(tmp2 + 23U, empty, 0U * sizeof (uint8_t));
    Hacl_HKDF_extract_sha2_256(o_secret, o_shared, 32U, tmp2, len2);
    uint8_t label_exp[3U] = { 0x65U, 0x78U, 0x70U };
    uint32_t len3 = 87U;
    KRML_CHECK_SIZE(sizeof (uint8_t), len3);
    uint8_t *tmp3 = (uint8_t *)alloca(len3 * sizeof (uint8_t));
    memset(tmp3, 0U, len3 * sizeof (uint8_t));
    store16_be(tmp3, (uint16_t)32U);
    uint8_t *uu____12 = tmp3 + 2U;
    uu____12[0U] = 0x48U;
    uu____12[1U] = 0x50U;
    uu____12[2U] = 0x4bU;
    uu____12[3U] = 0x45U;
    uu____12[4U] = 0x2dU;
    uu____12[5U] = 0x76U;
    uu____12[6U] = 0x31U;
    memcpy(tmp3 + 9U, suite_id, 10U * sizeof (uint8_t));
    memcpy(tmp3 + 19U, label_exp, 3U * sizeof (uint8_t));
    memcpy(tmp3 + 22U, o_context, 65U * sizeof (uint8_t));
    Hacl_HKDF_expand_sha2_256(o_ctx.ctx_exporter, o_secret, 32U, tmp3, len3, 32U);
    uint8_t label_key[3U] = { 0x6bU, 0x65U, 0x79U };
    uint32_t len4 = 87U;
    KRML_CHECK_SIZE(sizeof (uint8_t), len4);
    uint8_t *tmp4 = (uint8_t *)alloca(len4 * sizeof (uint8_t));
    memset(tmp4, 0U, len4 * sizeof (uint8_t));
    store16_be(tmp4, (uint16_t)32U);
    uint8_t *uu____13 = tmp4 + 2U;
    uu____13[0U] = 0x48U;
    uu____13[1U] = 0x50U;
    uu____13[2U] = 0x4bU;
    uu____13[3U] = 0x45U;
    uu____13[4U] = 0x2dU;
    uu____13[5U] = 0x76U;
    uu____13[6U] = 0x31U;
    memcpy(tmp4 + 9U, suite_id, 10U * sizeof (uint8_t));
    memcpy(tmp4 + 19U, label_key, 3U * sizeof (uint8_t));
    memcpy(tmp4 + 22U, o_context, 65U * sizeof (uint8_t));
    Hacl_HKDF_expand_sha2_256(o_ctx.ctx_key, o_secret, 32U, tmp4, len4, 32U);
    uint8_t
    label_base_nonce[10U] =
      { 0x62U, 0x61U, 0x73U, 0x65U, 0x5fU, 0x6eU, 0x6fU, 0x6eU, 0x63U, 0x65U };
    uint32_t len = 94U;
    KRML_CHECK_SIZE(sizeof (uint8_t), len);
    uint8_t *tmp = (uint8_t *)alloca(len * sizeof (uint8_t));
    memset(tmp, 0U, len * sizeof (uint8_t));
    store16_be(tmp, (uint16_t)12U);
    uint8_t *uu____14 = tmp + 2U;
    uu____14[0U] = 0x48U;
    uu____14[1U] = 0x50U;
    uu____14[2U] = 0x4bU;
    uu____14[3U] = 0x45U;
    uu____14[4U] = 0x2dU;
    uu____14[5U] = 0x76U;
    uu____14[6U] = 0x31U;
    memcpy(tmp + 9U, suite_id, 10U * sizeof (uint8_t));
    memcpy(tmp + 19U, label_base_nonce, 10U * sizeof (uint8_t));
    memcpy(tmp + 29U, o_context, 65U * sizeof (uint8_t));
    Hacl_HKDF_expand_sha2_256(o_ctx.ctx_nonce, o_secret, 32U, tmp, len, 12U);
    o_ctx.ctx_seq[0U] = 0ULL;
    return res0;
  }
  return res0;
}

uint32_t
Hacl_HPKE_Curve64_CP32_SHA256_setupBaseR(
  Hacl_Impl_HPKE_context_s o_ctx,
  uint8_t *enc,
  uint8_t *skR,
  uint32_t infolen,
  uint8_t *info
)
{
  uint8_t pkR[32U] = { 0U };
  Hacl_Curve25519_64_secret_to_public(pkR, skR);
  uint32_t res1 = 0U;
  uint8_t shared[32U] = { 0U };
  if (res1 == 0U)
  {
    uint8_t *pkE = enc;
    uint8_t dh[32U] = { 0U };
    uint8_t zeros[32U] = { 0U };
    Hacl_Curve25519_64_scalarmult(dh, skR, pkE);
    uint8_t res0 = 255U;
    for (uint32_t i = 0U; i < 32U; i++)
    {
      uint8_t uu____0 = FStar_UInt8_eq_mask(dh[i], zeros[i]);
      res0 = (uint32_t)uu____0 & (uint32_t)res0;
    }
    uint8_t z = res0;
    uint32_t res;
    if (z == 255U)
    {
      res = 1U;
    }
    else
    {
      res = 0U;
    }
    uint32_t res11 = res;
    uint32_t res2;
    uint8_t kemcontext[64U] = { 0U };
    if (res11 == 0U)
    {
      uint8_t *pkRm = kemcontext + 32U;
      uint8_t *pkR1 = pkRm;
      Hacl_Curve25519_64_secret_to_public(pkR1, skR);
      uint32_t res20 = 0U;
      if (res20 == 0U)
      {
        memcpy(kemcontext, enc, 32U * sizeof (uint8_t));
        uint8_t *dhm = dh;
        uint8_t o_eae_prk[32U] = { 0U };
        uint8_t suite_id_kem[5U] = { 0U };
        uint8_t *uu____1 = suite_id_kem;
        uu____1[0U] = 0x4bU;
        uu____1[1U] = 0x45U;
        uu____1[2U] = 0x4dU;
        uint8_t *uu____2 = suite_id_kem + 3U;
        uu____2[0U] = 0U;
        uu____2[1U] = 32U;
        uint8_t *empty = suite_id_kem;
        uint8_t label_eae_prk[7U] = { 0x65U, 0x61U, 0x65U, 0x5fU, 0x70U, 0x72U, 0x6bU };
        uint32_t len0 = 51U;
        KRML_CHECK_SIZE(sizeof (uint8_t), len0);
        uint8_t *tmp0 = (uint8_t *)alloca(len0 * sizeof (uint8_t));
        memset(tmp0, 0U, len0 * sizeof (uint8_t));
        uint8_t *uu____3 = tmp0;
        uu____3[0U] = 0x48U;
        uu____3[1U] = 0x50U;
        uu____3[2U] = 0x4bU;
        uu____3[3U] = 0x45U;
        uu____3[4U] = 0x2dU;
        uu____3[5U] = 0x76U;
        uu____3[6U] = 0x31U;
        memcpy(tmp0 + 7U, suite_id_kem, 5U * sizeof (uint8_t));
        memcpy(tmp0 + 12U, label_eae_prk, 7U * sizeof (uint8_t));
        memcpy(tmp0 + 19U, dhm, 32U * sizeof (uint8_t));
        Hacl_HKDF_extract_sha2_256(o_eae_prk, empty, 0U, tmp0, len0);
        uint8_t
        label_shared_secret[13U] =
          {
            0x73U, 0x68U, 0x61U, 0x72U, 0x65U, 0x64U, 0x5fU, 0x73U, 0x65U, 0x63U, 0x72U, 0x65U,
            0x74U
          };
        uint32_t len = 91U;
        KRML_CHECK_SIZE(sizeof (uint8_t), len);
        uint8_t *tmp = (uint8_t *)alloca(len * sizeof (uint8_t));
        memset(tmp, 0U, len * sizeof (uint8_t));
        store16_be(tmp, (uint16_t)32U);
        uint8_t *uu____4 = tmp + 2U;
        uu____4[0U] = 0x48U;
        uu____4[1U] = 0x50U;
        uu____4[2U] = 0x4bU;
        uu____4[3U] = 0x45U;
        uu____4[4U] = 0x2dU;
        uu____4[5U] = 0x76U;
        uu____4[6U] = 0x31U;
        memcpy(tmp + 9U, suite_id_kem, 5U * sizeof (uint8_t));
        memcpy(tmp + 14U, label_shared_secret, 13U * sizeof (uint8_t));
        memcpy(tmp + 27U, kemcontext, 64U * sizeof (uint8_t));
        Hacl_HKDF_expand_sha2_256(shared, o_eae_prk, 32U, tmp, len, 32U);
        res2 = 0U;
      }
      else
      {
        res2 = 1U;
      }
    }
    else
    {
      res2 = 1U;
    }
    if (res2 == 0U)
    {
      uint8_t o_context[65U] = { 0U };
      uint8_t o_secret[32U] = { 0U };
      uint8_t suite_id[10U] = { 0U };
      uint8_t *uu____5 = suite_id;
      uu____5[0U] = 0x48U;
      uu____5[1U] = 0x50U;
      uu____5[2U] = 0x4bU;
      uu____5[3U] = 0x45U;
      uint8_t *uu____6 = suite_id + 4U;
      uu____6[0U] = 0U;
      uu____6[1U] = 32U;
      uint8_t *uu____7 = suite_id + 6U;
      uu____7[0U] = 0U;
      uu____7[1U] = 1U;
      uint8_t *uu____8 = suite_id + 8U;
      uu____8[0U] = 0U;
      uu____8[1U] = 3U;
      uint8_t
      label_psk_id_hash[11U] =
        { 0x70U, 0x73U, 0x6bU, 0x5fU, 0x69U, 0x64U, 0x5fU, 0x68U, 0x61U, 0x73U, 0x68U };
      uint8_t o_psk_id_hash[32U] = { 0U };
      uint8_t *empty = suite_id;
      uint32_t len0 = 28U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len0);
      uint8_t *tmp0 = (uint8_t *)alloca(len0 * sizeof (uint8_t));
      memset(tmp0, 0U, len0 * sizeof (uint8_t));
      uint8_t *uu____9 = tmp0;
      uu____9[0U] = 0x48U;
      uu____9[1U] = 0x50U;
      uu____9[2U] = 0x4bU;
      uu____9[3U] = 0x45U;
      uu____9[4U] = 0x2dU;
      uu____9[5U] = 0x76U;
      uu____9[6U] = 0x31U;
      memcpy(tmp0 + 7U, suite_id, 10U * sizeof (uint8_t));
      memcpy(tmp0 + 17U, label_psk_id_hash, 11U * sizeof (uint8_t));
      memcpy(tmp0 + 28U, empty, 0U * sizeof (uint8_t));
      Hacl_HKDF_extract_sha2_256(o_psk_id_hash, empty, 0U, tmp0, len0);
      uint8_t
      label_info_hash[9U] = { 0x69U, 0x6eU, 0x66U, 0x6fU, 0x5fU, 0x68U, 0x61U, 0x73U, 0x68U };
      uint8_t o_info_hash[32U] = { 0U };
      uint32_t len1 = 26U + infolen;
      KRML_CHECK_SIZE(sizeof (uint8_t), len1);
      uint8_t *tmp1 = (uint8_t *)alloca(len1 * sizeof (uint8_t));
      memset(tmp1, 0U, len1 * sizeof (uint8_t));
      uint8_t *uu____10 = tmp1;
      uu____10[0U] = 0x48U;
      uu____10[1U] = 0x50U;
      uu____10[2U] = 0x4bU;
      uu____10[3U] = 0x45U;
      uu____10[4U] = 0x2dU;
      uu____10[5U] = 0x76U;
      uu____10[6U] = 0x31U;
      memcpy(tmp1 + 7U, suite_id, 10U * sizeof (uint8_t));
      memcpy(tmp1 + 17U, label_info_hash, 9U * sizeof (uint8_t));
      memcpy(tmp1 + 26U, info, infolen * sizeof (uint8_t));
      Hacl_HKDF_extract_sha2_256(o_info_hash, empty, 0U, tmp1, len1);
      o_context[0U] = 0U;
      memcpy(o_context + 1U, o_psk_id_hash, 32U * sizeof (uint8_t));
      memcpy(o_context + 33U, o_info_hash, 32U * sizeof (uint8_t));
      uint8_t label_secret[6U] = { 0x73U, 0x65U, 0x63U, 0x72U, 0x65U, 0x74U };
      uint32_t len2 = 23U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len2);
      uint8_t *tmp2 = (uint8_t *)alloca(len2 * sizeof (uint8_t));
      memset(tmp2, 0U, len2 * sizeof (uint8_t));
      uint8_t *uu____11 = tmp2;
      uu____11[0U] = 0x48U;
      uu____11[1U] = 0x50U;
      uu____11[2U] = 0x4bU;
      uu____11[3U] = 0x45U;
      uu____11[4U] = 0x2dU;
      uu____11[5U] = 0x76U;
      uu____11[6U] = 0x31U;
      memcpy(tmp2 + 7U, suite_id, 10U * sizeof (uint8_t));
      memcpy(tmp2 + 17U, label_secret, 6U * sizeof (uint8_t));
      memcpy(tmp2 + 23U, empty, 0U * sizeof (uint8_t));
      Hacl_HKDF_extract_sha2_256(o_secret, shared, 32U, tmp2, len2);
      uint8_t label_exp[3U] = { 0x65U, 0x78U, 0x70U };
      uint32_t len3 = 87U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len3);
      uint8_t *tmp3 = (uint8_t *)alloca(len3 * sizeof (uint8_t));
      memset(tmp3, 0U, len3 * sizeof (uint8_t));
      store16_be(tmp3, (uint16_t)32U);
      uint8_t *uu____12 = tmp3 + 2U;
      uu____12[0U] = 0x48U;
      uu____12[1U] = 0x50U;
      uu____12[2U] = 0x4bU;
      uu____12[3U] = 0x45U;
      uu____12[4U] = 0x2dU;
      uu____12[5U] = 0x76U;
      uu____12[6U] = 0x31U;
      memcpy(tmp3 + 9U, suite_id, 10U * sizeof (uint8_t));
      memcpy(tmp3 + 19U, label_exp, 3U * sizeof (uint8_t));
      memcpy(tmp3 + 22U, o_context, 65U * sizeof (uint8_t));
      Hacl_HKDF_expand_sha2_256(o_ctx.ctx_exporter, o_secret, 32U, tmp3, len3, 32U);
      uint8_t label_key[3U] = { 0x6bU, 0x65U, 0x79U };
      uint32_t len4 = 87U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len4);
      uint8_t *tmp4 = (uint8_t *)alloca(len4 * sizeof (uint8_t));
      memset(tmp4, 0U, len4 * sizeof (uint8_t));
      store16_be(tmp4, (uint16_t)32U);
      uint8_t *uu____13 = tmp4 + 2U;
      uu____13[0U] = 0x48U;
      uu____13[1U] = 0x50U;
      uu____13[2U] = 0x4bU;
      uu____13[3U] = 0x45U;
      uu____13[4U] = 0x2dU;
      uu____13[5U] = 0x76U;
      uu____13[6U] = 0x31U;
      memcpy(tmp4 + 9U, suite_id, 10U * sizeof (uint8_t));
      memcpy(tmp4 + 19U, label_key, 3U * sizeof (uint8_t));
      memcpy(tmp4 + 22U, o_context, 65U * sizeof (uint8_t));
      Hacl_HKDF_expand_sha2_256(o_ctx.ctx_key, o_secret, 32U, tmp4, len4, 32U);
      uint8_t
      label_base_nonce[10U] =
        { 0x62U, 0x61U, 0x73U, 0x65U, 0x5fU, 0x6eU, 0x6fU, 0x6eU, 0x63U, 0x65U };
      uint32_t len = 94U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len);
      uint8_t *tmp = (uint8_t *)alloca(len * sizeof (uint8_t));
      memset(tmp, 0U, len * sizeof (uint8_t));
      store16_be(tmp, (uint16_t)12U);
      uint8_t *uu____14 = tmp + 2U;
      uu____14[0U] = 0x48U;
      uu____14[1U] = 0x50U;
      uu____14[2U] = 0x4bU;
      uu____14[3U] = 0x45U;
      uu____14[4U] = 0x2dU;
      uu____14[5U] = 0x76U;
      uu____14[6U] = 0x31U;
      memcpy(tmp + 9U, suite_id, 10U * sizeof (uint8_t));
      memcpy(tmp + 19U, label_base_nonce, 10U * sizeof (uint8_t));
      memcpy(tmp + 29U, o_context, 65U * sizeof (uint8_t));
      Hacl_HKDF_expand_sha2_256(o_ctx.ctx_nonce, o_secret, 32U, tmp, len, 12U);
      o_ctx.ctx_seq[0U] = 0ULL;
      return 0U;
    }
    return 1U;
  }
  return 1U;
}

uint32_t
Hacl_HPKE_Curve64_CP32_SHA256_sealBase(
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
  uint64_t ctx_seq = 0ULL;
  uint8_t ctx_exporter[32U] = { 0U };
  Hacl_Impl_HPKE_context_s
  o_ctx =
    {
      .ctx_key = ctx_key,
      .ctx_nonce = ctx_nonce,
      .ctx_seq = &ctx_seq,
      .ctx_exporter = ctx_exporter
    };
  uint32_t res = Hacl_HPKE_Curve64_CP32_SHA256_setupBaseS(o_enc, o_ctx, skE, pkR, infolen, info);
  if (res == 0U)
  {
    uint8_t nonce[12U] = { 0U };
    uint64_t s = o_ctx.ctx_seq[0U];
    uint8_t enc[12U] = { 0U };
    store64_be(enc + 4U, s);
    KRML_MAYBE_FOR12(i,
      0U,
      12U,
      1U,
      uint8_t xi = enc[i];
      uint8_t yi = o_ctx.ctx_nonce[i];
      nonce[i] = (uint32_t)xi ^ (uint32_t)yi;);
    uint8_t *cipher = o_ct;
    uint8_t *tag = o_ct + plainlen;
    Hacl_AEAD_Chacha20Poly1305_encrypt(cipher,
      tag,
      plain,
      plainlen,
      aad,
      aadlen,
      o_ctx.ctx_key,
      nonce);
    uint64_t s1 = o_ctx.ctx_seq[0U];
    uint32_t res1;
    if (s1 == 18446744073709551615ULL)
    {
      res1 = 1U;
    }
    else
    {
      uint64_t s_ = s1 + 1ULL;
      o_ctx.ctx_seq[0U] = s_;
      res1 = 0U;
    }
    uint32_t res10 = res1;
    return res10;
  }
  return 1U;
}

uint32_t
Hacl_HPKE_Curve64_CP32_SHA256_openBase(
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
  uint64_t ctx_seq = 0ULL;
  uint8_t ctx_exporter[32U] = { 0U };
  Hacl_Impl_HPKE_context_s
  o_ctx =
    {
      .ctx_key = ctx_key,
      .ctx_nonce = ctx_nonce,
      .ctx_seq = &ctx_seq,
      .ctx_exporter = ctx_exporter
    };
  uint32_t res = Hacl_HPKE_Curve64_CP32_SHA256_setupBaseR(o_ctx, pkE, skR, infolen, info);
  if (res == 0U)
  {
    uint8_t nonce[12U] = { 0U };
    uint64_t s = o_ctx.ctx_seq[0U];
    uint8_t enc[12U] = { 0U };
    store64_be(enc + 4U, s);
    KRML_MAYBE_FOR12(i,
      0U,
      12U,
      1U,
      uint8_t xi = enc[i];
      uint8_t yi = o_ctx.ctx_nonce[i];
      nonce[i] = (uint32_t)xi ^ (uint32_t)yi;);
    uint8_t *cipher = ct;
    uint8_t *tag = ct + ctlen - 16U;
    uint32_t
    res1 =
      Hacl_AEAD_Chacha20Poly1305_decrypt(o_pt,
        cipher,
        ctlen - 16U,
        aad,
        aadlen,
        o_ctx.ctx_key,
        nonce,
        tag);
    if (res1 == 0U)
    {
      uint64_t s1 = o_ctx.ctx_seq[0U];
      if (s1 == 18446744073709551615ULL)
      {
        return 1U;
      }
      uint64_t s_ = s1 + 1ULL;
      o_ctx.ctx_seq[0U] = s_;
      return 0U;
    }
    return 1U;
  }
  return 1U;
}

