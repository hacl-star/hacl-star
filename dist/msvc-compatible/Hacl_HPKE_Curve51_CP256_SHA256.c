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


#include "Hacl_HPKE_Curve51_CP256_SHA256.h"

#include "internal/Hacl_Krmllib.h"

uint32_t
Hacl_HPKE_Curve51_CP256_SHA256_setupBaseS(
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
  Hacl_Curve25519_51_secret_to_public(o_pkE1, skE);
  uint32_t res1 = (uint32_t)0U;
  uint32_t res0;
  if (res1 == (uint32_t)0U)
  {
    uint8_t o_dh[32U] = { 0U };
    uint8_t zeros[32U] = { 0U };
    Hacl_Curve25519_51_scalarmult(o_dh, skE, pkR);
    uint8_t res2 = (uint8_t)255U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
    {
      uint8_t uu____0 = FStar_UInt8_eq_mask(o_dh[i], zeros[i]);
      res2 = uu____0 & res2;
    }
    uint8_t z = res2;
    uint32_t res;
    if (z == (uint8_t)255U)
    {
      res = (uint32_t)1U;
    }
    else
    {
      res = (uint32_t)0U;
    }
    uint32_t res20 = res;
    uint8_t o_kemcontext[64U] = { 0U };
    if (res20 == (uint32_t)0U)
    {
      memcpy(o_kemcontext, o_pkE, (uint32_t)32U * sizeof (uint8_t));
      uint8_t *o_pkRm = o_kemcontext + (uint32_t)32U;
      uint8_t *o_pkR = o_pkRm;
      memcpy(o_pkR, pkR, (uint32_t)32U * sizeof (uint8_t));
      uint8_t *o_dhm = o_dh;
      uint8_t o_eae_prk[32U] = { 0U };
      uint8_t suite_id_kem[5U] = { 0U };
      uint8_t *uu____1 = suite_id_kem;
      uu____1[0U] = (uint8_t)0x4bU;
      uu____1[1U] = (uint8_t)0x45U;
      uu____1[2U] = (uint8_t)0x4dU;
      uint8_t *uu____2 = suite_id_kem + (uint32_t)3U;
      uu____2[0U] = (uint8_t)0U;
      uu____2[1U] = (uint8_t)32U;
      uint8_t *empty = suite_id_kem;
      uint8_t
      label_eae_prk[7U] =
        {
          (uint8_t)0x65U, (uint8_t)0x61U, (uint8_t)0x65U, (uint8_t)0x5fU, (uint8_t)0x70U,
          (uint8_t)0x72U, (uint8_t)0x6bU
        };
      uint32_t len0 = (uint32_t)7U + (uint32_t)5U + (uint32_t)7U + (uint32_t)32U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len0);
      uint8_t *tmp0 = alloca(len0 * sizeof (uint8_t));
      memset(tmp0, 0U, len0 * sizeof (uint8_t));
      uint8_t *uu____3 = tmp0;
      uu____3[0U] = (uint8_t)0x48U;
      uu____3[1U] = (uint8_t)0x50U;
      uu____3[2U] = (uint8_t)0x4bU;
      uu____3[3U] = (uint8_t)0x45U;
      uu____3[4U] = (uint8_t)0x2dU;
      uu____3[5U] = (uint8_t)0x76U;
      uu____3[6U] = (uint8_t)0x31U;
      memcpy(tmp0 + (uint32_t)7U, suite_id_kem, (uint32_t)5U * sizeof (uint8_t));
      memcpy(tmp0 + (uint32_t)7U + (uint32_t)5U, label_eae_prk, (uint32_t)7U * sizeof (uint8_t));
      memcpy(tmp0 + (uint32_t)7U + (uint32_t)5U + (uint32_t)7U,
        o_dhm,
        (uint32_t)32U * sizeof (uint8_t));
      Hacl_HKDF_extract_sha2_256(o_eae_prk, empty, (uint32_t)0U, tmp0, len0);
      uint8_t
      label_shared_secret[13U] =
        {
          (uint8_t)0x73U, (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x72U, (uint8_t)0x65U,
          (uint8_t)0x64U, (uint8_t)0x5fU, (uint8_t)0x73U, (uint8_t)0x65U, (uint8_t)0x63U,
          (uint8_t)0x72U, (uint8_t)0x65U, (uint8_t)0x74U
        };
      uint32_t len = (uint32_t)9U + (uint32_t)5U + (uint32_t)13U + (uint32_t)64U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len);
      uint8_t *tmp = alloca(len * sizeof (uint8_t));
      memset(tmp, 0U, len * sizeof (uint8_t));
      uint8_t *uu____4 = tmp;
      store32_be(uu____4, (uint32_t)32U);
      memcpy(uu____4, uu____4 + (uint32_t)2U, (uint32_t)2U * sizeof (uint8_t));
      uint8_t *uu____5 = tmp + (uint32_t)2U;
      uu____5[0U] = (uint8_t)0x48U;
      uu____5[1U] = (uint8_t)0x50U;
      uu____5[2U] = (uint8_t)0x4bU;
      uu____5[3U] = (uint8_t)0x45U;
      uu____5[4U] = (uint8_t)0x2dU;
      uu____5[5U] = (uint8_t)0x76U;
      uu____5[6U] = (uint8_t)0x31U;
      memcpy(tmp + (uint32_t)9U, suite_id_kem, (uint32_t)5U * sizeof (uint8_t));
      memcpy(tmp + (uint32_t)9U + (uint32_t)5U,
        label_shared_secret,
        (uint32_t)13U * sizeof (uint8_t));
      memcpy(tmp + (uint32_t)9U + (uint32_t)5U + (uint32_t)13U,
        o_kemcontext,
        (uint32_t)64U * sizeof (uint8_t));
      Hacl_HKDF_expand_sha2_256(o_shared, o_eae_prk, (uint32_t)32U, tmp, len, (uint32_t)32U);
      res0 = (uint32_t)0U;
    }
    else
    {
      res0 = (uint32_t)1U;
    }
  }
  else
  {
    res0 = (uint32_t)1U;
  }
  if (res0 == (uint32_t)0U)
  {
    uint8_t o_context[65U] = { 0U };
    uint8_t o_secret[32U] = { 0U };
    uint8_t suite_id[10U] = { 0U };
    uint8_t *uu____6 = suite_id;
    uu____6[0U] = (uint8_t)0x48U;
    uu____6[1U] = (uint8_t)0x50U;
    uu____6[2U] = (uint8_t)0x4bU;
    uu____6[3U] = (uint8_t)0x45U;
    uint8_t *uu____7 = suite_id + (uint32_t)4U;
    uu____7[0U] = (uint8_t)0U;
    uu____7[1U] = (uint8_t)32U;
    uint8_t *uu____8 = suite_id + (uint32_t)6U;
    uu____8[0U] = (uint8_t)0U;
    uu____8[1U] = (uint8_t)1U;
    uint8_t *uu____9 = suite_id + (uint32_t)8U;
    uu____9[0U] = (uint8_t)0U;
    uu____9[1U] = (uint8_t)3U;
    uint8_t
    label_psk_id_hash[11U] =
      {
        (uint8_t)0x70U, (uint8_t)0x73U, (uint8_t)0x6bU, (uint8_t)0x5fU, (uint8_t)0x69U,
        (uint8_t)0x64U, (uint8_t)0x5fU, (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x73U,
        (uint8_t)0x68U
      };
    uint8_t o_psk_id_hash[32U] = { 0U };
    uint8_t *empty = suite_id;
    uint32_t len0 = (uint32_t)7U + (uint32_t)10U + (uint32_t)11U + (uint32_t)0U;
    KRML_CHECK_SIZE(sizeof (uint8_t), len0);
    uint8_t *tmp0 = alloca(len0 * sizeof (uint8_t));
    memset(tmp0, 0U, len0 * sizeof (uint8_t));
    uint8_t *uu____10 = tmp0;
    uu____10[0U] = (uint8_t)0x48U;
    uu____10[1U] = (uint8_t)0x50U;
    uu____10[2U] = (uint8_t)0x4bU;
    uu____10[3U] = (uint8_t)0x45U;
    uu____10[4U] = (uint8_t)0x2dU;
    uu____10[5U] = (uint8_t)0x76U;
    uu____10[6U] = (uint8_t)0x31U;
    memcpy(tmp0 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
    memcpy(tmp0 + (uint32_t)7U + (uint32_t)10U,
      label_psk_id_hash,
      (uint32_t)11U * sizeof (uint8_t));
    memcpy(tmp0 + (uint32_t)7U + (uint32_t)10U + (uint32_t)11U,
      empty,
      (uint32_t)0U * sizeof (uint8_t));
    Hacl_HKDF_extract_sha2_256(o_psk_id_hash, empty, (uint32_t)0U, tmp0, len0);
    uint8_t
    label_info_hash[9U] =
      {
        (uint8_t)0x69U, (uint8_t)0x6eU, (uint8_t)0x66U, (uint8_t)0x6fU, (uint8_t)0x5fU,
        (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x73U, (uint8_t)0x68U
      };
    uint8_t o_info_hash[32U] = { 0U };
    uint32_t len1 = (uint32_t)7U + (uint32_t)10U + (uint32_t)9U + infolen;
    KRML_CHECK_SIZE(sizeof (uint8_t), len1);
    uint8_t *tmp1 = alloca(len1 * sizeof (uint8_t));
    memset(tmp1, 0U, len1 * sizeof (uint8_t));
    uint8_t *uu____11 = tmp1;
    uu____11[0U] = (uint8_t)0x48U;
    uu____11[1U] = (uint8_t)0x50U;
    uu____11[2U] = (uint8_t)0x4bU;
    uu____11[3U] = (uint8_t)0x45U;
    uu____11[4U] = (uint8_t)0x2dU;
    uu____11[5U] = (uint8_t)0x76U;
    uu____11[6U] = (uint8_t)0x31U;
    memcpy(tmp1 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
    memcpy(tmp1 + (uint32_t)7U + (uint32_t)10U, label_info_hash, (uint32_t)9U * sizeof (uint8_t));
    memcpy(tmp1 + (uint32_t)7U + (uint32_t)10U + (uint32_t)9U, info, infolen * sizeof (uint8_t));
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
    uint32_t len2 = (uint32_t)7U + (uint32_t)10U + (uint32_t)6U + (uint32_t)0U;
    KRML_CHECK_SIZE(sizeof (uint8_t), len2);
    uint8_t *tmp2 = alloca(len2 * sizeof (uint8_t));
    memset(tmp2, 0U, len2 * sizeof (uint8_t));
    uint8_t *uu____12 = tmp2;
    uu____12[0U] = (uint8_t)0x48U;
    uu____12[1U] = (uint8_t)0x50U;
    uu____12[2U] = (uint8_t)0x4bU;
    uu____12[3U] = (uint8_t)0x45U;
    uu____12[4U] = (uint8_t)0x2dU;
    uu____12[5U] = (uint8_t)0x76U;
    uu____12[6U] = (uint8_t)0x31U;
    memcpy(tmp2 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
    memcpy(tmp2 + (uint32_t)7U + (uint32_t)10U, label_secret, (uint32_t)6U * sizeof (uint8_t));
    memcpy(tmp2 + (uint32_t)7U + (uint32_t)10U + (uint32_t)6U,
      empty,
      (uint32_t)0U * sizeof (uint8_t));
    Hacl_HKDF_extract_sha2_256(o_secret, o_shared, (uint32_t)32U, tmp2, len2);
    uint8_t label_exp[3U] = { (uint8_t)0x65U, (uint8_t)0x78U, (uint8_t)0x70U };
    uint32_t len3 = (uint32_t)9U + (uint32_t)10U + (uint32_t)3U + (uint32_t)65U;
    KRML_CHECK_SIZE(sizeof (uint8_t), len3);
    uint8_t *tmp3 = alloca(len3 * sizeof (uint8_t));
    memset(tmp3, 0U, len3 * sizeof (uint8_t));
    uint8_t *uu____13 = tmp3;
    store32_be(uu____13, (uint32_t)32U);
    memcpy(uu____13, uu____13 + (uint32_t)2U, (uint32_t)2U * sizeof (uint8_t));
    uint8_t *uu____14 = tmp3 + (uint32_t)2U;
    uu____14[0U] = (uint8_t)0x48U;
    uu____14[1U] = (uint8_t)0x50U;
    uu____14[2U] = (uint8_t)0x4bU;
    uu____14[3U] = (uint8_t)0x45U;
    uu____14[4U] = (uint8_t)0x2dU;
    uu____14[5U] = (uint8_t)0x76U;
    uu____14[6U] = (uint8_t)0x31U;
    memcpy(tmp3 + (uint32_t)9U, suite_id, (uint32_t)10U * sizeof (uint8_t));
    memcpy(tmp3 + (uint32_t)9U + (uint32_t)10U, label_exp, (uint32_t)3U * sizeof (uint8_t));
    memcpy(tmp3 + (uint32_t)9U + (uint32_t)10U + (uint32_t)3U,
      o_context,
      (uint32_t)65U * sizeof (uint8_t));
    Hacl_HKDF_expand_sha2_256(o_ctx.ctx_exporter,
      o_secret,
      (uint32_t)32U,
      tmp3,
      len3,
      (uint32_t)32U);
    uint8_t label_key[3U] = { (uint8_t)0x6bU, (uint8_t)0x65U, (uint8_t)0x79U };
    uint32_t len4 = (uint32_t)9U + (uint32_t)10U + (uint32_t)3U + (uint32_t)65U;
    KRML_CHECK_SIZE(sizeof (uint8_t), len4);
    uint8_t *tmp4 = alloca(len4 * sizeof (uint8_t));
    memset(tmp4, 0U, len4 * sizeof (uint8_t));
    uint8_t *uu____15 = tmp4;
    store32_be(uu____15, (uint32_t)32U);
    memcpy(uu____15, uu____15 + (uint32_t)2U, (uint32_t)2U * sizeof (uint8_t));
    uint8_t *uu____16 = tmp4 + (uint32_t)2U;
    uu____16[0U] = (uint8_t)0x48U;
    uu____16[1U] = (uint8_t)0x50U;
    uu____16[2U] = (uint8_t)0x4bU;
    uu____16[3U] = (uint8_t)0x45U;
    uu____16[4U] = (uint8_t)0x2dU;
    uu____16[5U] = (uint8_t)0x76U;
    uu____16[6U] = (uint8_t)0x31U;
    memcpy(tmp4 + (uint32_t)9U, suite_id, (uint32_t)10U * sizeof (uint8_t));
    memcpy(tmp4 + (uint32_t)9U + (uint32_t)10U, label_key, (uint32_t)3U * sizeof (uint8_t));
    memcpy(tmp4 + (uint32_t)9U + (uint32_t)10U + (uint32_t)3U,
      o_context,
      (uint32_t)65U * sizeof (uint8_t));
    Hacl_HKDF_expand_sha2_256(o_ctx.ctx_key, o_secret, (uint32_t)32U, tmp4, len4, (uint32_t)32U);
    uint8_t
    label_base_nonce[10U] =
      {
        (uint8_t)0x62U, (uint8_t)0x61U, (uint8_t)0x73U, (uint8_t)0x65U, (uint8_t)0x5fU,
        (uint8_t)0x6eU, (uint8_t)0x6fU, (uint8_t)0x6eU, (uint8_t)0x63U, (uint8_t)0x65U
      };
    uint32_t len = (uint32_t)9U + (uint32_t)10U + (uint32_t)10U + (uint32_t)65U;
    KRML_CHECK_SIZE(sizeof (uint8_t), len);
    uint8_t *tmp = alloca(len * sizeof (uint8_t));
    memset(tmp, 0U, len * sizeof (uint8_t));
    uint8_t *uu____17 = tmp;
    store32_be(uu____17, (uint32_t)12U);
    memcpy(uu____17, uu____17 + (uint32_t)2U, (uint32_t)2U * sizeof (uint8_t));
    uint8_t *uu____18 = tmp + (uint32_t)2U;
    uu____18[0U] = (uint8_t)0x48U;
    uu____18[1U] = (uint8_t)0x50U;
    uu____18[2U] = (uint8_t)0x4bU;
    uu____18[3U] = (uint8_t)0x45U;
    uu____18[4U] = (uint8_t)0x2dU;
    uu____18[5U] = (uint8_t)0x76U;
    uu____18[6U] = (uint8_t)0x31U;
    memcpy(tmp + (uint32_t)9U, suite_id, (uint32_t)10U * sizeof (uint8_t));
    memcpy(tmp + (uint32_t)9U + (uint32_t)10U, label_base_nonce, (uint32_t)10U * sizeof (uint8_t));
    memcpy(tmp + (uint32_t)9U + (uint32_t)10U + (uint32_t)10U,
      o_context,
      (uint32_t)65U * sizeof (uint8_t));
    Hacl_HKDF_expand_sha2_256(o_ctx.ctx_nonce, o_secret, (uint32_t)32U, tmp, len, (uint32_t)12U);
    o_ctx.ctx_seq[0U] = (uint64_t)0U;
    return res0;
  }
  return res0;
}

uint32_t
Hacl_HPKE_Curve51_CP256_SHA256_setupBaseR(
  Hacl_Impl_HPKE_context_s o_ctx,
  uint8_t *enc,
  uint8_t *skR,
  uint32_t infolen,
  uint8_t *info
)
{
  uint8_t pkR[32U] = { 0U };
  Hacl_Curve25519_51_secret_to_public(pkR, skR);
  uint32_t res1 = (uint32_t)0U;
  uint8_t shared[32U] = { 0U };
  if (res1 == (uint32_t)0U)
  {
    uint8_t *pkE = enc;
    uint8_t dh[32U] = { 0U };
    uint8_t zeros[32U] = { 0U };
    Hacl_Curve25519_51_scalarmult(dh, skR, pkE);
    uint8_t res0 = (uint8_t)255U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
    {
      uint8_t uu____0 = FStar_UInt8_eq_mask(dh[i], zeros[i]);
      res0 = uu____0 & res0;
    }
    uint8_t z = res0;
    uint32_t res;
    if (z == (uint8_t)255U)
    {
      res = (uint32_t)1U;
    }
    else
    {
      res = (uint32_t)0U;
    }
    uint32_t res11 = res;
    uint32_t res2;
    uint8_t kemcontext[64U] = { 0U };
    if (res11 == (uint32_t)0U)
    {
      uint8_t *pkRm = kemcontext + (uint32_t)32U;
      uint8_t *pkR1 = pkRm;
      Hacl_Curve25519_51_secret_to_public(pkR1, skR);
      uint32_t res20 = (uint32_t)0U;
      if (res20 == (uint32_t)0U)
      {
        memcpy(kemcontext, enc, (uint32_t)32U * sizeof (uint8_t));
        uint8_t *dhm = dh;
        uint8_t o_eae_prk[32U] = { 0U };
        uint8_t suite_id_kem[5U] = { 0U };
        uint8_t *uu____1 = suite_id_kem;
        uu____1[0U] = (uint8_t)0x4bU;
        uu____1[1U] = (uint8_t)0x45U;
        uu____1[2U] = (uint8_t)0x4dU;
        uint8_t *uu____2 = suite_id_kem + (uint32_t)3U;
        uu____2[0U] = (uint8_t)0U;
        uu____2[1U] = (uint8_t)32U;
        uint8_t *empty = suite_id_kem;
        uint8_t
        label_eae_prk[7U] =
          {
            (uint8_t)0x65U, (uint8_t)0x61U, (uint8_t)0x65U, (uint8_t)0x5fU, (uint8_t)0x70U,
            (uint8_t)0x72U, (uint8_t)0x6bU
          };
        uint32_t len0 = (uint32_t)7U + (uint32_t)5U + (uint32_t)7U + (uint32_t)32U;
        KRML_CHECK_SIZE(sizeof (uint8_t), len0);
        uint8_t *tmp0 = alloca(len0 * sizeof (uint8_t));
        memset(tmp0, 0U, len0 * sizeof (uint8_t));
        uint8_t *uu____3 = tmp0;
        uu____3[0U] = (uint8_t)0x48U;
        uu____3[1U] = (uint8_t)0x50U;
        uu____3[2U] = (uint8_t)0x4bU;
        uu____3[3U] = (uint8_t)0x45U;
        uu____3[4U] = (uint8_t)0x2dU;
        uu____3[5U] = (uint8_t)0x76U;
        uu____3[6U] = (uint8_t)0x31U;
        memcpy(tmp0 + (uint32_t)7U, suite_id_kem, (uint32_t)5U * sizeof (uint8_t));
        memcpy(tmp0 + (uint32_t)7U + (uint32_t)5U, label_eae_prk, (uint32_t)7U * sizeof (uint8_t));
        memcpy(tmp0 + (uint32_t)7U + (uint32_t)5U + (uint32_t)7U,
          dhm,
          (uint32_t)32U * sizeof (uint8_t));
        Hacl_HKDF_extract_sha2_256(o_eae_prk, empty, (uint32_t)0U, tmp0, len0);
        uint8_t
        label_shared_secret[13U] =
          {
            (uint8_t)0x73U, (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x72U, (uint8_t)0x65U,
            (uint8_t)0x64U, (uint8_t)0x5fU, (uint8_t)0x73U, (uint8_t)0x65U, (uint8_t)0x63U,
            (uint8_t)0x72U, (uint8_t)0x65U, (uint8_t)0x74U
          };
        uint32_t len = (uint32_t)9U + (uint32_t)5U + (uint32_t)13U + (uint32_t)64U;
        KRML_CHECK_SIZE(sizeof (uint8_t), len);
        uint8_t *tmp = alloca(len * sizeof (uint8_t));
        memset(tmp, 0U, len * sizeof (uint8_t));
        uint8_t *uu____4 = tmp;
        store32_be(uu____4, (uint32_t)32U);
        memcpy(uu____4, uu____4 + (uint32_t)2U, (uint32_t)2U * sizeof (uint8_t));
        uint8_t *uu____5 = tmp + (uint32_t)2U;
        uu____5[0U] = (uint8_t)0x48U;
        uu____5[1U] = (uint8_t)0x50U;
        uu____5[2U] = (uint8_t)0x4bU;
        uu____5[3U] = (uint8_t)0x45U;
        uu____5[4U] = (uint8_t)0x2dU;
        uu____5[5U] = (uint8_t)0x76U;
        uu____5[6U] = (uint8_t)0x31U;
        memcpy(tmp + (uint32_t)9U, suite_id_kem, (uint32_t)5U * sizeof (uint8_t));
        memcpy(tmp + (uint32_t)9U + (uint32_t)5U,
          label_shared_secret,
          (uint32_t)13U * sizeof (uint8_t));
        memcpy(tmp + (uint32_t)9U + (uint32_t)5U + (uint32_t)13U,
          kemcontext,
          (uint32_t)64U * sizeof (uint8_t));
        Hacl_HKDF_expand_sha2_256(shared, o_eae_prk, (uint32_t)32U, tmp, len, (uint32_t)32U);
        res2 = (uint32_t)0U;
      }
      else
      {
        res2 = (uint32_t)1U;
      }
    }
    else
    {
      res2 = (uint32_t)1U;
    }
    if (res2 == (uint32_t)0U)
    {
      uint8_t o_context[65U] = { 0U };
      uint8_t o_secret[32U] = { 0U };
      uint8_t suite_id[10U] = { 0U };
      uint8_t *uu____6 = suite_id;
      uu____6[0U] = (uint8_t)0x48U;
      uu____6[1U] = (uint8_t)0x50U;
      uu____6[2U] = (uint8_t)0x4bU;
      uu____6[3U] = (uint8_t)0x45U;
      uint8_t *uu____7 = suite_id + (uint32_t)4U;
      uu____7[0U] = (uint8_t)0U;
      uu____7[1U] = (uint8_t)32U;
      uint8_t *uu____8 = suite_id + (uint32_t)6U;
      uu____8[0U] = (uint8_t)0U;
      uu____8[1U] = (uint8_t)1U;
      uint8_t *uu____9 = suite_id + (uint32_t)8U;
      uu____9[0U] = (uint8_t)0U;
      uu____9[1U] = (uint8_t)3U;
      uint8_t
      label_psk_id_hash[11U] =
        {
          (uint8_t)0x70U, (uint8_t)0x73U, (uint8_t)0x6bU, (uint8_t)0x5fU, (uint8_t)0x69U,
          (uint8_t)0x64U, (uint8_t)0x5fU, (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x73U,
          (uint8_t)0x68U
        };
      uint8_t o_psk_id_hash[32U] = { 0U };
      uint8_t *empty = suite_id;
      uint32_t len0 = (uint32_t)7U + (uint32_t)10U + (uint32_t)11U + (uint32_t)0U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len0);
      uint8_t *tmp0 = alloca(len0 * sizeof (uint8_t));
      memset(tmp0, 0U, len0 * sizeof (uint8_t));
      uint8_t *uu____10 = tmp0;
      uu____10[0U] = (uint8_t)0x48U;
      uu____10[1U] = (uint8_t)0x50U;
      uu____10[2U] = (uint8_t)0x4bU;
      uu____10[3U] = (uint8_t)0x45U;
      uu____10[4U] = (uint8_t)0x2dU;
      uu____10[5U] = (uint8_t)0x76U;
      uu____10[6U] = (uint8_t)0x31U;
      memcpy(tmp0 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
      memcpy(tmp0 + (uint32_t)7U + (uint32_t)10U,
        label_psk_id_hash,
        (uint32_t)11U * sizeof (uint8_t));
      memcpy(tmp0 + (uint32_t)7U + (uint32_t)10U + (uint32_t)11U,
        empty,
        (uint32_t)0U * sizeof (uint8_t));
      Hacl_HKDF_extract_sha2_256(o_psk_id_hash, empty, (uint32_t)0U, tmp0, len0);
      uint8_t
      label_info_hash[9U] =
        {
          (uint8_t)0x69U, (uint8_t)0x6eU, (uint8_t)0x66U, (uint8_t)0x6fU, (uint8_t)0x5fU,
          (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x73U, (uint8_t)0x68U
        };
      uint8_t o_info_hash[32U] = { 0U };
      uint32_t len1 = (uint32_t)7U + (uint32_t)10U + (uint32_t)9U + infolen;
      KRML_CHECK_SIZE(sizeof (uint8_t), len1);
      uint8_t *tmp1 = alloca(len1 * sizeof (uint8_t));
      memset(tmp1, 0U, len1 * sizeof (uint8_t));
      uint8_t *uu____11 = tmp1;
      uu____11[0U] = (uint8_t)0x48U;
      uu____11[1U] = (uint8_t)0x50U;
      uu____11[2U] = (uint8_t)0x4bU;
      uu____11[3U] = (uint8_t)0x45U;
      uu____11[4U] = (uint8_t)0x2dU;
      uu____11[5U] = (uint8_t)0x76U;
      uu____11[6U] = (uint8_t)0x31U;
      memcpy(tmp1 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
      memcpy(tmp1 + (uint32_t)7U + (uint32_t)10U, label_info_hash, (uint32_t)9U * sizeof (uint8_t));
      memcpy(tmp1 + (uint32_t)7U + (uint32_t)10U + (uint32_t)9U, info, infolen * sizeof (uint8_t));
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
      uint32_t len2 = (uint32_t)7U + (uint32_t)10U + (uint32_t)6U + (uint32_t)0U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len2);
      uint8_t *tmp2 = alloca(len2 * sizeof (uint8_t));
      memset(tmp2, 0U, len2 * sizeof (uint8_t));
      uint8_t *uu____12 = tmp2;
      uu____12[0U] = (uint8_t)0x48U;
      uu____12[1U] = (uint8_t)0x50U;
      uu____12[2U] = (uint8_t)0x4bU;
      uu____12[3U] = (uint8_t)0x45U;
      uu____12[4U] = (uint8_t)0x2dU;
      uu____12[5U] = (uint8_t)0x76U;
      uu____12[6U] = (uint8_t)0x31U;
      memcpy(tmp2 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
      memcpy(tmp2 + (uint32_t)7U + (uint32_t)10U, label_secret, (uint32_t)6U * sizeof (uint8_t));
      memcpy(tmp2 + (uint32_t)7U + (uint32_t)10U + (uint32_t)6U,
        empty,
        (uint32_t)0U * sizeof (uint8_t));
      Hacl_HKDF_extract_sha2_256(o_secret, shared, (uint32_t)32U, tmp2, len2);
      uint8_t label_exp[3U] = { (uint8_t)0x65U, (uint8_t)0x78U, (uint8_t)0x70U };
      uint32_t len3 = (uint32_t)9U + (uint32_t)10U + (uint32_t)3U + (uint32_t)65U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len3);
      uint8_t *tmp3 = alloca(len3 * sizeof (uint8_t));
      memset(tmp3, 0U, len3 * sizeof (uint8_t));
      uint8_t *uu____13 = tmp3;
      store32_be(uu____13, (uint32_t)32U);
      memcpy(uu____13, uu____13 + (uint32_t)2U, (uint32_t)2U * sizeof (uint8_t));
      uint8_t *uu____14 = tmp3 + (uint32_t)2U;
      uu____14[0U] = (uint8_t)0x48U;
      uu____14[1U] = (uint8_t)0x50U;
      uu____14[2U] = (uint8_t)0x4bU;
      uu____14[3U] = (uint8_t)0x45U;
      uu____14[4U] = (uint8_t)0x2dU;
      uu____14[5U] = (uint8_t)0x76U;
      uu____14[6U] = (uint8_t)0x31U;
      memcpy(tmp3 + (uint32_t)9U, suite_id, (uint32_t)10U * sizeof (uint8_t));
      memcpy(tmp3 + (uint32_t)9U + (uint32_t)10U, label_exp, (uint32_t)3U * sizeof (uint8_t));
      memcpy(tmp3 + (uint32_t)9U + (uint32_t)10U + (uint32_t)3U,
        o_context,
        (uint32_t)65U * sizeof (uint8_t));
      Hacl_HKDF_expand_sha2_256(o_ctx.ctx_exporter,
        o_secret,
        (uint32_t)32U,
        tmp3,
        len3,
        (uint32_t)32U);
      uint8_t label_key[3U] = { (uint8_t)0x6bU, (uint8_t)0x65U, (uint8_t)0x79U };
      uint32_t len4 = (uint32_t)9U + (uint32_t)10U + (uint32_t)3U + (uint32_t)65U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len4);
      uint8_t *tmp4 = alloca(len4 * sizeof (uint8_t));
      memset(tmp4, 0U, len4 * sizeof (uint8_t));
      uint8_t *uu____15 = tmp4;
      store32_be(uu____15, (uint32_t)32U);
      memcpy(uu____15, uu____15 + (uint32_t)2U, (uint32_t)2U * sizeof (uint8_t));
      uint8_t *uu____16 = tmp4 + (uint32_t)2U;
      uu____16[0U] = (uint8_t)0x48U;
      uu____16[1U] = (uint8_t)0x50U;
      uu____16[2U] = (uint8_t)0x4bU;
      uu____16[3U] = (uint8_t)0x45U;
      uu____16[4U] = (uint8_t)0x2dU;
      uu____16[5U] = (uint8_t)0x76U;
      uu____16[6U] = (uint8_t)0x31U;
      memcpy(tmp4 + (uint32_t)9U, suite_id, (uint32_t)10U * sizeof (uint8_t));
      memcpy(tmp4 + (uint32_t)9U + (uint32_t)10U, label_key, (uint32_t)3U * sizeof (uint8_t));
      memcpy(tmp4 + (uint32_t)9U + (uint32_t)10U + (uint32_t)3U,
        o_context,
        (uint32_t)65U * sizeof (uint8_t));
      Hacl_HKDF_expand_sha2_256(o_ctx.ctx_key, o_secret, (uint32_t)32U, tmp4, len4, (uint32_t)32U);
      uint8_t
      label_base_nonce[10U] =
        {
          (uint8_t)0x62U, (uint8_t)0x61U, (uint8_t)0x73U, (uint8_t)0x65U, (uint8_t)0x5fU,
          (uint8_t)0x6eU, (uint8_t)0x6fU, (uint8_t)0x6eU, (uint8_t)0x63U, (uint8_t)0x65U
        };
      uint32_t len = (uint32_t)9U + (uint32_t)10U + (uint32_t)10U + (uint32_t)65U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len);
      uint8_t *tmp = alloca(len * sizeof (uint8_t));
      memset(tmp, 0U, len * sizeof (uint8_t));
      uint8_t *uu____17 = tmp;
      store32_be(uu____17, (uint32_t)12U);
      memcpy(uu____17, uu____17 + (uint32_t)2U, (uint32_t)2U * sizeof (uint8_t));
      uint8_t *uu____18 = tmp + (uint32_t)2U;
      uu____18[0U] = (uint8_t)0x48U;
      uu____18[1U] = (uint8_t)0x50U;
      uu____18[2U] = (uint8_t)0x4bU;
      uu____18[3U] = (uint8_t)0x45U;
      uu____18[4U] = (uint8_t)0x2dU;
      uu____18[5U] = (uint8_t)0x76U;
      uu____18[6U] = (uint8_t)0x31U;
      memcpy(tmp + (uint32_t)9U, suite_id, (uint32_t)10U * sizeof (uint8_t));
      memcpy(tmp + (uint32_t)9U + (uint32_t)10U,
        label_base_nonce,
        (uint32_t)10U * sizeof (uint8_t));
      memcpy(tmp + (uint32_t)9U + (uint32_t)10U + (uint32_t)10U,
        o_context,
        (uint32_t)65U * sizeof (uint8_t));
      Hacl_HKDF_expand_sha2_256(o_ctx.ctx_nonce, o_secret, (uint32_t)32U, tmp, len, (uint32_t)12U);
      o_ctx.ctx_seq[0U] = (uint64_t)0U;
      return (uint32_t)0U;
    }
    return (uint32_t)1U;
  }
  return (uint32_t)1U;
}

uint32_t
Hacl_HPKE_Curve51_CP256_SHA256_sealBase(
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
  uint32_t
  res = Hacl_HPKE_Curve51_CP256_SHA256_setupBaseS(o_enc, o_ctx, skE, pkR, infolen, info);
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
    Hacl_Chacha20Poly1305_256_aead_encrypt(o_ctx.ctx_key,
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

uint32_t
Hacl_HPKE_Curve51_CP256_SHA256_openBase(
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
  uint32_t res = Hacl_HPKE_Curve51_CP256_SHA256_setupBaseR(o_ctx, pkE, skR, infolen, info);
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
      Hacl_Chacha20Poly1305_256_aead_decrypt(o_ctx.ctx_key,
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

