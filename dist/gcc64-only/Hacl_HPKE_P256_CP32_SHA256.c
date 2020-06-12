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


#include "Hacl_HPKE_P256_CP32_SHA256.h"

uint32_t
Hacl_HPKE_P256_CP32_SHA256_setupBaseI(
  uint8_t *o_pkE,
  uint8_t *o_k,
  uint8_t *o_n,
  uint8_t *skE,
  uint8_t *pkR,
  uint32_t infolen,
  uint8_t *info
)
{
  uint8_t zz[65U] = { 0U };
  uint8_t *o_pkE_ = o_pkE + (uint32_t)1U;
  uint8_t *o_zz_ = zz + (uint32_t)1U;
  uint64_t res0 = Hacl_Impl_P256_DH_ecp256dh_i(o_pkE_, skE);
  uint64_t r_ = res0 & (uint64_t)1U;
  uint32_t res1 = (uint32_t)r_;
  uint8_t *uu____0 = pkR + (uint32_t)1U;
  uint8_t tmp0[64U] = { 0U };
  uint64_t res = Hacl_Impl_P256_DH_ecp256dh_r(tmp0, uu____0, skE);
  memcpy(o_zz_, tmp0, (uint32_t)64U * sizeof (tmp0[0U]));
  uint64_t r_0 = res & (uint64_t)1U;
  uint32_t res2 = (uint32_t)r_0;
  zz[0U] = (uint8_t)4U;
  o_pkE[0U] = (uint8_t)4U;
  uint32_t res3 = res1 | res2;
  uint8_t default_psk1[32U] = { 0U };
  uint8_t default_pkI1[65U] = { 0U };
  uint32_t
  context_len = (uint32_t)7U + (uint32_t)3U * (uint32_t)65U + (uint32_t)2U * (uint32_t)32U;
  KRML_CHECK_SIZE(sizeof (uint8_t), context_len);
  uint8_t context[context_len];
  memset(context, 0U, context_len * sizeof (context[0U]));
  uint8_t
  label_key1[8U] =
    {
      (uint8_t)0x68U, (uint8_t)0x70U, (uint8_t)0x6bU, (uint8_t)0x65U, (uint8_t)0x20U, (uint8_t)0x6bU,
      (uint8_t)0x65U, (uint8_t)0x79U
    };
  uint8_t
  label_nonce1[10U] =
    {
      (uint8_t)0x68U, (uint8_t)0x70U, (uint8_t)0x6bU, (uint8_t)0x65U, (uint8_t)0x20U, (uint8_t)0x6eU,
      (uint8_t)0x6fU, (uint8_t)0x6eU, (uint8_t)0x63U, (uint8_t)0x65U
    };
  KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)10U + context_len);
  uint8_t tmp[(uint32_t)10U + context_len];
  memset(tmp, 0U, ((uint32_t)10U + context_len) * sizeof (tmp[0U]));
  uint8_t secret1[32U] = { 0U };
  uint8_t *info_hash = tmp;
  uint8_t *pskID_hash = tmp + (uint32_t)32U;
  Hacl_Hash_SHA2_hash_256(info, infolen, info_hash);
  uint8_t *empty_b = info;
  Hacl_Hash_SHA2_hash_256(empty_b, (uint32_t)0U, pskID_hash);
  context[0U] = (uint8_t)0U;
  uint8_t *uu____1 = context + (uint32_t)1U;
  uint8_t *uu____2 = uu____1;
  uu____2[0U] = (uint8_t)0U;
  uu____2[1U] = (uint8_t)1U;
  uint8_t *uu____3 = uu____1 + (uint32_t)2U;
  uu____3[0U] = (uint8_t)0U;
  uu____3[1U] = (uint8_t)1U;
  uint8_t *uu____4 = uu____1 + (uint32_t)4U;
  uu____4[0U] = (uint8_t)0U;
  uu____4[1U] = (uint8_t)3U;
  memcpy(context + (uint32_t)7U, o_pkE, (uint32_t)65U * sizeof (o_pkE[0U]));
  memcpy(context + (uint32_t)7U + (uint32_t)65U, pkR, (uint32_t)65U * sizeof (pkR[0U]));
  memcpy(context + (uint32_t)7U + (uint32_t)65U + (uint32_t)65U,
    default_pkI1,
    (uint32_t)65U * sizeof (default_pkI1[0U]));
  uint8_t *pskhash_b = context + (uint32_t)7U + (uint32_t)65U + (uint32_t)65U + (uint32_t)65U;
  memcpy(pskhash_b, pskID_hash, (uint32_t)32U * sizeof (pskID_hash[0U]));
  uint8_t
  *output_info =
    context
    + (uint32_t)7U + (uint32_t)65U + (uint32_t)65U + (uint32_t)65U + (uint32_t)32U;
  memcpy(output_info, info_hash, (uint32_t)32U * sizeof (info_hash[0U]));
  Hacl_HKDF_extract_sha2_256(secret1, default_psk1, (uint32_t)32U, zz, (uint32_t)65U);
  uint8_t *info_key = tmp + (uint32_t)2U;
  memcpy(info_key, label_key1, (uint32_t)8U * sizeof (label_key1[0U]));
  memcpy(info_key + (uint32_t)8U, context, context_len * sizeof (context[0U]));
  Hacl_HKDF_expand_sha2_256(o_k,
    secret1,
    (uint32_t)32U,
    info_key,
    (uint32_t)8U + context_len,
    (uint32_t)32U);
  memcpy(tmp, label_nonce1, (uint32_t)10U * sizeof (label_nonce1[0U]));
  Hacl_HKDF_expand_sha2_256(o_n,
    secret1,
    (uint32_t)32U,
    tmp,
    (uint32_t)10U + context_len,
    (uint32_t)12U);
  return res3;
}

uint32_t
Hacl_HPKE_P256_CP32_SHA256_setupBaseR(
  uint8_t *o_key_aead,
  uint8_t *o_nonce_aead,
  uint8_t *pkE,
  uint8_t *skR,
  uint32_t infolen,
  uint8_t *info
)
{
  uint8_t pkR[65U] = { 0U };
  uint8_t *pkR_ = pkR + (uint32_t)1U;
  uint8_t zz[65U] = { 0U };
  uint64_t res0 = Hacl_Impl_P256_DH_ecp256dh_i(pkR_, skR);
  uint64_t r_ = res0 & (uint64_t)1U;
  uint32_t res1 = (uint32_t)r_;
  pkR[0U] = (uint8_t)4U;
  uint8_t *o_pkR_ = zz + (uint32_t)1U;
  uint8_t *uu____0 = pkE + (uint32_t)1U;
  uint8_t tmp0[64U] = { 0U };
  uint64_t res = Hacl_Impl_P256_DH_ecp256dh_r(tmp0, uu____0, skR);
  memcpy(o_pkR_, tmp0, (uint32_t)64U * sizeof (tmp0[0U]));
  uint64_t r_0 = res & (uint64_t)1U;
  uint32_t res2 = (uint32_t)r_0;
  zz[0U] = (uint8_t)4U;
  uint32_t res20 = res2;
  uint8_t default_psk1[32U] = { 0U };
  uint8_t default_pkI1[65U] = { 0U };
  uint32_t
  context_len = (uint32_t)7U + (uint32_t)3U * (uint32_t)65U + (uint32_t)2U * (uint32_t)32U;
  KRML_CHECK_SIZE(sizeof (uint8_t), context_len);
  uint8_t context[context_len];
  memset(context, 0U, context_len * sizeof (context[0U]));
  uint8_t
  label_key1[8U] =
    {
      (uint8_t)0x68U, (uint8_t)0x70U, (uint8_t)0x6bU, (uint8_t)0x65U, (uint8_t)0x20U, (uint8_t)0x6bU,
      (uint8_t)0x65U, (uint8_t)0x79U
    };
  uint8_t
  label_nonce1[10U] =
    {
      (uint8_t)0x68U, (uint8_t)0x70U, (uint8_t)0x6bU, (uint8_t)0x65U, (uint8_t)0x20U, (uint8_t)0x6eU,
      (uint8_t)0x6fU, (uint8_t)0x6eU, (uint8_t)0x63U, (uint8_t)0x65U
    };
  KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)10U + context_len);
  uint8_t tmp[(uint32_t)10U + context_len];
  memset(tmp, 0U, ((uint32_t)10U + context_len) * sizeof (tmp[0U]));
  uint8_t secret1[32U] = { 0U };
  uint8_t *info_hash = tmp;
  uint8_t *pskID_hash = tmp + (uint32_t)32U;
  Hacl_Hash_SHA2_hash_256(info, infolen, info_hash);
  uint8_t *empty_b = info;
  Hacl_Hash_SHA2_hash_256(empty_b, (uint32_t)0U, pskID_hash);
  context[0U] = (uint8_t)0U;
  uint8_t *uu____1 = context + (uint32_t)1U;
  uint8_t *uu____2 = uu____1;
  uu____2[0U] = (uint8_t)0U;
  uu____2[1U] = (uint8_t)1U;
  uint8_t *uu____3 = uu____1 + (uint32_t)2U;
  uu____3[0U] = (uint8_t)0U;
  uu____3[1U] = (uint8_t)1U;
  uint8_t *uu____4 = uu____1 + (uint32_t)4U;
  uu____4[0U] = (uint8_t)0U;
  uu____4[1U] = (uint8_t)3U;
  memcpy(context + (uint32_t)7U, pkE, (uint32_t)65U * sizeof (pkE[0U]));
  memcpy(context + (uint32_t)7U + (uint32_t)65U, pkR, (uint32_t)65U * sizeof (pkR[0U]));
  memcpy(context + (uint32_t)7U + (uint32_t)65U + (uint32_t)65U,
    default_pkI1,
    (uint32_t)65U * sizeof (default_pkI1[0U]));
  uint8_t *pskhash_b = context + (uint32_t)7U + (uint32_t)65U + (uint32_t)65U + (uint32_t)65U;
  memcpy(pskhash_b, pskID_hash, (uint32_t)32U * sizeof (pskID_hash[0U]));
  uint8_t
  *output_info =
    context
    + (uint32_t)7U + (uint32_t)65U + (uint32_t)65U + (uint32_t)65U + (uint32_t)32U;
  memcpy(output_info, info_hash, (uint32_t)32U * sizeof (info_hash[0U]));
  Hacl_HKDF_extract_sha2_256(secret1, default_psk1, (uint32_t)32U, zz, (uint32_t)65U);
  uint8_t *info_key = tmp + (uint32_t)2U;
  memcpy(info_key, label_key1, (uint32_t)8U * sizeof (label_key1[0U]));
  memcpy(info_key + (uint32_t)8U, context, context_len * sizeof (context[0U]));
  Hacl_HKDF_expand_sha2_256(o_key_aead,
    secret1,
    (uint32_t)32U,
    info_key,
    (uint32_t)8U + context_len,
    (uint32_t)32U);
  memcpy(tmp, label_nonce1, (uint32_t)10U * sizeof (label_nonce1[0U]));
  Hacl_HKDF_expand_sha2_256(o_nonce_aead,
    secret1,
    (uint32_t)32U,
    tmp,
    (uint32_t)10U + context_len,
    (uint32_t)12U);
  return res1 | res20;
}

uint32_t
Hacl_HPKE_P256_CP32_SHA256_sealBase(
  uint8_t *skE,
  uint8_t *pkR,
  uint32_t mlen,
  uint8_t *m,
  uint32_t infolen,
  uint8_t *info,
  uint8_t *output
)
{
  uint8_t zz[65U] = { 0U };
  uint8_t k1[32U] = { 0U };
  uint8_t n1[12U] = { 0U };
  uint8_t *pkE = output;
  uint32_t res = Hacl_HPKE_P256_CP32_SHA256_setupBaseI(pkE, k1, n1, skE, pkR, infolen, info);
  uint8_t *dec = output + (uint32_t)65U;
  Hacl_Chacha20Poly1305_32_aead_encrypt(k1, n1, infolen, info, mlen, m, dec, dec + mlen);
  uint32_t res0 = res;
  return res0;
}

uint32_t
Hacl_HPKE_P256_CP32_SHA256_openBase(
  uint8_t *pkE,
  uint8_t *skR,
  uint32_t mlen,
  uint8_t *m,
  uint32_t infolen,
  uint8_t *info,
  uint8_t *output
)
{
  uint8_t zz[65U] = { 0U };
  uint8_t k1[32U] = { 0U };
  uint8_t n1[12U] = { 0U };
  uint8_t *pkE1 = m;
  uint32_t clen = mlen - (uint32_t)65U;
  uint8_t *c = m + (uint32_t)65U;
  uint32_t res1 = Hacl_HPKE_P256_CP32_SHA256_setupBaseR(k1, n1, pkE1, skR, infolen, info);
  uint32_t
  res2 =
    Hacl_Chacha20Poly1305_32_aead_decrypt(k1,
      n1,
      infolen,
      info,
      clen - (uint32_t)16U,
      output,
      c,
      c + clen - (uint32_t)16U);
  uint32_t z = res1 | res2;
  return z;
}

