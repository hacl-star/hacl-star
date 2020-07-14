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


#include "Hacl_HPKE_Curve51_CP32_SHA256.h"

uint32_t
Hacl_HPKE_Curve51_CP32_SHA256_setupBaseI(
  uint8_t *o_pkE,
  uint8_t *o_k,
  uint8_t *o_n,
  uint8_t *skE,
  uint8_t *pkR,
  uint32_t infolen,
  uint8_t *info
)
{
  uint8_t zz[32U] = { 0U };
  uint8_t *o_pkE_ = o_pkE;
  uint8_t *o_zz_ = zz;
  Hacl_Curve25519_51_secret_to_public(o_pkE_, skE);
  uint32_t res1 = (uint32_t)0U;
  uint8_t *uu____0 = pkR;
  uint8_t zeros[32U] = { 0U };
  Hacl_Curve25519_51_scalarmult(o_zz_, skE, uu____0);
  uint8_t res0 = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
  {
    uint8_t uu____1 = FStar_UInt8_eq_mask(o_zz_[i], zeros[i]);
    res0 = uu____1 & res0;
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
  uint32_t res2 = res;
  uint32_t res3 = res1 | res2;
  uint8_t default_psk[32U] = { 0U };
  uint8_t default_pkI[32U] = { 0U };
  uint32_t
  context_len = (uint32_t)7U + (uint32_t)3U * (uint32_t)32U + (uint32_t)2U * (uint32_t)32U;
  KRML_CHECK_SIZE(sizeof (uint8_t), context_len);
  uint8_t context[context_len];
  memset(context, 0U, context_len * sizeof (context[0U]));
  uint8_t
  label_key[8U] =
    {
      (uint8_t)0x68U, (uint8_t)0x70U, (uint8_t)0x6bU, (uint8_t)0x65U, (uint8_t)0x20U, (uint8_t)0x6bU,
      (uint8_t)0x65U, (uint8_t)0x79U
    };
  uint8_t
  label_nonce[10U] =
    {
      (uint8_t)0x68U, (uint8_t)0x70U, (uint8_t)0x6bU, (uint8_t)0x65U, (uint8_t)0x20U, (uint8_t)0x6eU,
      (uint8_t)0x6fU, (uint8_t)0x6eU, (uint8_t)0x63U, (uint8_t)0x65U
    };
  KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)10U + context_len);
  uint8_t tmp[(uint32_t)10U + context_len];
  memset(tmp, 0U, ((uint32_t)10U + context_len) * sizeof (tmp[0U]));
  uint8_t secret[32U] = { 0U };
  uint8_t *info_hash;
  if (tmp == NULL)
  {
    info_hash = NULL;
  }
  else
  {
    info_hash = tmp;
  }
  uint8_t *pskID_hash;
  if (tmp == NULL)
  {
    pskID_hash = NULL;
  }
  else
  {
    pskID_hash = tmp + (uint32_t)32U;
  }
  Hacl_Hash_SHA2_hash_256(info, infolen, info_hash);
  uint8_t *empty_b;
  if (info == NULL)
  {
    empty_b = NULL;
  }
  else
  {
    empty_b = info;
  }
  Hacl_Hash_SHA2_hash_256(empty_b, (uint32_t)0U, pskID_hash);
  context[0U] = (uint8_t)0U;
  uint8_t *uu____2;
  if (context == NULL)
  {
    uu____2 = NULL;
  }
  else
  {
    uu____2 = context + (uint32_t)1U;
  }
  uint8_t *uu____3;
  if (uu____2 == NULL)
  {
    uu____3 = NULL;
  }
  else
  {
    uu____3 = uu____2;
  }
  uu____3[0U] = (uint8_t)0U;
  uu____3[1U] = (uint8_t)2U;
  uint8_t *uu____4;
  if (uu____2 == NULL)
  {
    uu____4 = NULL;
  }
  else
  {
    uu____4 = uu____2 + (uint32_t)2U;
  }
  uu____4[0U] = (uint8_t)0U;
  uu____4[1U] = (uint8_t)1U;
  uint8_t *uu____5;
  if (uu____2 == NULL)
  {
    uu____5 = NULL;
  }
  else
  {
    uu____5 = uu____2 + (uint32_t)4U;
  }
  uu____5[0U] = (uint8_t)0U;
  uu____5[1U] = (uint8_t)3U;
  uint8_t *uu____6;
  if (context == NULL)
  {
    uu____6 = NULL;
  }
  else
  {
    uu____6 = context + (uint32_t)7U;
  }
  bool uu____7 = o_pkE == NULL;
  if (!(uu____7 || uu____6 == NULL))
  {
    memcpy(uu____6, o_pkE, (uint32_t)32U * sizeof (o_pkE[0U]));
  }
  uint8_t *uu____8;
  if (context == NULL)
  {
    uu____8 = NULL;
  }
  else
  {
    uu____8 = context + (uint32_t)7U + (uint32_t)32U;
  }
  bool uu____9 = pkR == NULL;
  if (!(uu____9 || uu____8 == NULL))
  {
    memcpy(uu____8, pkR, (uint32_t)32U * sizeof (pkR[0U]));
  }
  uint8_t *uu____10;
  if (context == NULL)
  {
    uu____10 = NULL;
  }
  else
  {
    uu____10 = context + (uint32_t)7U + (uint32_t)32U + (uint32_t)32U;
  }
  bool uu____11 = default_pkI == NULL;
  if (!(uu____11 || uu____10 == NULL))
  {
    memcpy(uu____10, default_pkI, (uint32_t)32U * sizeof (default_pkI[0U]));
  }
  uint8_t *pskhash_b;
  if (context == NULL)
  {
    pskhash_b = NULL;
  }
  else
  {
    pskhash_b = context + (uint32_t)7U + (uint32_t)32U + (uint32_t)32U + (uint32_t)32U;
  }
  bool uu____12 = pskID_hash == NULL;
  if (!(uu____12 || pskhash_b == NULL))
  {
    memcpy(pskhash_b, pskID_hash, (uint32_t)32U * sizeof (pskID_hash[0U]));
  }
  uint8_t *output_info;
  if (context == NULL)
  {
    output_info = NULL;
  }
  else
  {
    output_info =
      context
      + (uint32_t)7U + (uint32_t)32U + (uint32_t)32U + (uint32_t)32U + (uint32_t)32U;
  }
  bool uu____13 = info_hash == NULL;
  if (!(uu____13 || output_info == NULL))
  {
    memcpy(output_info, info_hash, (uint32_t)32U * sizeof (info_hash[0U]));
  }
  Hacl_HKDF_extract_sha2_256(secret, default_psk, (uint32_t)32U, zz, (uint32_t)32U);
  uint8_t *info_key;
  if (tmp == NULL)
  {
    info_key = NULL;
  }
  else
  {
    info_key = tmp + (uint32_t)2U;
  }
  uint8_t *uu____14;
  if (info_key == NULL)
  {
    uu____14 = NULL;
  }
  else
  {
    uu____14 = info_key;
  }
  bool uu____15 = label_key == NULL;
  if (!(uu____15 || uu____14 == NULL))
  {
    memcpy(uu____14, label_key, (uint32_t)8U * sizeof (label_key[0U]));
  }
  uint8_t *uu____16;
  if (info_key == NULL)
  {
    uu____16 = NULL;
  }
  else
  {
    uu____16 = info_key + (uint32_t)8U;
  }
  bool uu____17 = context == NULL;
  if (!(uu____17 || uu____16 == NULL))
  {
    memcpy(uu____16, context, context_len * sizeof (context[0U]));
  }
  Hacl_HKDF_expand_sha2_256(o_k,
    secret,
    (uint32_t)32U,
    info_key,
    (uint32_t)8U + context_len,
    (uint32_t)32U);
  uint8_t *uu____18;
  if (tmp == NULL)
  {
    uu____18 = NULL;
  }
  else
  {
    uu____18 = tmp;
  }
  bool uu____19 = label_nonce == NULL;
  if (!(uu____19 || uu____18 == NULL))
  {
    memcpy(uu____18, label_nonce, (uint32_t)10U * sizeof (label_nonce[0U]));
  }
  Hacl_HKDF_expand_sha2_256(o_n,
    secret,
    (uint32_t)32U,
    tmp,
    (uint32_t)10U + context_len,
    (uint32_t)12U);
  return res3;
}

uint32_t
Hacl_HPKE_Curve51_CP32_SHA256_setupBaseR(
  uint8_t *o_key_aead,
  uint8_t *o_nonce_aead,
  uint8_t *pkE,
  uint8_t *skR,
  uint32_t infolen,
  uint8_t *info
)
{
  uint8_t pkR[32U] = { 0U };
  uint8_t *pkR_ = pkR;
  uint8_t zz[32U] = { 0U };
  Hacl_Curve25519_51_secret_to_public(pkR_, skR);
  uint32_t res1 = (uint32_t)0U;
  uint8_t *o_pkR_ = zz;
  uint8_t *uu____0 = pkE;
  uint8_t zeros[32U] = { 0U };
  Hacl_Curve25519_51_scalarmult(o_pkR_, skR, uu____0);
  uint8_t res0 = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
  {
    uint8_t uu____1 = FStar_UInt8_eq_mask(o_pkR_[i], zeros[i]);
    res0 = uu____1 & res0;
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
  uint32_t res2 = res;
  uint32_t res20 = res2;
  uint8_t default_psk[32U] = { 0U };
  uint8_t default_pkI[32U] = { 0U };
  uint32_t
  context_len = (uint32_t)7U + (uint32_t)3U * (uint32_t)32U + (uint32_t)2U * (uint32_t)32U;
  KRML_CHECK_SIZE(sizeof (uint8_t), context_len);
  uint8_t context[context_len];
  memset(context, 0U, context_len * sizeof (context[0U]));
  uint8_t
  label_key[8U] =
    {
      (uint8_t)0x68U, (uint8_t)0x70U, (uint8_t)0x6bU, (uint8_t)0x65U, (uint8_t)0x20U, (uint8_t)0x6bU,
      (uint8_t)0x65U, (uint8_t)0x79U
    };
  uint8_t
  label_nonce[10U] =
    {
      (uint8_t)0x68U, (uint8_t)0x70U, (uint8_t)0x6bU, (uint8_t)0x65U, (uint8_t)0x20U, (uint8_t)0x6eU,
      (uint8_t)0x6fU, (uint8_t)0x6eU, (uint8_t)0x63U, (uint8_t)0x65U
    };
  KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)10U + context_len);
  uint8_t tmp[(uint32_t)10U + context_len];
  memset(tmp, 0U, ((uint32_t)10U + context_len) * sizeof (tmp[0U]));
  uint8_t secret[32U] = { 0U };
  uint8_t *info_hash;
  if (tmp == NULL)
  {
    info_hash = NULL;
  }
  else
  {
    info_hash = tmp;
  }
  uint8_t *pskID_hash;
  if (tmp == NULL)
  {
    pskID_hash = NULL;
  }
  else
  {
    pskID_hash = tmp + (uint32_t)32U;
  }
  Hacl_Hash_SHA2_hash_256(info, infolen, info_hash);
  uint8_t *empty_b;
  if (info == NULL)
  {
    empty_b = NULL;
  }
  else
  {
    empty_b = info;
  }
  Hacl_Hash_SHA2_hash_256(empty_b, (uint32_t)0U, pskID_hash);
  context[0U] = (uint8_t)0U;
  uint8_t *uu____2;
  if (context == NULL)
  {
    uu____2 = NULL;
  }
  else
  {
    uu____2 = context + (uint32_t)1U;
  }
  uint8_t *uu____3;
  if (uu____2 == NULL)
  {
    uu____3 = NULL;
  }
  else
  {
    uu____3 = uu____2;
  }
  uu____3[0U] = (uint8_t)0U;
  uu____3[1U] = (uint8_t)2U;
  uint8_t *uu____4;
  if (uu____2 == NULL)
  {
    uu____4 = NULL;
  }
  else
  {
    uu____4 = uu____2 + (uint32_t)2U;
  }
  uu____4[0U] = (uint8_t)0U;
  uu____4[1U] = (uint8_t)1U;
  uint8_t *uu____5;
  if (uu____2 == NULL)
  {
    uu____5 = NULL;
  }
  else
  {
    uu____5 = uu____2 + (uint32_t)4U;
  }
  uu____5[0U] = (uint8_t)0U;
  uu____5[1U] = (uint8_t)3U;
  uint8_t *uu____6;
  if (context == NULL)
  {
    uu____6 = NULL;
  }
  else
  {
    uu____6 = context + (uint32_t)7U;
  }
  bool uu____7 = pkE == NULL;
  if (!(uu____7 || uu____6 == NULL))
  {
    memcpy(uu____6, pkE, (uint32_t)32U * sizeof (pkE[0U]));
  }
  uint8_t *uu____8;
  if (context == NULL)
  {
    uu____8 = NULL;
  }
  else
  {
    uu____8 = context + (uint32_t)7U + (uint32_t)32U;
  }
  bool uu____9 = pkR == NULL;
  if (!(uu____9 || uu____8 == NULL))
  {
    memcpy(uu____8, pkR, (uint32_t)32U * sizeof (pkR[0U]));
  }
  uint8_t *uu____10;
  if (context == NULL)
  {
    uu____10 = NULL;
  }
  else
  {
    uu____10 = context + (uint32_t)7U + (uint32_t)32U + (uint32_t)32U;
  }
  bool uu____11 = default_pkI == NULL;
  if (!(uu____11 || uu____10 == NULL))
  {
    memcpy(uu____10, default_pkI, (uint32_t)32U * sizeof (default_pkI[0U]));
  }
  uint8_t *pskhash_b;
  if (context == NULL)
  {
    pskhash_b = NULL;
  }
  else
  {
    pskhash_b = context + (uint32_t)7U + (uint32_t)32U + (uint32_t)32U + (uint32_t)32U;
  }
  bool uu____12 = pskID_hash == NULL;
  if (!(uu____12 || pskhash_b == NULL))
  {
    memcpy(pskhash_b, pskID_hash, (uint32_t)32U * sizeof (pskID_hash[0U]));
  }
  uint8_t *output_info;
  if (context == NULL)
  {
    output_info = NULL;
  }
  else
  {
    output_info =
      context
      + (uint32_t)7U + (uint32_t)32U + (uint32_t)32U + (uint32_t)32U + (uint32_t)32U;
  }
  bool uu____13 = info_hash == NULL;
  if (!(uu____13 || output_info == NULL))
  {
    memcpy(output_info, info_hash, (uint32_t)32U * sizeof (info_hash[0U]));
  }
  Hacl_HKDF_extract_sha2_256(secret, default_psk, (uint32_t)32U, zz, (uint32_t)32U);
  uint8_t *info_key;
  if (tmp == NULL)
  {
    info_key = NULL;
  }
  else
  {
    info_key = tmp + (uint32_t)2U;
  }
  uint8_t *uu____14;
  if (info_key == NULL)
  {
    uu____14 = NULL;
  }
  else
  {
    uu____14 = info_key;
  }
  bool uu____15 = label_key == NULL;
  if (!(uu____15 || uu____14 == NULL))
  {
    memcpy(uu____14, label_key, (uint32_t)8U * sizeof (label_key[0U]));
  }
  uint8_t *uu____16;
  if (info_key == NULL)
  {
    uu____16 = NULL;
  }
  else
  {
    uu____16 = info_key + (uint32_t)8U;
  }
  bool uu____17 = context == NULL;
  if (!(uu____17 || uu____16 == NULL))
  {
    memcpy(uu____16, context, context_len * sizeof (context[0U]));
  }
  Hacl_HKDF_expand_sha2_256(o_key_aead,
    secret,
    (uint32_t)32U,
    info_key,
    (uint32_t)8U + context_len,
    (uint32_t)32U);
  uint8_t *uu____18;
  if (tmp == NULL)
  {
    uu____18 = NULL;
  }
  else
  {
    uu____18 = tmp;
  }
  bool uu____19 = label_nonce == NULL;
  if (!(uu____19 || uu____18 == NULL))
  {
    memcpy(uu____18, label_nonce, (uint32_t)10U * sizeof (label_nonce[0U]));
  }
  Hacl_HKDF_expand_sha2_256(o_nonce_aead,
    secret,
    (uint32_t)32U,
    tmp,
    (uint32_t)10U + context_len,
    (uint32_t)12U);
  return res1 | res20;
}

uint32_t
Hacl_HPKE_Curve51_CP32_SHA256_sealBase(
  uint8_t *skE,
  uint8_t *pkR,
  uint32_t mlen,
  uint8_t *m,
  uint32_t infolen,
  uint8_t *info,
  uint8_t *output
)
{
  uint8_t zz[32U] = { 0U };
  uint8_t k[32U] = { 0U };
  uint8_t n[12U] = { 0U };
  uint8_t *pkE;
  if (output == NULL)
  {
    pkE = NULL;
  }
  else
  {
    pkE = output;
  }
  uint32_t res = Hacl_HPKE_Curve51_CP32_SHA256_setupBaseI(pkE, k, n, skE, pkR, infolen, info);
  uint8_t *dec;
  if (output == NULL)
  {
    dec = NULL;
  }
  else
  {
    dec = output + (uint32_t)32U;
  }
  uint8_t *uu____0;
  if (dec == NULL)
  {
    uu____0 = NULL;
  }
  else
  {
    uu____0 = dec;
  }
  uint8_t *ite;
  if (dec == NULL)
  {
    ite = NULL;
  }
  else
  {
    ite = dec + mlen;
  }
  Hacl_Chacha20Poly1305_32_aead_encrypt(k, n, infolen, info, mlen, m, uu____0, ite);
  uint32_t res0 = res;
  return res0;
}

uint32_t
Hacl_HPKE_Curve51_CP32_SHA256_openBase(
  uint8_t *pkE,
  uint8_t *skR,
  uint32_t mlen,
  uint8_t *m,
  uint32_t infolen,
  uint8_t *info,
  uint8_t *output
)
{
  uint8_t zz[32U] = { 0U };
  uint8_t k[32U] = { 0U };
  uint8_t n[12U] = { 0U };
  uint8_t *pkE1;
  if (m == NULL)
  {
    pkE1 = NULL;
  }
  else
  {
    pkE1 = m;
  }
  uint32_t clen = mlen - (uint32_t)32U;
  uint8_t *c;
  if (m == NULL)
  {
    c = NULL;
  }
  else
  {
    c = m + (uint32_t)32U;
  }
  uint32_t res1 = Hacl_HPKE_Curve51_CP32_SHA256_setupBaseR(k, n, pkE1, skR, infolen, info);
  uint8_t *uu____0;
  if (c == NULL)
  {
    uu____0 = NULL;
  }
  else
  {
    uu____0 = c;
  }
  uint8_t *ite;
  if (c == NULL)
  {
    ite = NULL;
  }
  else
  {
    ite = c + clen - (uint32_t)16U;
  }
  uint32_t
  res2 =
    Hacl_Chacha20Poly1305_32_aead_decrypt(k,
      n,
      infolen,
      info,
      clen - (uint32_t)16U,
      output,
      uu____0,
      ite);
  uint32_t z = res1 | res2;
  return z;
}

