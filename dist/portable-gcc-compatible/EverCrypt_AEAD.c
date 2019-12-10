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


#include "EverCrypt_AEAD.h"

/* SNIPPET_START: EverCrypt_AEAD_alg_of_vale_impl */

static Spec_Agile_AEAD_alg EverCrypt_AEAD_alg_of_vale_impl(Spec_Cipher_Expansion_impl i1)
{
  switch (i1)
  {
    case Spec_Cipher_Expansion_Vale_AES128:
      {
        return Spec_Agile_AEAD_AES128_GCM;
      }
    case Spec_Cipher_Expansion_Vale_AES256:
      {
        return Spec_Agile_AEAD_AES256_GCM;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

/* SNIPPET_END: EverCrypt_AEAD_alg_of_vale_impl */

/* SNIPPET_START: EverCrypt_AEAD_state_s */

typedef struct EverCrypt_AEAD_state_s_s
{
  Spec_Cipher_Expansion_impl impl;
  uint8_t *ek;
}
EverCrypt_AEAD_state_s;

/* SNIPPET_END: EverCrypt_AEAD_state_s */

/* SNIPPET_START: EverCrypt_AEAD_uu___is_Ek */

bool EverCrypt_AEAD_uu___is_Ek(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s projectee)
{
  return true;
}

/* SNIPPET_END: EverCrypt_AEAD_uu___is_Ek */

/* SNIPPET_START: EverCrypt_AEAD___proj__Ek__item__impl */

Spec_Cipher_Expansion_impl
EverCrypt_AEAD___proj__Ek__item__impl(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s projectee)
{
  return projectee.impl;
}

/* SNIPPET_END: EverCrypt_AEAD___proj__Ek__item__impl */

/* SNIPPET_START: EverCrypt_AEAD___proj__Ek__item__ek */

uint8_t
*EverCrypt_AEAD___proj__Ek__item__ek(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s projectee)
{
  return projectee.ek;
}

/* SNIPPET_END: EverCrypt_AEAD___proj__Ek__item__ek */

/* SNIPPET_START: EverCrypt_AEAD_alg_of_state */

Spec_Agile_AEAD_alg EverCrypt_AEAD_alg_of_state(EverCrypt_AEAD_state_s *s)
{
  EverCrypt_AEAD_state_s scrut = *s;
  Spec_Cipher_Expansion_impl impl = scrut.impl;
  switch (impl)
  {
    case Spec_Cipher_Expansion_Hacl_CHACHA20:
      {
        return Spec_Agile_AEAD_CHACHA20_POLY1305;
      }
    case Spec_Cipher_Expansion_Vale_AES128:
      {
        return Spec_Agile_AEAD_AES128_GCM;
      }
    case Spec_Cipher_Expansion_Vale_AES256:
      {
        return Spec_Agile_AEAD_AES256_GCM;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

/* SNIPPET_END: EverCrypt_AEAD_alg_of_state */

/* SNIPPET_START: EverCrypt_AEAD_create_in_chacha20_poly1305 */

static EverCrypt_Error_error_code
EverCrypt_AEAD_create_in_chacha20_poly1305(EverCrypt_AEAD_state_s **dst, uint8_t *k1)
{
  uint8_t *ek = KRML_HOST_CALLOC((uint32_t)32U, sizeof (uint8_t));
  KRML_CHECK_SIZE(sizeof (EverCrypt_AEAD_state_s), (uint32_t)1U);
  EverCrypt_AEAD_state_s *p = KRML_HOST_MALLOC(sizeof (EverCrypt_AEAD_state_s));
  p[0U] = ((EverCrypt_AEAD_state_s){ .impl = Spec_Cipher_Expansion_Hacl_CHACHA20, .ek = ek });
  memcpy(ek, k1, (uint32_t)32U * sizeof k1[0U]);
  dst[0U] = p;
  return EverCrypt_Error_Success;
}

/* SNIPPET_END: EverCrypt_AEAD_create_in_chacha20_poly1305 */

/* SNIPPET_START: EverCrypt_AEAD_create_in_aes128_gcm */

static EverCrypt_Error_error_code
EverCrypt_AEAD_create_in_aes128_gcm(EverCrypt_AEAD_state_s **dst, uint8_t *k1)
{
  Spec_Agile_AEAD_alg a = EverCrypt_AEAD_alg_of_vale_impl(Spec_Cipher_Expansion_Vale_AES128);
  bool has_aesni1 = EverCrypt_AutoConfig2_has_aesni();
  bool has_pclmulqdq1 = EverCrypt_AutoConfig2_has_pclmulqdq();
  bool has_avx1 = EverCrypt_AutoConfig2_has_avx();
  bool has_sse1 = EverCrypt_AutoConfig2_has_sse();
  bool has_movbe1 = EverCrypt_AutoConfig2_has_movbe();
  #if EVERCRYPT_TARGETCONFIG_X64
  if (has_aesni1 && has_pclmulqdq1 && has_avx1 && has_sse1 && has_movbe1)
  {
    uint8_t *ek = KRML_HOST_CALLOC((uint32_t)480U, sizeof (uint8_t));
    uint8_t *keys_b = ek;
    uint8_t *hkeys_b = ek + (uint32_t)176U;
    uint64_t scrut = aes128_key_expansion(k1, keys_b);
    uint64_t scrut0 = aes128_keyhash_init(keys_b, hkeys_b);
    KRML_CHECK_SIZE(sizeof (EverCrypt_AEAD_state_s), (uint32_t)1U);
    EverCrypt_AEAD_state_s *p = KRML_HOST_MALLOC(sizeof (EverCrypt_AEAD_state_s));
    p[0U] = ((EverCrypt_AEAD_state_s){ .impl = Spec_Cipher_Expansion_Vale_AES128, .ek = ek });
    *dst = p;
    return EverCrypt_Error_Success;
  }
  #endif
  return EverCrypt_Error_UnsupportedAlgorithm;
}

/* SNIPPET_END: EverCrypt_AEAD_create_in_aes128_gcm */

/* SNIPPET_START: EverCrypt_AEAD_create_in_aes256_gcm */

static EverCrypt_Error_error_code
EverCrypt_AEAD_create_in_aes256_gcm(EverCrypt_AEAD_state_s **dst, uint8_t *k1)
{
  Spec_Agile_AEAD_alg a = EverCrypt_AEAD_alg_of_vale_impl(Spec_Cipher_Expansion_Vale_AES256);
  bool has_aesni1 = EverCrypt_AutoConfig2_has_aesni();
  bool has_pclmulqdq1 = EverCrypt_AutoConfig2_has_pclmulqdq();
  bool has_avx1 = EverCrypt_AutoConfig2_has_avx();
  bool has_sse1 = EverCrypt_AutoConfig2_has_sse();
  bool has_movbe1 = EverCrypt_AutoConfig2_has_movbe();
  #if EVERCRYPT_TARGETCONFIG_X64
  if (has_aesni1 && has_pclmulqdq1 && has_avx1 && has_sse1 && has_movbe1)
  {
    uint8_t *ek = KRML_HOST_CALLOC((uint32_t)544U, sizeof (uint8_t));
    uint8_t *keys_b = ek;
    uint8_t *hkeys_b = ek + (uint32_t)240U;
    uint64_t scrut = aes256_key_expansion(k1, keys_b);
    uint64_t scrut0 = aes256_keyhash_init(keys_b, hkeys_b);
    KRML_CHECK_SIZE(sizeof (EverCrypt_AEAD_state_s), (uint32_t)1U);
    EverCrypt_AEAD_state_s *p = KRML_HOST_MALLOC(sizeof (EverCrypt_AEAD_state_s));
    p[0U] = ((EverCrypt_AEAD_state_s){ .impl = Spec_Cipher_Expansion_Vale_AES256, .ek = ek });
    *dst = p;
    return EverCrypt_Error_Success;
  }
  #endif
  return EverCrypt_Error_UnsupportedAlgorithm;
}

/* SNIPPET_END: EverCrypt_AEAD_create_in_aes256_gcm */

/* SNIPPET_START: EverCrypt_AEAD_create_in */

EverCrypt_Error_error_code
EverCrypt_AEAD_create_in(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s **dst, uint8_t *k1)
{
  switch (a)
  {
    case Spec_Agile_AEAD_AES128_GCM:
      {
        return EverCrypt_AEAD_create_in_aes128_gcm(dst, k1);
      }
    case Spec_Agile_AEAD_AES256_GCM:
      {
        return EverCrypt_AEAD_create_in_aes256_gcm(dst, k1);
      }
    case Spec_Agile_AEAD_CHACHA20_POLY1305:
      {
        return EverCrypt_AEAD_create_in_chacha20_poly1305(dst, k1);
      }
    default:
      {
        return EverCrypt_Error_UnsupportedAlgorithm;
      }
  }
}

/* SNIPPET_END: EverCrypt_AEAD_create_in */

/* SNIPPET_START: EverCrypt_AEAD_encrypt_aes128_gcm */

static EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_aes128_gcm(
  EverCrypt_AEAD_state_s *s,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher1,
  uint8_t *tag
)
{
  if (s == NULL)
  {
    return EverCrypt_Error_InvalidKey;
  }
  Spec_Agile_AEAD_alg a = EverCrypt_AEAD_alg_of_vale_impl(Spec_Cipher_Expansion_Vale_AES128);
  if (iv_len == (uint32_t)0U)
  {
    return EverCrypt_Error_InvalidIVLength;
  }
  EverCrypt_AEAD_state_s scrut = *s;
  uint8_t *ek = scrut.ek;
  uint8_t *scratch_b = ek + (uint32_t)304U;
  uint8_t *ek1 = ek;
  uint8_t *keys_b = ek1;
  uint8_t *hkeys_b = ek1 + (uint32_t)176U;
  uint8_t tmp_iv[16U] = { 0U };
  uint32_t len = iv_len / (uint32_t)16U;
  uint32_t bytes_len = len * (uint32_t)16U;
  uint8_t *iv_b = iv;
  memcpy(tmp_iv, iv + bytes_len, iv_len % (uint32_t)16U * sizeof iv[0U]);
  uint64_t
  uu____0 = compute_iv_stdcall(iv_b, (uint64_t)iv_len, (uint64_t)len, tmp_iv, tmp_iv, hkeys_b);
  uint8_t *inout_b = scratch_b;
  uint8_t *abytes_b = scratch_b + (uint32_t)16U;
  uint8_t *scratch_b1 = scratch_b + (uint32_t)32U;
  uint32_t plain_len_ = (uint32_t)(uint64_t)plain_len / (uint32_t)16U * (uint32_t)16U;
  uint32_t auth_len_ = (uint32_t)(uint64_t)ad_len / (uint32_t)16U * (uint32_t)16U;
  uint8_t *plain_b_ = plain;
  uint8_t *out_b_ = cipher1;
  uint8_t *auth_b_ = ad;
  memcpy(inout_b,
    plain + plain_len_,
    (uint32_t)(uint64_t)plain_len % (uint32_t)16U * sizeof plain[0U]);
  memcpy(abytes_b, ad + auth_len_, (uint32_t)(uint64_t)ad_len % (uint32_t)16U * sizeof ad[0U]);
  uint64_t len128x6 = (uint64_t)plain_len / (uint64_t)96U * (uint64_t)96U;
  if (len128x6 / (uint64_t)16U >= (uint64_t)18U)
  {
    uint64_t len128_num = (uint64_t)plain_len / (uint64_t)16U * (uint64_t)16U - len128x6;
    uint8_t *in128x6_b = plain_b_;
    uint8_t *out128x6_b = out_b_;
    uint8_t *in128_b = plain_b_ + (uint32_t)len128x6;
    uint8_t *out128_b = out_b_ + (uint32_t)len128x6;
    uint64_t auth_num = (uint64_t)ad_len / (uint64_t)16U;
    uint64_t len128x6_ = len128x6 / (uint64_t)16U;
    uint64_t len128_num_ = len128_num / (uint64_t)16U;
    uint64_t
    scrut0 =
      gcm128_encrypt_opt(auth_b_,
        (uint64_t)ad_len,
        auth_num,
        keys_b,
        tmp_iv,
        hkeys_b,
        abytes_b,
        in128x6_b,
        out128x6_b,
        len128x6_,
        in128_b,
        out128_b,
        len128_num_,
        inout_b,
        (uint64_t)plain_len,
        scratch_b1,
        tag);
  }
  else
  {
    uint32_t len128x61 = (uint32_t)0U;
    uint64_t len128_num = (uint64_t)plain_len / (uint64_t)16U * (uint64_t)16U;
    uint8_t *in128x6_b = plain_b_;
    uint8_t *out128x6_b = out_b_;
    uint8_t *in128_b = plain_b_ + len128x61;
    uint8_t *out128_b = out_b_ + len128x61;
    uint64_t auth_num = (uint64_t)ad_len / (uint64_t)16U;
    uint64_t len128_num_ = len128_num / (uint64_t)16U;
    uint64_t len128x6_ = (uint64_t)0U;
    uint64_t
    scrut0 =
      gcm128_encrypt_opt(auth_b_,
        (uint64_t)ad_len,
        auth_num,
        keys_b,
        tmp_iv,
        hkeys_b,
        abytes_b,
        in128x6_b,
        out128x6_b,
        len128x6_,
        in128_b,
        out128_b,
        len128_num_,
        inout_b,
        (uint64_t)plain_len,
        scratch_b1,
        tag);
  }
  memcpy(cipher1 + (uint32_t)(uint64_t)plain_len / (uint32_t)16U * (uint32_t)16U,
    inout_b,
    (uint32_t)(uint64_t)plain_len % (uint32_t)16U * sizeof inout_b[0U]);
  return EverCrypt_Error_Success;
}

/* SNIPPET_END: EverCrypt_AEAD_encrypt_aes128_gcm */

/* SNIPPET_START: EverCrypt_AEAD_encrypt_aes256_gcm */

static EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_aes256_gcm(
  EverCrypt_AEAD_state_s *s,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher1,
  uint8_t *tag
)
{
  if (s == NULL)
  {
    return EverCrypt_Error_InvalidKey;
  }
  Spec_Agile_AEAD_alg a = EverCrypt_AEAD_alg_of_vale_impl(Spec_Cipher_Expansion_Vale_AES256);
  if (iv_len == (uint32_t)0U)
  {
    return EverCrypt_Error_InvalidIVLength;
  }
  EverCrypt_AEAD_state_s scrut = *s;
  uint8_t *ek = scrut.ek;
  uint8_t *scratch_b = ek + (uint32_t)368U;
  uint8_t *ek1 = ek;
  uint8_t *keys_b = ek1;
  uint8_t *hkeys_b = ek1 + (uint32_t)240U;
  uint8_t tmp_iv[16U] = { 0U };
  uint32_t len = iv_len / (uint32_t)16U;
  uint32_t bytes_len = len * (uint32_t)16U;
  uint8_t *iv_b = iv;
  memcpy(tmp_iv, iv + bytes_len, iv_len % (uint32_t)16U * sizeof iv[0U]);
  uint64_t
  uu____0 = compute_iv_stdcall(iv_b, (uint64_t)iv_len, (uint64_t)len, tmp_iv, tmp_iv, hkeys_b);
  uint8_t *inout_b = scratch_b;
  uint8_t *abytes_b = scratch_b + (uint32_t)16U;
  uint8_t *scratch_b1 = scratch_b + (uint32_t)32U;
  uint32_t plain_len_ = (uint32_t)(uint64_t)plain_len / (uint32_t)16U * (uint32_t)16U;
  uint32_t auth_len_ = (uint32_t)(uint64_t)ad_len / (uint32_t)16U * (uint32_t)16U;
  uint8_t *plain_b_ = plain;
  uint8_t *out_b_ = cipher1;
  uint8_t *auth_b_ = ad;
  memcpy(inout_b,
    plain + plain_len_,
    (uint32_t)(uint64_t)plain_len % (uint32_t)16U * sizeof plain[0U]);
  memcpy(abytes_b, ad + auth_len_, (uint32_t)(uint64_t)ad_len % (uint32_t)16U * sizeof ad[0U]);
  uint64_t len128x6 = (uint64_t)plain_len / (uint64_t)96U * (uint64_t)96U;
  if (len128x6 / (uint64_t)16U >= (uint64_t)18U)
  {
    uint64_t len128_num = (uint64_t)plain_len / (uint64_t)16U * (uint64_t)16U - len128x6;
    uint8_t *in128x6_b = plain_b_;
    uint8_t *out128x6_b = out_b_;
    uint8_t *in128_b = plain_b_ + (uint32_t)len128x6;
    uint8_t *out128_b = out_b_ + (uint32_t)len128x6;
    uint64_t auth_num = (uint64_t)ad_len / (uint64_t)16U;
    uint64_t len128x6_ = len128x6 / (uint64_t)16U;
    uint64_t len128_num_ = len128_num / (uint64_t)16U;
    uint64_t
    scrut0 =
      gcm256_encrypt_opt(auth_b_,
        (uint64_t)ad_len,
        auth_num,
        keys_b,
        tmp_iv,
        hkeys_b,
        abytes_b,
        in128x6_b,
        out128x6_b,
        len128x6_,
        in128_b,
        out128_b,
        len128_num_,
        inout_b,
        (uint64_t)plain_len,
        scratch_b1,
        tag);
  }
  else
  {
    uint32_t len128x61 = (uint32_t)0U;
    uint64_t len128_num = (uint64_t)plain_len / (uint64_t)16U * (uint64_t)16U;
    uint8_t *in128x6_b = plain_b_;
    uint8_t *out128x6_b = out_b_;
    uint8_t *in128_b = plain_b_ + len128x61;
    uint8_t *out128_b = out_b_ + len128x61;
    uint64_t auth_num = (uint64_t)ad_len / (uint64_t)16U;
    uint64_t len128_num_ = len128_num / (uint64_t)16U;
    uint64_t len128x6_ = (uint64_t)0U;
    uint64_t
    scrut0 =
      gcm256_encrypt_opt(auth_b_,
        (uint64_t)ad_len,
        auth_num,
        keys_b,
        tmp_iv,
        hkeys_b,
        abytes_b,
        in128x6_b,
        out128x6_b,
        len128x6_,
        in128_b,
        out128_b,
        len128_num_,
        inout_b,
        (uint64_t)plain_len,
        scratch_b1,
        tag);
  }
  memcpy(cipher1 + (uint32_t)(uint64_t)plain_len / (uint32_t)16U * (uint32_t)16U,
    inout_b,
    (uint32_t)(uint64_t)plain_len % (uint32_t)16U * sizeof inout_b[0U]);
  return EverCrypt_Error_Success;
}

/* SNIPPET_END: EverCrypt_AEAD_encrypt_aes256_gcm */

/* SNIPPET_START: EverCrypt_AEAD_encrypt */

EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt(
  EverCrypt_AEAD_state_s *s,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher1,
  uint8_t *tag
)
{
  if (s == NULL)
  {
    return EverCrypt_Error_InvalidKey;
  }
  EverCrypt_AEAD_state_s scrut = *s;
  Spec_Cipher_Expansion_impl i1 = scrut.impl;
  uint8_t *ek = scrut.ek;
  switch (i1)
  {
    case Spec_Cipher_Expansion_Vale_AES128:
      {
        return
          EverCrypt_AEAD_encrypt_aes128_gcm(s,
            iv,
            iv_len,
            ad,
            ad_len,
            plain,
            plain_len,
            cipher1,
            tag);
      }
    case Spec_Cipher_Expansion_Vale_AES256:
      {
        return
          EverCrypt_AEAD_encrypt_aes256_gcm(s,
            iv,
            iv_len,
            ad,
            ad_len,
            plain,
            plain_len,
            cipher1,
            tag);
      }
    case Spec_Cipher_Expansion_Hacl_CHACHA20:
      {
        if (iv_len != (uint32_t)12U)
        {
          return EverCrypt_Error_InvalidIVLength;
        }
        EverCrypt_Chacha20Poly1305_aead_encrypt(ek, iv, ad_len, ad, plain_len, plain, cipher1, tag);
        return EverCrypt_Error_Success;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

/* SNIPPET_END: EverCrypt_AEAD_encrypt */

/* SNIPPET_START: EverCrypt_AEAD_decrypt_aes128_gcm */

static EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_aes128_gcm(
  EverCrypt_AEAD_state_s *s,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher1,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
)
{
  if (s == NULL)
  {
    return EverCrypt_Error_InvalidKey;
  }
  if (iv_len == (uint32_t)0U)
  {
    return EverCrypt_Error_InvalidIVLength;
  }
  Spec_Agile_AEAD_alg a = EverCrypt_AEAD_alg_of_vale_impl(Spec_Cipher_Expansion_Vale_AES128);
  EverCrypt_AEAD_state_s scrut = *s;
  uint8_t *ek = scrut.ek;
  uint8_t *scratch_b = ek + (uint32_t)304U;
  uint8_t *ek1 = ek;
  uint8_t *keys_b = ek1;
  uint8_t *hkeys_b = ek1 + (uint32_t)176U;
  uint8_t tmp_iv[16U] = { 0U };
  uint32_t len = iv_len / (uint32_t)16U;
  uint32_t bytes_len = len * (uint32_t)16U;
  uint8_t *iv_b = iv;
  memcpy(tmp_iv, iv + bytes_len, iv_len % (uint32_t)16U * sizeof iv[0U]);
  uint64_t
  uu____0 = compute_iv_stdcall(iv_b, (uint64_t)iv_len, (uint64_t)len, tmp_iv, tmp_iv, hkeys_b);
  uint8_t *inout_b = scratch_b;
  uint8_t *abytes_b = scratch_b + (uint32_t)16U;
  uint8_t *scratch_b1 = scratch_b + (uint32_t)32U;
  uint32_t cipher_len_ = (uint32_t)(uint64_t)cipher_len / (uint32_t)16U * (uint32_t)16U;
  uint32_t auth_len_ = (uint32_t)(uint64_t)ad_len / (uint32_t)16U * (uint32_t)16U;
  uint8_t *cipher_b_ = cipher1;
  uint8_t *out_b_ = dst;
  uint8_t *auth_b_ = ad;
  memcpy(inout_b,
    cipher1 + cipher_len_,
    (uint32_t)(uint64_t)cipher_len % (uint32_t)16U * sizeof cipher1[0U]);
  memcpy(abytes_b, ad + auth_len_, (uint32_t)(uint64_t)ad_len % (uint32_t)16U * sizeof ad[0U]);
  uint64_t len128x6 = (uint64_t)cipher_len / (uint64_t)96U * (uint64_t)96U;
  uint64_t c;
  if (len128x6 / (uint64_t)16U >= (uint64_t)6U)
  {
    uint64_t len128_num = (uint64_t)cipher_len / (uint64_t)16U * (uint64_t)16U - len128x6;
    uint8_t *in128x6_b = cipher_b_;
    uint8_t *out128x6_b = out_b_;
    uint8_t *in128_b = cipher_b_ + (uint32_t)len128x6;
    uint8_t *out128_b = out_b_ + (uint32_t)len128x6;
    uint64_t auth_num = (uint64_t)ad_len / (uint64_t)16U;
    uint64_t len128x6_ = len128x6 / (uint64_t)16U;
    uint64_t len128_num_ = len128_num / (uint64_t)16U;
    uint64_t
    scrut0 =
      gcm128_decrypt_opt(auth_b_,
        (uint64_t)ad_len,
        auth_num,
        keys_b,
        tmp_iv,
        hkeys_b,
        abytes_b,
        in128x6_b,
        out128x6_b,
        len128x6_,
        in128_b,
        out128_b,
        len128_num_,
        inout_b,
        (uint64_t)cipher_len,
        scratch_b1,
        tag);
    uint64_t c0 = scrut0;
    c = c0;
  }
  else
  {
    uint32_t len128x61 = (uint32_t)0U;
    uint64_t len128_num = (uint64_t)cipher_len / (uint64_t)16U * (uint64_t)16U;
    uint8_t *in128x6_b = cipher_b_;
    uint8_t *out128x6_b = out_b_;
    uint8_t *in128_b = cipher_b_ + len128x61;
    uint8_t *out128_b = out_b_ + len128x61;
    uint64_t auth_num = (uint64_t)ad_len / (uint64_t)16U;
    uint64_t len128_num_ = len128_num / (uint64_t)16U;
    uint64_t len128x6_ = (uint64_t)0U;
    uint64_t
    scrut0 =
      gcm128_decrypt_opt(auth_b_,
        (uint64_t)ad_len,
        auth_num,
        keys_b,
        tmp_iv,
        hkeys_b,
        abytes_b,
        in128x6_b,
        out128x6_b,
        len128x6_,
        in128_b,
        out128_b,
        len128_num_,
        inout_b,
        (uint64_t)cipher_len,
        scratch_b1,
        tag);
    uint64_t c0 = scrut0;
    c = c0;
  }
  memcpy(dst + (uint32_t)(uint64_t)cipher_len / (uint32_t)16U * (uint32_t)16U,
    inout_b,
    (uint32_t)(uint64_t)cipher_len % (uint32_t)16U * sizeof inout_b[0U]);
  uint64_t r = c;
  if (r == (uint64_t)0U)
  {
    return EverCrypt_Error_Success;
  }
  return EverCrypt_Error_AuthenticationFailure;
}

/* SNIPPET_END: EverCrypt_AEAD_decrypt_aes128_gcm */

/* SNIPPET_START: EverCrypt_AEAD_decrypt_aes256_gcm */

static EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_aes256_gcm(
  EverCrypt_AEAD_state_s *s,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher1,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
)
{
  if (s == NULL)
  {
    return EverCrypt_Error_InvalidKey;
  }
  if (iv_len == (uint32_t)0U)
  {
    return EverCrypt_Error_InvalidIVLength;
  }
  Spec_Agile_AEAD_alg a = EverCrypt_AEAD_alg_of_vale_impl(Spec_Cipher_Expansion_Vale_AES256);
  EverCrypt_AEAD_state_s scrut = *s;
  uint8_t *ek = scrut.ek;
  uint8_t *scratch_b = ek + (uint32_t)368U;
  uint8_t *ek1 = ek;
  uint8_t *keys_b = ek1;
  uint8_t *hkeys_b = ek1 + (uint32_t)240U;
  uint8_t tmp_iv[16U] = { 0U };
  uint32_t len = iv_len / (uint32_t)16U;
  uint32_t bytes_len = len * (uint32_t)16U;
  uint8_t *iv_b = iv;
  memcpy(tmp_iv, iv + bytes_len, iv_len % (uint32_t)16U * sizeof iv[0U]);
  uint64_t
  uu____0 = compute_iv_stdcall(iv_b, (uint64_t)iv_len, (uint64_t)len, tmp_iv, tmp_iv, hkeys_b);
  uint8_t *inout_b = scratch_b;
  uint8_t *abytes_b = scratch_b + (uint32_t)16U;
  uint8_t *scratch_b1 = scratch_b + (uint32_t)32U;
  uint32_t cipher_len_ = (uint32_t)(uint64_t)cipher_len / (uint32_t)16U * (uint32_t)16U;
  uint32_t auth_len_ = (uint32_t)(uint64_t)ad_len / (uint32_t)16U * (uint32_t)16U;
  uint8_t *cipher_b_ = cipher1;
  uint8_t *out_b_ = dst;
  uint8_t *auth_b_ = ad;
  memcpy(inout_b,
    cipher1 + cipher_len_,
    (uint32_t)(uint64_t)cipher_len % (uint32_t)16U * sizeof cipher1[0U]);
  memcpy(abytes_b, ad + auth_len_, (uint32_t)(uint64_t)ad_len % (uint32_t)16U * sizeof ad[0U]);
  uint64_t len128x6 = (uint64_t)cipher_len / (uint64_t)96U * (uint64_t)96U;
  uint64_t c;
  if (len128x6 / (uint64_t)16U >= (uint64_t)6U)
  {
    uint64_t len128_num = (uint64_t)cipher_len / (uint64_t)16U * (uint64_t)16U - len128x6;
    uint8_t *in128x6_b = cipher_b_;
    uint8_t *out128x6_b = out_b_;
    uint8_t *in128_b = cipher_b_ + (uint32_t)len128x6;
    uint8_t *out128_b = out_b_ + (uint32_t)len128x6;
    uint64_t auth_num = (uint64_t)ad_len / (uint64_t)16U;
    uint64_t len128x6_ = len128x6 / (uint64_t)16U;
    uint64_t len128_num_ = len128_num / (uint64_t)16U;
    uint64_t
    scrut0 =
      gcm256_decrypt_opt(auth_b_,
        (uint64_t)ad_len,
        auth_num,
        keys_b,
        tmp_iv,
        hkeys_b,
        abytes_b,
        in128x6_b,
        out128x6_b,
        len128x6_,
        in128_b,
        out128_b,
        len128_num_,
        inout_b,
        (uint64_t)cipher_len,
        scratch_b1,
        tag);
    uint64_t c0 = scrut0;
    c = c0;
  }
  else
  {
    uint32_t len128x61 = (uint32_t)0U;
    uint64_t len128_num = (uint64_t)cipher_len / (uint64_t)16U * (uint64_t)16U;
    uint8_t *in128x6_b = cipher_b_;
    uint8_t *out128x6_b = out_b_;
    uint8_t *in128_b = cipher_b_ + len128x61;
    uint8_t *out128_b = out_b_ + len128x61;
    uint64_t auth_num = (uint64_t)ad_len / (uint64_t)16U;
    uint64_t len128_num_ = len128_num / (uint64_t)16U;
    uint64_t len128x6_ = (uint64_t)0U;
    uint64_t
    scrut0 =
      gcm256_decrypt_opt(auth_b_,
        (uint64_t)ad_len,
        auth_num,
        keys_b,
        tmp_iv,
        hkeys_b,
        abytes_b,
        in128x6_b,
        out128x6_b,
        len128x6_,
        in128_b,
        out128_b,
        len128_num_,
        inout_b,
        (uint64_t)cipher_len,
        scratch_b1,
        tag);
    uint64_t c0 = scrut0;
    c = c0;
  }
  memcpy(dst + (uint32_t)(uint64_t)cipher_len / (uint32_t)16U * (uint32_t)16U,
    inout_b,
    (uint32_t)(uint64_t)cipher_len % (uint32_t)16U * sizeof inout_b[0U]);
  uint64_t r = c;
  if (r == (uint64_t)0U)
  {
    return EverCrypt_Error_Success;
  }
  return EverCrypt_Error_AuthenticationFailure;
}

/* SNIPPET_END: EverCrypt_AEAD_decrypt_aes256_gcm */

/* SNIPPET_START: EverCrypt_AEAD_decrypt */

EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt(
  EverCrypt_AEAD_state_s *s,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher1,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
)
{
  if (s == NULL)
  {
    return EverCrypt_Error_InvalidKey;
  }
  EverCrypt_AEAD_state_s scrut = *s;
  Spec_Cipher_Expansion_impl i1 = scrut.impl;
  uint8_t *ek = scrut.ek;
  switch (i1)
  {
    case Spec_Cipher_Expansion_Vale_AES128:
      {
        return
          EverCrypt_AEAD_decrypt_aes128_gcm(s,
            iv,
            iv_len,
            ad,
            ad_len,
            cipher1,
            cipher_len,
            tag,
            dst);
      }
    case Spec_Cipher_Expansion_Vale_AES256:
      {
        return
          EverCrypt_AEAD_decrypt_aes256_gcm(s,
            iv,
            iv_len,
            ad,
            ad_len,
            cipher1,
            cipher_len,
            tag,
            dst);
      }
    case Spec_Cipher_Expansion_Hacl_CHACHA20:
      {
        if (iv_len != (uint32_t)12U)
        {
          return EverCrypt_Error_InvalidIVLength;
        }
        uint32_t
        r =
          EverCrypt_Chacha20Poly1305_aead_decrypt(ek,
            iv,
            ad_len,
            ad,
            cipher_len,
            dst,
            cipher1,
            tag);
        if (r == (uint32_t)0U)
        {
          return EverCrypt_Error_Success;
        }
        return EverCrypt_Error_AuthenticationFailure;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

/* SNIPPET_END: EverCrypt_AEAD_decrypt */

/* SNIPPET_START: EverCrypt_AEAD_free */

void EverCrypt_AEAD_free(EverCrypt_AEAD_state_s *s)
{
  EverCrypt_AEAD_state_s scrut = *s;
  uint8_t *ek = scrut.ek;
  KRML_HOST_FREE(ek);
  KRML_HOST_FREE(s);
}

/* SNIPPET_END: EverCrypt_AEAD_free */

