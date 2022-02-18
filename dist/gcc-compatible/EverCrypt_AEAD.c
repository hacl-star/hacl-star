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

#include "internal/Vale.h"
#include "internal/Hacl_Kremlib.h"

typedef struct EverCrypt_AEAD_state_s_s
{
  Spec_Cipher_Expansion_impl impl;
  uint8_t *ek;
}
EverCrypt_AEAD_state_s;

bool EverCrypt_AEAD_uu___is_Ek(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s projectee)
{
  return true;
}

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

static EverCrypt_Error_error_code
create_in_chacha20_poly1305(EverCrypt_AEAD_state_s **dst, uint8_t *k)
{
  uint8_t *ek = KRML_HOST_CALLOC((uint32_t)32U, sizeof (uint8_t));
  KRML_CHECK_SIZE(sizeof (EverCrypt_AEAD_state_s), (uint32_t)1U);
  EverCrypt_AEAD_state_s *p = KRML_HOST_MALLOC(sizeof (EverCrypt_AEAD_state_s));
  p[0U] = ((EverCrypt_AEAD_state_s){ .impl = Spec_Cipher_Expansion_Hacl_CHACHA20, .ek = ek });
  memcpy(ek, k, (uint32_t)32U * sizeof (uint8_t));
  dst[0U] = p;
  return EverCrypt_Error_Success;
}

static EverCrypt_Error_error_code
create_in_aes128_gcm(EverCrypt_AEAD_state_s **dst, uint8_t *k)
{
  bool has_aesni = EverCrypt_AutoConfig2_has_aesni();
  bool has_pclmulqdq = EverCrypt_AutoConfig2_has_pclmulqdq();
  bool has_avx = EverCrypt_AutoConfig2_has_avx();
  bool has_sse = EverCrypt_AutoConfig2_has_sse();
  bool has_movbe = EverCrypt_AutoConfig2_has_movbe();
  #if HACL_CAN_COMPILE_VALE
  if (has_aesni && has_pclmulqdq && has_avx && has_sse && has_movbe)
  {
    uint8_t *ek = KRML_HOST_CALLOC((uint32_t)480U, sizeof (uint8_t));
    uint8_t *keys_b = ek;
    uint8_t *hkeys_b = ek + (uint32_t)176U;
    uint64_t scrut = aes128_key_expansion(k, keys_b);
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

static EverCrypt_Error_error_code
create_in_aes256_gcm(EverCrypt_AEAD_state_s **dst, uint8_t *k)
{
  bool has_aesni = EverCrypt_AutoConfig2_has_aesni();
  bool has_pclmulqdq = EverCrypt_AutoConfig2_has_pclmulqdq();
  bool has_avx = EverCrypt_AutoConfig2_has_avx();
  bool has_sse = EverCrypt_AutoConfig2_has_sse();
  bool has_movbe = EverCrypt_AutoConfig2_has_movbe();
  #if HACL_CAN_COMPILE_VALE
  if (has_aesni && has_pclmulqdq && has_avx && has_sse && has_movbe)
  {
    uint8_t *ek = KRML_HOST_CALLOC((uint32_t)544U, sizeof (uint8_t));
    uint8_t *keys_b = ek;
    uint8_t *hkeys_b = ek + (uint32_t)240U;
    uint64_t scrut = aes256_key_expansion(k, keys_b);
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

EverCrypt_Error_error_code
EverCrypt_AEAD_create_in(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s **dst, uint8_t *k)
{
  switch (a)
  {
    case Spec_Agile_AEAD_AES128_GCM:
      {
        return create_in_aes128_gcm(dst, k);
      }
    case Spec_Agile_AEAD_AES256_GCM:
      {
        return create_in_aes256_gcm(dst, k);
      }
    case Spec_Agile_AEAD_CHACHA20_POLY1305:
      {
        return create_in_chacha20_poly1305(dst, k);
      }
    default:
      {
        return EverCrypt_Error_UnsupportedAlgorithm;
      }
  }
}

static EverCrypt_Error_error_code
encrypt_aes128_gcm(
  EverCrypt_AEAD_state_s *s,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
)
{
  #if HACL_CAN_COMPILE_VALE
  if (s == NULL)
  {
    return EverCrypt_Error_InvalidKey;
  }
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
  memcpy(tmp_iv, iv + bytes_len, iv_len % (uint32_t)16U * sizeof (uint8_t));
  uint64_t
  uu____0 = compute_iv_stdcall(iv_b, (uint64_t)iv_len, (uint64_t)len, tmp_iv, tmp_iv, hkeys_b);
  uint8_t *inout_b = scratch_b;
  uint8_t *abytes_b = scratch_b + (uint32_t)16U;
  uint8_t *scratch_b1 = scratch_b + (uint32_t)32U;
  uint32_t plain_len_ = (uint32_t)(uint64_t)plain_len / (uint32_t)16U * (uint32_t)16U;
  uint32_t auth_len_ = (uint32_t)(uint64_t)ad_len / (uint32_t)16U * (uint32_t)16U;
  uint8_t *plain_b_ = plain;
  uint8_t *out_b_ = cipher;
  uint8_t *auth_b_ = ad;
  memcpy(inout_b,
    plain + plain_len_,
    (uint32_t)(uint64_t)plain_len % (uint32_t)16U * sizeof (uint8_t));
  memcpy(abytes_b,
    ad + auth_len_,
    (uint32_t)(uint64_t)ad_len % (uint32_t)16U * sizeof (uint8_t));
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
  memcpy(cipher + (uint32_t)(uint64_t)plain_len / (uint32_t)16U * (uint32_t)16U,
    inout_b,
    (uint32_t)(uint64_t)plain_len % (uint32_t)16U * sizeof (uint8_t));
  return EverCrypt_Error_Success;
  #else
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "statically unreachable");
  KRML_HOST_EXIT(255U);
  #endif
}

static EverCrypt_Error_error_code
encrypt_aes256_gcm(
  EverCrypt_AEAD_state_s *s,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
)
{
  #if HACL_CAN_COMPILE_VALE
  if (s == NULL)
  {
    return EverCrypt_Error_InvalidKey;
  }
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
  memcpy(tmp_iv, iv + bytes_len, iv_len % (uint32_t)16U * sizeof (uint8_t));
  uint64_t
  uu____0 = compute_iv_stdcall(iv_b, (uint64_t)iv_len, (uint64_t)len, tmp_iv, tmp_iv, hkeys_b);
  uint8_t *inout_b = scratch_b;
  uint8_t *abytes_b = scratch_b + (uint32_t)16U;
  uint8_t *scratch_b1 = scratch_b + (uint32_t)32U;
  uint32_t plain_len_ = (uint32_t)(uint64_t)plain_len / (uint32_t)16U * (uint32_t)16U;
  uint32_t auth_len_ = (uint32_t)(uint64_t)ad_len / (uint32_t)16U * (uint32_t)16U;
  uint8_t *plain_b_ = plain;
  uint8_t *out_b_ = cipher;
  uint8_t *auth_b_ = ad;
  memcpy(inout_b,
    plain + plain_len_,
    (uint32_t)(uint64_t)plain_len % (uint32_t)16U * sizeof (uint8_t));
  memcpy(abytes_b,
    ad + auth_len_,
    (uint32_t)(uint64_t)ad_len % (uint32_t)16U * sizeof (uint8_t));
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
  memcpy(cipher + (uint32_t)(uint64_t)plain_len / (uint32_t)16U * (uint32_t)16U,
    inout_b,
    (uint32_t)(uint64_t)plain_len % (uint32_t)16U * sizeof (uint8_t));
  return EverCrypt_Error_Success;
  #else
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "statically unreachable");
  KRML_HOST_EXIT(255U);
  #endif
}

EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt(
  EverCrypt_AEAD_state_s *s,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
)
{
  if (s == NULL)
  {
    return EverCrypt_Error_InvalidKey;
  }
  EverCrypt_AEAD_state_s scrut = *s;
  Spec_Cipher_Expansion_impl i = scrut.impl;
  uint8_t *ek = scrut.ek;
  switch (i)
  {
    case Spec_Cipher_Expansion_Vale_AES128:
      {
        return encrypt_aes128_gcm(s, iv, iv_len, ad, ad_len, plain, plain_len, cipher, tag);
      }
    case Spec_Cipher_Expansion_Vale_AES256:
      {
        return encrypt_aes256_gcm(s, iv, iv_len, ad, ad_len, plain, plain_len, cipher, tag);
      }
    case Spec_Cipher_Expansion_Hacl_CHACHA20:
      {
        if (iv_len != (uint32_t)12U)
        {
          return EverCrypt_Error_InvalidIVLength;
        }
        EverCrypt_Chacha20Poly1305_aead_encrypt(ek, iv, ad_len, ad, plain_len, plain, cipher, tag);
        return EverCrypt_Error_Success;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

/*
WARNING: this function doesn't perform any dynamic
  hardware check. You MUST make sure your hardware supports the
  implementation of AESGCM. Besides, this function was not designed
  for cross-compilation: if you compile it on a system which doesn't
  support Vale, it will compile it to a function which makes the
  program exit.
*/
EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_expand_aes128_gcm_no_check(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
)
{
  #if HACL_CAN_COMPILE_VALE
  uint8_t ek[480U] = { 0U };
  uint8_t *keys_b0 = ek;
  uint8_t *hkeys_b0 = ek + (uint32_t)176U;
  uint64_t scrut0 = aes128_key_expansion(k, keys_b0);
  uint64_t scrut1 = aes128_keyhash_init(keys_b0, hkeys_b0);
  EverCrypt_AEAD_state_s p = { .impl = Spec_Cipher_Expansion_Vale_AES128, .ek = ek };
  EverCrypt_AEAD_state_s *s = &p;
  EverCrypt_Error_error_code r;
  if (s == NULL)
  {
    r = EverCrypt_Error_InvalidKey;
  }
  else if (iv_len == (uint32_t)0U)
  {
    r = EverCrypt_Error_InvalidIVLength;
  }
  else
  {
    EverCrypt_AEAD_state_s scrut = *s;
    uint8_t *ek0 = scrut.ek;
    uint8_t *scratch_b = ek0 + (uint32_t)304U;
    uint8_t *ek1 = ek0;
    uint8_t *keys_b = ek1;
    uint8_t *hkeys_b = ek1 + (uint32_t)176U;
    uint8_t tmp_iv[16U] = { 0U };
    uint32_t len = iv_len / (uint32_t)16U;
    uint32_t bytes_len = len * (uint32_t)16U;
    uint8_t *iv_b = iv;
    memcpy(tmp_iv, iv + bytes_len, iv_len % (uint32_t)16U * sizeof (uint8_t));
    uint64_t
    uu____0 = compute_iv_stdcall(iv_b, (uint64_t)iv_len, (uint64_t)len, tmp_iv, tmp_iv, hkeys_b);
    uint8_t *inout_b = scratch_b;
    uint8_t *abytes_b = scratch_b + (uint32_t)16U;
    uint8_t *scratch_b1 = scratch_b + (uint32_t)32U;
    uint32_t plain_len_ = (uint32_t)(uint64_t)plain_len / (uint32_t)16U * (uint32_t)16U;
    uint32_t auth_len_ = (uint32_t)(uint64_t)ad_len / (uint32_t)16U * (uint32_t)16U;
    uint8_t *plain_b_ = plain;
    uint8_t *out_b_ = cipher;
    uint8_t *auth_b_ = ad;
    memcpy(inout_b,
      plain + plain_len_,
      (uint32_t)(uint64_t)plain_len % (uint32_t)16U * sizeof (uint8_t));
    memcpy(abytes_b,
      ad + auth_len_,
      (uint32_t)(uint64_t)ad_len % (uint32_t)16U * sizeof (uint8_t));
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
      scrut2 =
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
      scrut2 =
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
    memcpy(cipher + (uint32_t)(uint64_t)plain_len / (uint32_t)16U * (uint32_t)16U,
      inout_b,
      (uint32_t)(uint64_t)plain_len % (uint32_t)16U * sizeof (uint8_t));
    r = EverCrypt_Error_Success;
  }
  return EverCrypt_Error_Success;
  #else
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "EverCrypt was compiled on a system which doesn\'t support Vale");
  KRML_HOST_EXIT(255U);
  #endif
}

/*
WARNING: this function doesn't perform any dynamic
  hardware check. You MUST make sure your hardware supports the
  implementation of AESGCM. Besides, this function was not designed
  for cross-compilation: if you compile it on a system which doesn't
  support Vale, it will compile it to a function which makes the
  program exit.
*/
EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_expand_aes256_gcm_no_check(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
)
{
  #if HACL_CAN_COMPILE_VALE
  uint8_t ek[544U] = { 0U };
  uint8_t *keys_b0 = ek;
  uint8_t *hkeys_b0 = ek + (uint32_t)240U;
  uint64_t scrut0 = aes256_key_expansion(k, keys_b0);
  uint64_t scrut1 = aes256_keyhash_init(keys_b0, hkeys_b0);
  EverCrypt_AEAD_state_s p = { .impl = Spec_Cipher_Expansion_Vale_AES256, .ek = ek };
  EverCrypt_AEAD_state_s *s = &p;
  EverCrypt_Error_error_code r;
  if (s == NULL)
  {
    r = EverCrypt_Error_InvalidKey;
  }
  else if (iv_len == (uint32_t)0U)
  {
    r = EverCrypt_Error_InvalidIVLength;
  }
  else
  {
    EverCrypt_AEAD_state_s scrut = *s;
    uint8_t *ek0 = scrut.ek;
    uint8_t *scratch_b = ek0 + (uint32_t)368U;
    uint8_t *ek1 = ek0;
    uint8_t *keys_b = ek1;
    uint8_t *hkeys_b = ek1 + (uint32_t)240U;
    uint8_t tmp_iv[16U] = { 0U };
    uint32_t len = iv_len / (uint32_t)16U;
    uint32_t bytes_len = len * (uint32_t)16U;
    uint8_t *iv_b = iv;
    memcpy(tmp_iv, iv + bytes_len, iv_len % (uint32_t)16U * sizeof (uint8_t));
    uint64_t
    uu____0 = compute_iv_stdcall(iv_b, (uint64_t)iv_len, (uint64_t)len, tmp_iv, tmp_iv, hkeys_b);
    uint8_t *inout_b = scratch_b;
    uint8_t *abytes_b = scratch_b + (uint32_t)16U;
    uint8_t *scratch_b1 = scratch_b + (uint32_t)32U;
    uint32_t plain_len_ = (uint32_t)(uint64_t)plain_len / (uint32_t)16U * (uint32_t)16U;
    uint32_t auth_len_ = (uint32_t)(uint64_t)ad_len / (uint32_t)16U * (uint32_t)16U;
    uint8_t *plain_b_ = plain;
    uint8_t *out_b_ = cipher;
    uint8_t *auth_b_ = ad;
    memcpy(inout_b,
      plain + plain_len_,
      (uint32_t)(uint64_t)plain_len % (uint32_t)16U * sizeof (uint8_t));
    memcpy(abytes_b,
      ad + auth_len_,
      (uint32_t)(uint64_t)ad_len % (uint32_t)16U * sizeof (uint8_t));
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
      scrut2 =
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
      scrut2 =
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
    memcpy(cipher + (uint32_t)(uint64_t)plain_len / (uint32_t)16U * (uint32_t)16U,
      inout_b,
      (uint32_t)(uint64_t)plain_len % (uint32_t)16U * sizeof (uint8_t));
    r = EverCrypt_Error_Success;
  }
  return EverCrypt_Error_Success;
  #else
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "EverCrypt was compiled on a system which doesn\'t support Vale");
  KRML_HOST_EXIT(255U);
  #endif
}

EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_expand_aes128_gcm(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
)
{
  bool has_pclmulqdq = EverCrypt_AutoConfig2_has_pclmulqdq();
  bool has_avx = EverCrypt_AutoConfig2_has_avx();
  bool has_sse = EverCrypt_AutoConfig2_has_sse();
  bool has_movbe = EverCrypt_AutoConfig2_has_movbe();
  bool has_aesni = EverCrypt_AutoConfig2_has_aesni();
  #if HACL_CAN_COMPILE_VALE
  if (has_aesni && has_pclmulqdq && has_avx && has_sse && has_movbe)
  {
    uint8_t ek[480U] = { 0U };
    uint8_t *keys_b0 = ek;
    uint8_t *hkeys_b0 = ek + (uint32_t)176U;
    uint64_t scrut0 = aes128_key_expansion(k, keys_b0);
    uint64_t scrut1 = aes128_keyhash_init(keys_b0, hkeys_b0);
    EverCrypt_AEAD_state_s p = { .impl = Spec_Cipher_Expansion_Vale_AES128, .ek = ek };
    EverCrypt_AEAD_state_s *s = &p;
    EverCrypt_Error_error_code r;
    if (s == NULL)
    {
      r = EverCrypt_Error_InvalidKey;
    }
    else if (iv_len == (uint32_t)0U)
    {
      r = EverCrypt_Error_InvalidIVLength;
    }
    else
    {
      EverCrypt_AEAD_state_s scrut = *s;
      uint8_t *ek0 = scrut.ek;
      uint8_t *scratch_b = ek0 + (uint32_t)304U;
      uint8_t *ek1 = ek0;
      uint8_t *keys_b = ek1;
      uint8_t *hkeys_b = ek1 + (uint32_t)176U;
      uint8_t tmp_iv[16U] = { 0U };
      uint32_t len = iv_len / (uint32_t)16U;
      uint32_t bytes_len = len * (uint32_t)16U;
      uint8_t *iv_b = iv;
      memcpy(tmp_iv, iv + bytes_len, iv_len % (uint32_t)16U * sizeof (uint8_t));
      uint64_t
      uu____0 = compute_iv_stdcall(iv_b, (uint64_t)iv_len, (uint64_t)len, tmp_iv, tmp_iv, hkeys_b);
      uint8_t *inout_b = scratch_b;
      uint8_t *abytes_b = scratch_b + (uint32_t)16U;
      uint8_t *scratch_b1 = scratch_b + (uint32_t)32U;
      uint32_t plain_len_ = (uint32_t)(uint64_t)plain_len / (uint32_t)16U * (uint32_t)16U;
      uint32_t auth_len_ = (uint32_t)(uint64_t)ad_len / (uint32_t)16U * (uint32_t)16U;
      uint8_t *plain_b_ = plain;
      uint8_t *out_b_ = cipher;
      uint8_t *auth_b_ = ad;
      memcpy(inout_b,
        plain + plain_len_,
        (uint32_t)(uint64_t)plain_len % (uint32_t)16U * sizeof (uint8_t));
      memcpy(abytes_b,
        ad + auth_len_,
        (uint32_t)(uint64_t)ad_len % (uint32_t)16U * sizeof (uint8_t));
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
        scrut2 =
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
        scrut2 =
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
      memcpy(cipher + (uint32_t)(uint64_t)plain_len / (uint32_t)16U * (uint32_t)16U,
        inout_b,
        (uint32_t)(uint64_t)plain_len % (uint32_t)16U * sizeof (uint8_t));
      r = EverCrypt_Error_Success;
    }
    return EverCrypt_Error_Success;
  }
  #endif
  return EverCrypt_Error_UnsupportedAlgorithm;
}

EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_expand_aes256_gcm(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
)
{
  bool has_pclmulqdq = EverCrypt_AutoConfig2_has_pclmulqdq();
  bool has_avx = EverCrypt_AutoConfig2_has_avx();
  bool has_sse = EverCrypt_AutoConfig2_has_sse();
  bool has_movbe = EverCrypt_AutoConfig2_has_movbe();
  bool has_aesni = EverCrypt_AutoConfig2_has_aesni();
  #if HACL_CAN_COMPILE_VALE
  if (has_aesni && has_pclmulqdq && has_avx && has_sse && has_movbe)
  {
    uint8_t ek[544U] = { 0U };
    uint8_t *keys_b0 = ek;
    uint8_t *hkeys_b0 = ek + (uint32_t)240U;
    uint64_t scrut0 = aes256_key_expansion(k, keys_b0);
    uint64_t scrut1 = aes256_keyhash_init(keys_b0, hkeys_b0);
    EverCrypt_AEAD_state_s p = { .impl = Spec_Cipher_Expansion_Vale_AES256, .ek = ek };
    EverCrypt_AEAD_state_s *s = &p;
    EverCrypt_Error_error_code r;
    if (s == NULL)
    {
      r = EverCrypt_Error_InvalidKey;
    }
    else if (iv_len == (uint32_t)0U)
    {
      r = EverCrypt_Error_InvalidIVLength;
    }
    else
    {
      EverCrypt_AEAD_state_s scrut = *s;
      uint8_t *ek0 = scrut.ek;
      uint8_t *scratch_b = ek0 + (uint32_t)368U;
      uint8_t *ek1 = ek0;
      uint8_t *keys_b = ek1;
      uint8_t *hkeys_b = ek1 + (uint32_t)240U;
      uint8_t tmp_iv[16U] = { 0U };
      uint32_t len = iv_len / (uint32_t)16U;
      uint32_t bytes_len = len * (uint32_t)16U;
      uint8_t *iv_b = iv;
      memcpy(tmp_iv, iv + bytes_len, iv_len % (uint32_t)16U * sizeof (uint8_t));
      uint64_t
      uu____0 = compute_iv_stdcall(iv_b, (uint64_t)iv_len, (uint64_t)len, tmp_iv, tmp_iv, hkeys_b);
      uint8_t *inout_b = scratch_b;
      uint8_t *abytes_b = scratch_b + (uint32_t)16U;
      uint8_t *scratch_b1 = scratch_b + (uint32_t)32U;
      uint32_t plain_len_ = (uint32_t)(uint64_t)plain_len / (uint32_t)16U * (uint32_t)16U;
      uint32_t auth_len_ = (uint32_t)(uint64_t)ad_len / (uint32_t)16U * (uint32_t)16U;
      uint8_t *plain_b_ = plain;
      uint8_t *out_b_ = cipher;
      uint8_t *auth_b_ = ad;
      memcpy(inout_b,
        plain + plain_len_,
        (uint32_t)(uint64_t)plain_len % (uint32_t)16U * sizeof (uint8_t));
      memcpy(abytes_b,
        ad + auth_len_,
        (uint32_t)(uint64_t)ad_len % (uint32_t)16U * sizeof (uint8_t));
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
        scrut2 =
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
        scrut2 =
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
      memcpy(cipher + (uint32_t)(uint64_t)plain_len / (uint32_t)16U * (uint32_t)16U,
        inout_b,
        (uint32_t)(uint64_t)plain_len % (uint32_t)16U * sizeof (uint8_t));
      r = EverCrypt_Error_Success;
    }
    return EverCrypt_Error_Success;
  }
  #endif
  return EverCrypt_Error_UnsupportedAlgorithm;
}

EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_expand_chacha20_poly1305(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
)
{
  uint8_t ek[32U] = { 0U };
  EverCrypt_AEAD_state_s p = { .impl = Spec_Cipher_Expansion_Hacl_CHACHA20, .ek = ek };
  memcpy(ek, k, (uint32_t)32U * sizeof (uint8_t));
  EverCrypt_AEAD_state_s *s = &p;
  EverCrypt_AEAD_state_s scrut = *s;
  uint8_t *ek0 = scrut.ek;
  EverCrypt_Chacha20Poly1305_aead_encrypt(ek0, iv, ad_len, ad, plain_len, plain, cipher, tag);
  return EverCrypt_Error_Success;
}

EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_expand(
  Spec_Agile_AEAD_alg a,
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
)
{
  switch (a)
  {
    case Spec_Agile_AEAD_AES128_GCM:
      {
        return
          EverCrypt_AEAD_encrypt_expand_aes128_gcm(k,
            iv,
            iv_len,
            ad,
            ad_len,
            plain,
            plain_len,
            cipher,
            tag);
      }
    case Spec_Agile_AEAD_AES256_GCM:
      {
        return
          EverCrypt_AEAD_encrypt_expand_aes256_gcm(k,
            iv,
            iv_len,
            ad,
            ad_len,
            plain,
            plain_len,
            cipher,
            tag);
      }
    case Spec_Agile_AEAD_CHACHA20_POLY1305:
      {
        return
          EverCrypt_AEAD_encrypt_expand_chacha20_poly1305(k,
            iv,
            iv_len,
            ad,
            ad_len,
            plain,
            plain_len,
            cipher,
            tag);
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static EverCrypt_Error_error_code
decrypt_aes128_gcm(
  EverCrypt_AEAD_state_s *s,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
)
{
  #if HACL_CAN_COMPILE_VALE
  if (s == NULL)
  {
    return EverCrypt_Error_InvalidKey;
  }
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
  memcpy(tmp_iv, iv + bytes_len, iv_len % (uint32_t)16U * sizeof (uint8_t));
  uint64_t
  uu____0 = compute_iv_stdcall(iv_b, (uint64_t)iv_len, (uint64_t)len, tmp_iv, tmp_iv, hkeys_b);
  uint8_t *inout_b = scratch_b;
  uint8_t *abytes_b = scratch_b + (uint32_t)16U;
  uint8_t *scratch_b1 = scratch_b + (uint32_t)32U;
  uint32_t cipher_len_ = (uint32_t)(uint64_t)cipher_len / (uint32_t)16U * (uint32_t)16U;
  uint32_t auth_len_ = (uint32_t)(uint64_t)ad_len / (uint32_t)16U * (uint32_t)16U;
  uint8_t *cipher_b_ = cipher;
  uint8_t *out_b_ = dst;
  uint8_t *auth_b_ = ad;
  memcpy(inout_b,
    cipher + cipher_len_,
    (uint32_t)(uint64_t)cipher_len % (uint32_t)16U * sizeof (uint8_t));
  memcpy(abytes_b,
    ad + auth_len_,
    (uint32_t)(uint64_t)ad_len % (uint32_t)16U * sizeof (uint8_t));
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
    (uint32_t)(uint64_t)cipher_len % (uint32_t)16U * sizeof (uint8_t));
  uint64_t r = c;
  if (r == (uint64_t)0U)
  {
    return EverCrypt_Error_Success;
  }
  return EverCrypt_Error_AuthenticationFailure;
  #else
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "statically unreachable");
  KRML_HOST_EXIT(255U);
  #endif
}

static EverCrypt_Error_error_code
decrypt_aes256_gcm(
  EverCrypt_AEAD_state_s *s,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
)
{
  #if HACL_CAN_COMPILE_VALE
  if (s == NULL)
  {
    return EverCrypt_Error_InvalidKey;
  }
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
  memcpy(tmp_iv, iv + bytes_len, iv_len % (uint32_t)16U * sizeof (uint8_t));
  uint64_t
  uu____0 = compute_iv_stdcall(iv_b, (uint64_t)iv_len, (uint64_t)len, tmp_iv, tmp_iv, hkeys_b);
  uint8_t *inout_b = scratch_b;
  uint8_t *abytes_b = scratch_b + (uint32_t)16U;
  uint8_t *scratch_b1 = scratch_b + (uint32_t)32U;
  uint32_t cipher_len_ = (uint32_t)(uint64_t)cipher_len / (uint32_t)16U * (uint32_t)16U;
  uint32_t auth_len_ = (uint32_t)(uint64_t)ad_len / (uint32_t)16U * (uint32_t)16U;
  uint8_t *cipher_b_ = cipher;
  uint8_t *out_b_ = dst;
  uint8_t *auth_b_ = ad;
  memcpy(inout_b,
    cipher + cipher_len_,
    (uint32_t)(uint64_t)cipher_len % (uint32_t)16U * sizeof (uint8_t));
  memcpy(abytes_b,
    ad + auth_len_,
    (uint32_t)(uint64_t)ad_len % (uint32_t)16U * sizeof (uint8_t));
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
    (uint32_t)(uint64_t)cipher_len % (uint32_t)16U * sizeof (uint8_t));
  uint64_t r = c;
  if (r == (uint64_t)0U)
  {
    return EverCrypt_Error_Success;
  }
  return EverCrypt_Error_AuthenticationFailure;
  #else
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "statically unreachable");
  KRML_HOST_EXIT(255U);
  #endif
}

static EverCrypt_Error_error_code
decrypt_chacha20_poly1305(
  EverCrypt_AEAD_state_s *s,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
)
{
  if (s == NULL)
  {
    return EverCrypt_Error_InvalidKey;
  }
  if (iv_len != (uint32_t)12U)
  {
    return EverCrypt_Error_InvalidIVLength;
  }
  EverCrypt_AEAD_state_s scrut = *s;
  uint8_t *ek = scrut.ek;
  uint32_t
  r = EverCrypt_Chacha20Poly1305_aead_decrypt(ek, iv, ad_len, ad, cipher_len, dst, cipher, tag);
  if (r == (uint32_t)0U)
  {
    return EverCrypt_Error_Success;
  }
  return EverCrypt_Error_AuthenticationFailure;
}

EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt(
  EverCrypt_AEAD_state_s *s,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
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
  Spec_Cipher_Expansion_impl i = scrut.impl;
  switch (i)
  {
    case Spec_Cipher_Expansion_Vale_AES128:
      {
        return decrypt_aes128_gcm(s, iv, iv_len, ad, ad_len, cipher, cipher_len, tag, dst);
      }
    case Spec_Cipher_Expansion_Vale_AES256:
      {
        return decrypt_aes256_gcm(s, iv, iv_len, ad, ad_len, cipher, cipher_len, tag, dst);
      }
    case Spec_Cipher_Expansion_Hacl_CHACHA20:
      {
        return decrypt_chacha20_poly1305(s, iv, iv_len, ad, ad_len, cipher, cipher_len, tag, dst);
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

/*
WARNING: this function doesn't perform any dynamic
  hardware check. You MUST make sure your hardware supports the
  implementation of AESGCM. Besides, this function was not designed
  for cross-compilation: if you compile it on a system which doesn't
  support Vale, it will compile it to a function which makes the
  program exit.
*/
EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_expand_aes128_gcm_no_check(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
)
{
  #if HACL_CAN_COMPILE_VALE
  uint8_t ek[480U] = { 0U };
  uint8_t *keys_b0 = ek;
  uint8_t *hkeys_b0 = ek + (uint32_t)176U;
  uint64_t scrut = aes128_key_expansion(k, keys_b0);
  uint64_t scrut0 = aes128_keyhash_init(keys_b0, hkeys_b0);
  EverCrypt_AEAD_state_s p = { .impl = Spec_Cipher_Expansion_Vale_AES128, .ek = ek };
  EverCrypt_AEAD_state_s *s = &p;
  if (s == NULL)
  {
    return EverCrypt_Error_InvalidKey;
  }
  if (iv_len == (uint32_t)0U)
  {
    return EverCrypt_Error_InvalidIVLength;
  }
  EverCrypt_AEAD_state_s scrut1 = *s;
  uint8_t *ek0 = scrut1.ek;
  uint8_t *scratch_b = ek0 + (uint32_t)304U;
  uint8_t *ek1 = ek0;
  uint8_t *keys_b = ek1;
  uint8_t *hkeys_b = ek1 + (uint32_t)176U;
  uint8_t tmp_iv[16U] = { 0U };
  uint32_t len = iv_len / (uint32_t)16U;
  uint32_t bytes_len = len * (uint32_t)16U;
  uint8_t *iv_b = iv;
  memcpy(tmp_iv, iv + bytes_len, iv_len % (uint32_t)16U * sizeof (uint8_t));
  uint64_t
  uu____0 = compute_iv_stdcall(iv_b, (uint64_t)iv_len, (uint64_t)len, tmp_iv, tmp_iv, hkeys_b);
  uint8_t *inout_b = scratch_b;
  uint8_t *abytes_b = scratch_b + (uint32_t)16U;
  uint8_t *scratch_b1 = scratch_b + (uint32_t)32U;
  uint32_t cipher_len_ = (uint32_t)(uint64_t)cipher_len / (uint32_t)16U * (uint32_t)16U;
  uint32_t auth_len_ = (uint32_t)(uint64_t)ad_len / (uint32_t)16U * (uint32_t)16U;
  uint8_t *cipher_b_ = cipher;
  uint8_t *out_b_ = dst;
  uint8_t *auth_b_ = ad;
  memcpy(inout_b,
    cipher + cipher_len_,
    (uint32_t)(uint64_t)cipher_len % (uint32_t)16U * sizeof (uint8_t));
  memcpy(abytes_b,
    ad + auth_len_,
    (uint32_t)(uint64_t)ad_len % (uint32_t)16U * sizeof (uint8_t));
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
    scrut2 =
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
    uint64_t c0 = scrut2;
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
    scrut2 =
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
    uint64_t c0 = scrut2;
    c = c0;
  }
  memcpy(dst + (uint32_t)(uint64_t)cipher_len / (uint32_t)16U * (uint32_t)16U,
    inout_b,
    (uint32_t)(uint64_t)cipher_len % (uint32_t)16U * sizeof (uint8_t));
  uint64_t r = c;
  if (r == (uint64_t)0U)
  {
    return EverCrypt_Error_Success;
  }
  return EverCrypt_Error_AuthenticationFailure;
  #else
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "EverCrypt was compiled on a system which doesn\'t support Vale");
  KRML_HOST_EXIT(255U);
  #endif
}

/*
WARNING: this function doesn't perform any dynamic
  hardware check. You MUST make sure your hardware supports the
  implementation of AESGCM. Besides, this function was not designed
  for cross-compilation: if you compile it on a system which doesn't
  support Vale, it will compile it to a function which makes the
  program exit.
*/
EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_expand_aes256_gcm_no_check(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
)
{
  #if HACL_CAN_COMPILE_VALE
  uint8_t ek[544U] = { 0U };
  uint8_t *keys_b0 = ek;
  uint8_t *hkeys_b0 = ek + (uint32_t)240U;
  uint64_t scrut = aes256_key_expansion(k, keys_b0);
  uint64_t scrut0 = aes256_keyhash_init(keys_b0, hkeys_b0);
  EverCrypt_AEAD_state_s p = { .impl = Spec_Cipher_Expansion_Vale_AES256, .ek = ek };
  EverCrypt_AEAD_state_s *s = &p;
  if (s == NULL)
  {
    return EverCrypt_Error_InvalidKey;
  }
  if (iv_len == (uint32_t)0U)
  {
    return EverCrypt_Error_InvalidIVLength;
  }
  EverCrypt_AEAD_state_s scrut1 = *s;
  uint8_t *ek0 = scrut1.ek;
  uint8_t *scratch_b = ek0 + (uint32_t)368U;
  uint8_t *ek1 = ek0;
  uint8_t *keys_b = ek1;
  uint8_t *hkeys_b = ek1 + (uint32_t)240U;
  uint8_t tmp_iv[16U] = { 0U };
  uint32_t len = iv_len / (uint32_t)16U;
  uint32_t bytes_len = len * (uint32_t)16U;
  uint8_t *iv_b = iv;
  memcpy(tmp_iv, iv + bytes_len, iv_len % (uint32_t)16U * sizeof (uint8_t));
  uint64_t
  uu____0 = compute_iv_stdcall(iv_b, (uint64_t)iv_len, (uint64_t)len, tmp_iv, tmp_iv, hkeys_b);
  uint8_t *inout_b = scratch_b;
  uint8_t *abytes_b = scratch_b + (uint32_t)16U;
  uint8_t *scratch_b1 = scratch_b + (uint32_t)32U;
  uint32_t cipher_len_ = (uint32_t)(uint64_t)cipher_len / (uint32_t)16U * (uint32_t)16U;
  uint32_t auth_len_ = (uint32_t)(uint64_t)ad_len / (uint32_t)16U * (uint32_t)16U;
  uint8_t *cipher_b_ = cipher;
  uint8_t *out_b_ = dst;
  uint8_t *auth_b_ = ad;
  memcpy(inout_b,
    cipher + cipher_len_,
    (uint32_t)(uint64_t)cipher_len % (uint32_t)16U * sizeof (uint8_t));
  memcpy(abytes_b,
    ad + auth_len_,
    (uint32_t)(uint64_t)ad_len % (uint32_t)16U * sizeof (uint8_t));
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
    scrut2 =
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
    uint64_t c0 = scrut2;
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
    scrut2 =
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
    uint64_t c0 = scrut2;
    c = c0;
  }
  memcpy(dst + (uint32_t)(uint64_t)cipher_len / (uint32_t)16U * (uint32_t)16U,
    inout_b,
    (uint32_t)(uint64_t)cipher_len % (uint32_t)16U * sizeof (uint8_t));
  uint64_t r = c;
  if (r == (uint64_t)0U)
  {
    return EverCrypt_Error_Success;
  }
  return EverCrypt_Error_AuthenticationFailure;
  #else
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "EverCrypt was compiled on a system which doesn\'t support Vale");
  KRML_HOST_EXIT(255U);
  #endif
}

EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_expand_aes128_gcm(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
)
{
  bool has_pclmulqdq = EverCrypt_AutoConfig2_has_pclmulqdq();
  bool has_avx = EverCrypt_AutoConfig2_has_avx();
  bool has_sse = EverCrypt_AutoConfig2_has_sse();
  bool has_movbe = EverCrypt_AutoConfig2_has_movbe();
  bool has_aesni = EverCrypt_AutoConfig2_has_aesni();
  #if HACL_CAN_COMPILE_VALE
  if (has_aesni && has_pclmulqdq && has_avx && has_sse && has_movbe)
  {
    uint8_t ek[480U] = { 0U };
    uint8_t *keys_b0 = ek;
    uint8_t *hkeys_b0 = ek + (uint32_t)176U;
    uint64_t scrut = aes128_key_expansion(k, keys_b0);
    uint64_t scrut0 = aes128_keyhash_init(keys_b0, hkeys_b0);
    EverCrypt_AEAD_state_s p = { .impl = Spec_Cipher_Expansion_Vale_AES128, .ek = ek };
    EverCrypt_AEAD_state_s *s = &p;
    if (s == NULL)
    {
      return EverCrypt_Error_InvalidKey;
    }
    else if (iv_len == (uint32_t)0U)
    {
      return EverCrypt_Error_InvalidIVLength;
    }
    else
    {
      EverCrypt_AEAD_state_s scrut1 = *s;
      uint8_t *ek0 = scrut1.ek;
      uint8_t *scratch_b = ek0 + (uint32_t)304U;
      uint8_t *ek1 = ek0;
      uint8_t *keys_b = ek1;
      uint8_t *hkeys_b = ek1 + (uint32_t)176U;
      uint8_t tmp_iv[16U] = { 0U };
      uint32_t len = iv_len / (uint32_t)16U;
      uint32_t bytes_len = len * (uint32_t)16U;
      uint8_t *iv_b = iv;
      memcpy(tmp_iv, iv + bytes_len, iv_len % (uint32_t)16U * sizeof (uint8_t));
      uint64_t
      uu____0 = compute_iv_stdcall(iv_b, (uint64_t)iv_len, (uint64_t)len, tmp_iv, tmp_iv, hkeys_b);
      uint8_t *inout_b = scratch_b;
      uint8_t *abytes_b = scratch_b + (uint32_t)16U;
      uint8_t *scratch_b1 = scratch_b + (uint32_t)32U;
      uint32_t cipher_len_ = (uint32_t)(uint64_t)cipher_len / (uint32_t)16U * (uint32_t)16U;
      uint32_t auth_len_ = (uint32_t)(uint64_t)ad_len / (uint32_t)16U * (uint32_t)16U;
      uint8_t *cipher_b_ = cipher;
      uint8_t *out_b_ = dst;
      uint8_t *auth_b_ = ad;
      memcpy(inout_b,
        cipher + cipher_len_,
        (uint32_t)(uint64_t)cipher_len % (uint32_t)16U * sizeof (uint8_t));
      memcpy(abytes_b,
        ad + auth_len_,
        (uint32_t)(uint64_t)ad_len % (uint32_t)16U * sizeof (uint8_t));
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
        scrut2 =
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
        uint64_t c0 = scrut2;
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
        scrut2 =
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
        uint64_t c0 = scrut2;
        c = c0;
      }
      memcpy(dst + (uint32_t)(uint64_t)cipher_len / (uint32_t)16U * (uint32_t)16U,
        inout_b,
        (uint32_t)(uint64_t)cipher_len % (uint32_t)16U * sizeof (uint8_t));
      uint64_t r = c;
      if (r == (uint64_t)0U)
      {
        return EverCrypt_Error_Success;
      }
      else
      {
        return EverCrypt_Error_AuthenticationFailure;
      }
    }
  }
  #endif
  return EverCrypt_Error_UnsupportedAlgorithm;
}

EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_expand_aes256_gcm(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
)
{
  bool has_pclmulqdq = EverCrypt_AutoConfig2_has_pclmulqdq();
  bool has_avx = EverCrypt_AutoConfig2_has_avx();
  bool has_sse = EverCrypt_AutoConfig2_has_sse();
  bool has_movbe = EverCrypt_AutoConfig2_has_movbe();
  bool has_aesni = EverCrypt_AutoConfig2_has_aesni();
  #if HACL_CAN_COMPILE_VALE
  if (has_aesni && has_pclmulqdq && has_avx && has_sse && has_movbe)
  {
    uint8_t ek[544U] = { 0U };
    uint8_t *keys_b0 = ek;
    uint8_t *hkeys_b0 = ek + (uint32_t)240U;
    uint64_t scrut = aes256_key_expansion(k, keys_b0);
    uint64_t scrut0 = aes256_keyhash_init(keys_b0, hkeys_b0);
    EverCrypt_AEAD_state_s p = { .impl = Spec_Cipher_Expansion_Vale_AES256, .ek = ek };
    EverCrypt_AEAD_state_s *s = &p;
    if (s == NULL)
    {
      return EverCrypt_Error_InvalidKey;
    }
    else if (iv_len == (uint32_t)0U)
    {
      return EverCrypt_Error_InvalidIVLength;
    }
    else
    {
      EverCrypt_AEAD_state_s scrut1 = *s;
      uint8_t *ek0 = scrut1.ek;
      uint8_t *scratch_b = ek0 + (uint32_t)368U;
      uint8_t *ek1 = ek0;
      uint8_t *keys_b = ek1;
      uint8_t *hkeys_b = ek1 + (uint32_t)240U;
      uint8_t tmp_iv[16U] = { 0U };
      uint32_t len = iv_len / (uint32_t)16U;
      uint32_t bytes_len = len * (uint32_t)16U;
      uint8_t *iv_b = iv;
      memcpy(tmp_iv, iv + bytes_len, iv_len % (uint32_t)16U * sizeof (uint8_t));
      uint64_t
      uu____0 = compute_iv_stdcall(iv_b, (uint64_t)iv_len, (uint64_t)len, tmp_iv, tmp_iv, hkeys_b);
      uint8_t *inout_b = scratch_b;
      uint8_t *abytes_b = scratch_b + (uint32_t)16U;
      uint8_t *scratch_b1 = scratch_b + (uint32_t)32U;
      uint32_t cipher_len_ = (uint32_t)(uint64_t)cipher_len / (uint32_t)16U * (uint32_t)16U;
      uint32_t auth_len_ = (uint32_t)(uint64_t)ad_len / (uint32_t)16U * (uint32_t)16U;
      uint8_t *cipher_b_ = cipher;
      uint8_t *out_b_ = dst;
      uint8_t *auth_b_ = ad;
      memcpy(inout_b,
        cipher + cipher_len_,
        (uint32_t)(uint64_t)cipher_len % (uint32_t)16U * sizeof (uint8_t));
      memcpy(abytes_b,
        ad + auth_len_,
        (uint32_t)(uint64_t)ad_len % (uint32_t)16U * sizeof (uint8_t));
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
        scrut2 =
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
        uint64_t c0 = scrut2;
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
        scrut2 =
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
        uint64_t c0 = scrut2;
        c = c0;
      }
      memcpy(dst + (uint32_t)(uint64_t)cipher_len / (uint32_t)16U * (uint32_t)16U,
        inout_b,
        (uint32_t)(uint64_t)cipher_len % (uint32_t)16U * sizeof (uint8_t));
      uint64_t r = c;
      if (r == (uint64_t)0U)
      {
        return EverCrypt_Error_Success;
      }
      else
      {
        return EverCrypt_Error_AuthenticationFailure;
      }
    }
  }
  #endif
  return EverCrypt_Error_UnsupportedAlgorithm;
}

EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_expand_chacha20_poly1305(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
)
{
  uint8_t ek[32U] = { 0U };
  EverCrypt_AEAD_state_s p = { .impl = Spec_Cipher_Expansion_Hacl_CHACHA20, .ek = ek };
  memcpy(ek, k, (uint32_t)32U * sizeof (uint8_t));
  EverCrypt_AEAD_state_s *s = &p;
  EverCrypt_Error_error_code
  r = decrypt_chacha20_poly1305(s, iv, iv_len, ad, ad_len, cipher, cipher_len, tag, dst);
  return r;
}

EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_expand(
  Spec_Agile_AEAD_alg a,
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
)
{
  switch (a)
  {
    case Spec_Agile_AEAD_AES128_GCM:
      {
        return
          EverCrypt_AEAD_decrypt_expand_aes128_gcm(k,
            iv,
            iv_len,
            ad,
            ad_len,
            cipher,
            cipher_len,
            tag,
            dst);
      }
    case Spec_Agile_AEAD_AES256_GCM:
      {
        return
          EverCrypt_AEAD_decrypt_expand_aes256_gcm(k,
            iv,
            iv_len,
            ad,
            ad_len,
            cipher,
            cipher_len,
            tag,
            dst);
      }
    case Spec_Agile_AEAD_CHACHA20_POLY1305:
      {
        return
          EverCrypt_AEAD_decrypt_expand_chacha20_poly1305(k,
            iv,
            iv_len,
            ad,
            ad_len,
            cipher,
            cipher_len,
            tag,
            dst);
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

void EverCrypt_AEAD_free(EverCrypt_AEAD_state_s *s)
{
  EverCrypt_AEAD_state_s scrut = *s;
  uint8_t *ek = scrut.ek;
  KRML_HOST_FREE(ek);
  KRML_HOST_FREE(s);
}

