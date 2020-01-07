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

typedef struct EverCrypt_AEAD_state_s_s
{
  Spec_Cipher_Expansion_impl impl;
  u8 *ek;
}
EverCrypt_AEAD_state_s;

bool EverCrypt_AEAD_uu___is_Ek(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s projectee)
{
  return true;
}

Spec_Cipher_Expansion_impl
EverCrypt_AEAD___proj__Ek__item__impl(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s projectee)
{
  return projectee.impl;
}

u8
*EverCrypt_AEAD___proj__Ek__item__ek(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s projectee)
{
  return projectee.ek;
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
EverCrypt_AEAD_create_in_chacha20_poly1305(EverCrypt_AEAD_state_s **dst, u8 *k1)
{
  u8 *ek = KRML_HOST_CALLOC((u32)32U, sizeof (u8));
  KRML_CHECK_SIZE(sizeof (EverCrypt_AEAD_state_s), (u32)1U);
  {
    EverCrypt_AEAD_state_s *p = KRML_HOST_MALLOC(sizeof (EverCrypt_AEAD_state_s));
    p[0U] = ((EverCrypt_AEAD_state_s){ .impl = Spec_Cipher_Expansion_Hacl_CHACHA20, .ek = ek });
    memcpy(ek, k1, (u32)32U * sizeof k1[0U]);
    dst[0U] = p;
    return EverCrypt_Error_Success;
  }
}

static EverCrypt_Error_error_code
EverCrypt_AEAD_create_in_aes128_gcm(EverCrypt_AEAD_state_s **dst, u8 *k1)
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
    u8 *ek = KRML_HOST_CALLOC((u32)480U, sizeof (u8));
    u8 *keys_b = ek;
    u8 *hkeys_b = ek + (u32)176U;
    u64 scrut = aes128_key_expansion(k1, keys_b);
    u64 scrut0 = aes128_keyhash_init(keys_b, hkeys_b);
    KRML_CHECK_SIZE(sizeof (EverCrypt_AEAD_state_s), (u32)1U);
    {
      EverCrypt_AEAD_state_s *p = KRML_HOST_MALLOC(sizeof (EverCrypt_AEAD_state_s));
      p[0U] = ((EverCrypt_AEAD_state_s){ .impl = Spec_Cipher_Expansion_Vale_AES128, .ek = ek });
      *dst = p;
      return EverCrypt_Error_Success;
    }
  }
  #endif
  return EverCrypt_Error_UnsupportedAlgorithm;
}

static EverCrypt_Error_error_code
EverCrypt_AEAD_create_in_aes256_gcm(EverCrypt_AEAD_state_s **dst, u8 *k1)
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
    u8 *ek = KRML_HOST_CALLOC((u32)544U, sizeof (u8));
    u8 *keys_b = ek;
    u8 *hkeys_b = ek + (u32)240U;
    u64 scrut = aes256_key_expansion(k1, keys_b);
    u64 scrut0 = aes256_keyhash_init(keys_b, hkeys_b);
    KRML_CHECK_SIZE(sizeof (EverCrypt_AEAD_state_s), (u32)1U);
    {
      EverCrypt_AEAD_state_s *p = KRML_HOST_MALLOC(sizeof (EverCrypt_AEAD_state_s));
      p[0U] = ((EverCrypt_AEAD_state_s){ .impl = Spec_Cipher_Expansion_Vale_AES256, .ek = ek });
      *dst = p;
      return EverCrypt_Error_Success;
    }
  }
  #endif
  return EverCrypt_Error_UnsupportedAlgorithm;
}

EverCrypt_Error_error_code
EverCrypt_AEAD_create_in(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s **dst, u8 *k1)
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

static EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_aes128_gcm(
  EverCrypt_AEAD_state_s *s,
  u8 *iv,
  u32 iv_len,
  u8 *ad,
  u32 ad_len,
  u8 *plain,
  u32 plain_len,
  u8 *cipher,
  u8 *tag
)
{
  if (s == NULL)
  {
    return EverCrypt_Error_InvalidKey;
  }
  else
  {
    Spec_Agile_AEAD_alg a = EverCrypt_AEAD_alg_of_vale_impl(Spec_Cipher_Expansion_Vale_AES128);
    if (iv_len == (u32)0U)
    {
      return EverCrypt_Error_InvalidIVLength;
    }
    else
    {
      EverCrypt_AEAD_state_s scrut = *s;
      u8 *ek = scrut.ek;
      u8 *scratch_b = ek + (u32)304U;
      u8 *ek1 = ek;
      u8 *keys_b = ek1;
      u8 *hkeys_b = ek1 + (u32)176U;
      u8 tmp_iv[16U] = { 0U };
      u32 len = iv_len / (u32)16U;
      u32 bytes_len = len * (u32)16U;
      u8 *iv_b = iv;
      memcpy(tmp_iv, iv + bytes_len, iv_len % (u32)16U * sizeof iv[0U]);
      {
        u64 uu____0 = compute_iv_stdcall(iv_b, (u64)iv_len, (u64)len, tmp_iv, tmp_iv, hkeys_b);
        u8 *inout_b = scratch_b;
        u8 *abytes_b = scratch_b + (u32)16U;
        u8 *scratch_b1 = scratch_b + (u32)32U;
        u32 plain_len_ = (u32)(u64)plain_len / (u32)16U * (u32)16U;
        u32 auth_len_ = (u32)(u64)ad_len / (u32)16U * (u32)16U;
        u8 *plain_b_ = plain;
        u8 *out_b_ = cipher;
        u8 *auth_b_ = ad;
        memcpy(inout_b, plain + plain_len_, (u32)(u64)plain_len % (u32)16U * sizeof plain[0U]);
        memcpy(abytes_b, ad + auth_len_, (u32)(u64)ad_len % (u32)16U * sizeof ad[0U]);
        {
          u64 len128x6 = (u64)plain_len / (u64)96U * (u64)96U;
          if (len128x6 / (u64)16U >= (u64)18U)
          {
            u64 len128_num = (u64)plain_len / (u64)16U * (u64)16U - len128x6;
            u8 *in128x6_b = plain_b_;
            u8 *out128x6_b = out_b_;
            u8 *in128_b = plain_b_ + (u32)len128x6;
            u8 *out128_b = out_b_ + (u32)len128x6;
            u64 auth_num = (u64)ad_len / (u64)16U;
            u64 len128x6_ = len128x6 / (u64)16U;
            u64 len128_num_ = len128_num / (u64)16U;
            u64
            scrut0 =
              gcm128_encrypt_opt(auth_b_,
                (u64)ad_len,
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
                (u64)plain_len,
                scratch_b1,
                tag);
          }
          else
          {
            u32 len128x61 = (u32)0U;
            u64 len128_num = (u64)plain_len / (u64)16U * (u64)16U;
            u8 *in128x6_b = plain_b_;
            u8 *out128x6_b = out_b_;
            u8 *in128_b = plain_b_ + len128x61;
            u8 *out128_b = out_b_ + len128x61;
            u64 auth_num = (u64)ad_len / (u64)16U;
            u64 len128_num_ = len128_num / (u64)16U;
            u64 len128x6_ = (u64)0U;
            u64
            scrut0 =
              gcm128_encrypt_opt(auth_b_,
                (u64)ad_len,
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
                (u64)plain_len,
                scratch_b1,
                tag);
          }
          memcpy(cipher + (u32)(u64)plain_len / (u32)16U * (u32)16U,
            inout_b,
            (u32)(u64)plain_len % (u32)16U * sizeof inout_b[0U]);
          return EverCrypt_Error_Success;
        }
      }
    }
  }
}

static EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_aes256_gcm(
  EverCrypt_AEAD_state_s *s,
  u8 *iv,
  u32 iv_len,
  u8 *ad,
  u32 ad_len,
  u8 *plain,
  u32 plain_len,
  u8 *cipher,
  u8 *tag
)
{
  if (s == NULL)
  {
    return EverCrypt_Error_InvalidKey;
  }
  else
  {
    Spec_Agile_AEAD_alg a = EverCrypt_AEAD_alg_of_vale_impl(Spec_Cipher_Expansion_Vale_AES256);
    if (iv_len == (u32)0U)
    {
      return EverCrypt_Error_InvalidIVLength;
    }
    else
    {
      EverCrypt_AEAD_state_s scrut = *s;
      u8 *ek = scrut.ek;
      u8 *scratch_b = ek + (u32)368U;
      u8 *ek1 = ek;
      u8 *keys_b = ek1;
      u8 *hkeys_b = ek1 + (u32)240U;
      u8 tmp_iv[16U] = { 0U };
      u32 len = iv_len / (u32)16U;
      u32 bytes_len = len * (u32)16U;
      u8 *iv_b = iv;
      memcpy(tmp_iv, iv + bytes_len, iv_len % (u32)16U * sizeof iv[0U]);
      {
        u64 uu____0 = compute_iv_stdcall(iv_b, (u64)iv_len, (u64)len, tmp_iv, tmp_iv, hkeys_b);
        u8 *inout_b = scratch_b;
        u8 *abytes_b = scratch_b + (u32)16U;
        u8 *scratch_b1 = scratch_b + (u32)32U;
        u32 plain_len_ = (u32)(u64)plain_len / (u32)16U * (u32)16U;
        u32 auth_len_ = (u32)(u64)ad_len / (u32)16U * (u32)16U;
        u8 *plain_b_ = plain;
        u8 *out_b_ = cipher;
        u8 *auth_b_ = ad;
        memcpy(inout_b, plain + plain_len_, (u32)(u64)plain_len % (u32)16U * sizeof plain[0U]);
        memcpy(abytes_b, ad + auth_len_, (u32)(u64)ad_len % (u32)16U * sizeof ad[0U]);
        {
          u64 len128x6 = (u64)plain_len / (u64)96U * (u64)96U;
          if (len128x6 / (u64)16U >= (u64)18U)
          {
            u64 len128_num = (u64)plain_len / (u64)16U * (u64)16U - len128x6;
            u8 *in128x6_b = plain_b_;
            u8 *out128x6_b = out_b_;
            u8 *in128_b = plain_b_ + (u32)len128x6;
            u8 *out128_b = out_b_ + (u32)len128x6;
            u64 auth_num = (u64)ad_len / (u64)16U;
            u64 len128x6_ = len128x6 / (u64)16U;
            u64 len128_num_ = len128_num / (u64)16U;
            u64
            scrut0 =
              gcm256_encrypt_opt(auth_b_,
                (u64)ad_len,
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
                (u64)plain_len,
                scratch_b1,
                tag);
          }
          else
          {
            u32 len128x61 = (u32)0U;
            u64 len128_num = (u64)plain_len / (u64)16U * (u64)16U;
            u8 *in128x6_b = plain_b_;
            u8 *out128x6_b = out_b_;
            u8 *in128_b = plain_b_ + len128x61;
            u8 *out128_b = out_b_ + len128x61;
            u64 auth_num = (u64)ad_len / (u64)16U;
            u64 len128_num_ = len128_num / (u64)16U;
            u64 len128x6_ = (u64)0U;
            u64
            scrut0 =
              gcm256_encrypt_opt(auth_b_,
                (u64)ad_len,
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
                (u64)plain_len,
                scratch_b1,
                tag);
          }
          memcpy(cipher + (u32)(u64)plain_len / (u32)16U * (u32)16U,
            inout_b,
            (u32)(u64)plain_len % (u32)16U * sizeof inout_b[0U]);
          return EverCrypt_Error_Success;
        }
      }
    }
  }
}

EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt(
  EverCrypt_AEAD_state_s *s,
  u8 *iv,
  u32 iv_len,
  u8 *ad,
  u32 ad_len,
  u8 *plain,
  u32 plain_len,
  u8 *cipher,
  u8 *tag
)
{
  if (s == NULL)
  {
    return EverCrypt_Error_InvalidKey;
  }
  else
  {
    EverCrypt_AEAD_state_s scrut = *s;
    Spec_Cipher_Expansion_impl i1 = scrut.impl;
    u8 *ek = scrut.ek;
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
              cipher,
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
              cipher,
              tag);
        }
      case Spec_Cipher_Expansion_Hacl_CHACHA20:
        {
          if (iv_len != (u32)12U)
          {
            return EverCrypt_Error_InvalidIVLength;
          }
          else
          {
            EverCrypt_Chacha20Poly1305_aead_encrypt(ek,
              iv,
              ad_len,
              ad,
              plain_len,
              plain,
              cipher,
              tag);
            return EverCrypt_Error_Success;
          }
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
  }
}

static EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_aes128_gcm(
  EverCrypt_AEAD_state_s *s,
  u8 *iv,
  u32 iv_len,
  u8 *ad,
  u32 ad_len,
  u8 *cipher,
  u32 cipher_len,
  u8 *tag,
  u8 *dst
)
{
  if (s == NULL)
  {
    return EverCrypt_Error_InvalidKey;
  }
  else if (iv_len == (u32)0U)
  {
    return EverCrypt_Error_InvalidIVLength;
  }
  else
  {
    Spec_Agile_AEAD_alg a = EverCrypt_AEAD_alg_of_vale_impl(Spec_Cipher_Expansion_Vale_AES128);
    EverCrypt_AEAD_state_s scrut = *s;
    u8 *ek = scrut.ek;
    u8 *scratch_b = ek + (u32)304U;
    u8 *ek1 = ek;
    u8 *keys_b = ek1;
    u8 *hkeys_b = ek1 + (u32)176U;
    u8 tmp_iv[16U] = { 0U };
    u32 len = iv_len / (u32)16U;
    u32 bytes_len = len * (u32)16U;
    u8 *iv_b = iv;
    memcpy(tmp_iv, iv + bytes_len, iv_len % (u32)16U * sizeof iv[0U]);
    {
      u64 uu____0 = compute_iv_stdcall(iv_b, (u64)iv_len, (u64)len, tmp_iv, tmp_iv, hkeys_b);
      u8 *inout_b = scratch_b;
      u8 *abytes_b = scratch_b + (u32)16U;
      u8 *scratch_b1 = scratch_b + (u32)32U;
      u32 cipher_len_ = (u32)(u64)cipher_len / (u32)16U * (u32)16U;
      u32 auth_len_ = (u32)(u64)ad_len / (u32)16U * (u32)16U;
      u8 *cipher_b_ = cipher;
      u8 *out_b_ = dst;
      u8 *auth_b_ = ad;
      memcpy(inout_b, cipher + cipher_len_, (u32)(u64)cipher_len % (u32)16U * sizeof cipher[0U]);
      memcpy(abytes_b, ad + auth_len_, (u32)(u64)ad_len % (u32)16U * sizeof ad[0U]);
      {
        u64 len128x6 = (u64)cipher_len / (u64)96U * (u64)96U;
        u64 c;
        if (len128x6 / (u64)16U >= (u64)6U)
        {
          u64 len128_num = (u64)cipher_len / (u64)16U * (u64)16U - len128x6;
          u8 *in128x6_b = cipher_b_;
          u8 *out128x6_b = out_b_;
          u8 *in128_b = cipher_b_ + (u32)len128x6;
          u8 *out128_b = out_b_ + (u32)len128x6;
          u64 auth_num = (u64)ad_len / (u64)16U;
          u64 len128x6_ = len128x6 / (u64)16U;
          u64 len128_num_ = len128_num / (u64)16U;
          u64
          scrut0 =
            gcm128_decrypt_opt(auth_b_,
              (u64)ad_len,
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
              (u64)cipher_len,
              scratch_b1,
              tag);
          u64 c0 = scrut0;
          c = c0;
        }
        else
        {
          u32 len128x61 = (u32)0U;
          u64 len128_num = (u64)cipher_len / (u64)16U * (u64)16U;
          u8 *in128x6_b = cipher_b_;
          u8 *out128x6_b = out_b_;
          u8 *in128_b = cipher_b_ + len128x61;
          u8 *out128_b = out_b_ + len128x61;
          u64 auth_num = (u64)ad_len / (u64)16U;
          u64 len128_num_ = len128_num / (u64)16U;
          u64 len128x6_ = (u64)0U;
          u64
          scrut0 =
            gcm128_decrypt_opt(auth_b_,
              (u64)ad_len,
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
              (u64)cipher_len,
              scratch_b1,
              tag);
          u64 c0 = scrut0;
          c = c0;
        }
        memcpy(dst + (u32)(u64)cipher_len / (u32)16U * (u32)16U,
          inout_b,
          (u32)(u64)cipher_len % (u32)16U * sizeof inout_b[0U]);
        {
          u64 r = c;
          if (r == (u64)0U)
          {
            return EverCrypt_Error_Success;
          }
          else
          {
            return EverCrypt_Error_AuthenticationFailure;
          }
        }
      }
    }
  }
}

static EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_aes256_gcm(
  EverCrypt_AEAD_state_s *s,
  u8 *iv,
  u32 iv_len,
  u8 *ad,
  u32 ad_len,
  u8 *cipher,
  u32 cipher_len,
  u8 *tag,
  u8 *dst
)
{
  if (s == NULL)
  {
    return EverCrypt_Error_InvalidKey;
  }
  else if (iv_len == (u32)0U)
  {
    return EverCrypt_Error_InvalidIVLength;
  }
  else
  {
    Spec_Agile_AEAD_alg a = EverCrypt_AEAD_alg_of_vale_impl(Spec_Cipher_Expansion_Vale_AES256);
    EverCrypt_AEAD_state_s scrut = *s;
    u8 *ek = scrut.ek;
    u8 *scratch_b = ek + (u32)368U;
    u8 *ek1 = ek;
    u8 *keys_b = ek1;
    u8 *hkeys_b = ek1 + (u32)240U;
    u8 tmp_iv[16U] = { 0U };
    u32 len = iv_len / (u32)16U;
    u32 bytes_len = len * (u32)16U;
    u8 *iv_b = iv;
    memcpy(tmp_iv, iv + bytes_len, iv_len % (u32)16U * sizeof iv[0U]);
    {
      u64 uu____0 = compute_iv_stdcall(iv_b, (u64)iv_len, (u64)len, tmp_iv, tmp_iv, hkeys_b);
      u8 *inout_b = scratch_b;
      u8 *abytes_b = scratch_b + (u32)16U;
      u8 *scratch_b1 = scratch_b + (u32)32U;
      u32 cipher_len_ = (u32)(u64)cipher_len / (u32)16U * (u32)16U;
      u32 auth_len_ = (u32)(u64)ad_len / (u32)16U * (u32)16U;
      u8 *cipher_b_ = cipher;
      u8 *out_b_ = dst;
      u8 *auth_b_ = ad;
      memcpy(inout_b, cipher + cipher_len_, (u32)(u64)cipher_len % (u32)16U * sizeof cipher[0U]);
      memcpy(abytes_b, ad + auth_len_, (u32)(u64)ad_len % (u32)16U * sizeof ad[0U]);
      {
        u64 len128x6 = (u64)cipher_len / (u64)96U * (u64)96U;
        u64 c;
        if (len128x6 / (u64)16U >= (u64)6U)
        {
          u64 len128_num = (u64)cipher_len / (u64)16U * (u64)16U - len128x6;
          u8 *in128x6_b = cipher_b_;
          u8 *out128x6_b = out_b_;
          u8 *in128_b = cipher_b_ + (u32)len128x6;
          u8 *out128_b = out_b_ + (u32)len128x6;
          u64 auth_num = (u64)ad_len / (u64)16U;
          u64 len128x6_ = len128x6 / (u64)16U;
          u64 len128_num_ = len128_num / (u64)16U;
          u64
          scrut0 =
            gcm256_decrypt_opt(auth_b_,
              (u64)ad_len,
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
              (u64)cipher_len,
              scratch_b1,
              tag);
          u64 c0 = scrut0;
          c = c0;
        }
        else
        {
          u32 len128x61 = (u32)0U;
          u64 len128_num = (u64)cipher_len / (u64)16U * (u64)16U;
          u8 *in128x6_b = cipher_b_;
          u8 *out128x6_b = out_b_;
          u8 *in128_b = cipher_b_ + len128x61;
          u8 *out128_b = out_b_ + len128x61;
          u64 auth_num = (u64)ad_len / (u64)16U;
          u64 len128_num_ = len128_num / (u64)16U;
          u64 len128x6_ = (u64)0U;
          u64
          scrut0 =
            gcm256_decrypt_opt(auth_b_,
              (u64)ad_len,
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
              (u64)cipher_len,
              scratch_b1,
              tag);
          u64 c0 = scrut0;
          c = c0;
        }
        memcpy(dst + (u32)(u64)cipher_len / (u32)16U * (u32)16U,
          inout_b,
          (u32)(u64)cipher_len % (u32)16U * sizeof inout_b[0U]);
        {
          u64 r = c;
          if (r == (u64)0U)
          {
            return EverCrypt_Error_Success;
          }
          else
          {
            return EverCrypt_Error_AuthenticationFailure;
          }
        }
      }
    }
  }
}

EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt(
  EverCrypt_AEAD_state_s *s,
  u8 *iv,
  u32 iv_len,
  u8 *ad,
  u32 ad_len,
  u8 *cipher,
  u32 cipher_len,
  u8 *tag,
  u8 *dst
)
{
  if (s == NULL)
  {
    return EverCrypt_Error_InvalidKey;
  }
  else
  {
    EverCrypt_AEAD_state_s scrut = *s;
    Spec_Cipher_Expansion_impl i1 = scrut.impl;
    u8 *ek = scrut.ek;
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
              cipher,
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
              cipher,
              cipher_len,
              tag,
              dst);
        }
      case Spec_Cipher_Expansion_Hacl_CHACHA20:
        {
          if (iv_len != (u32)12U)
          {
            return EverCrypt_Error_InvalidIVLength;
          }
          else
          {
            u32
            r =
              EverCrypt_Chacha20Poly1305_aead_decrypt(ek,
                iv,
                ad_len,
                ad,
                cipher_len,
                dst,
                cipher,
                tag);
            if (r == (u32)0U)
            {
              return EverCrypt_Error_Success;
            }
            else
            {
              return EverCrypt_Error_AuthenticationFailure;
            }
          }
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
  }
}

void EverCrypt_AEAD_free(EverCrypt_AEAD_state_s *s)
{
  EverCrypt_AEAD_state_s scrut = *s;
  u8 *ek = scrut.ek;
  KRML_HOST_FREE(ek);
  KRML_HOST_FREE(s);
}

