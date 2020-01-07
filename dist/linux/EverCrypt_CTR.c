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


#include "EverCrypt_CTR.h"

typedef struct EverCrypt_CTR_state_s_s
{
  Spec_Cipher_Expansion_impl i;
  u8 *iv;
  u32 iv_len;
  u8 *xkey;
  u32 ctr;
}
EverCrypt_CTR_state_s;

bool
EverCrypt_CTR_uu___is_State(Spec_Agile_Cipher_cipher_alg a, EverCrypt_CTR_state_s projectee)
{
  return true;
}

Spec_Cipher_Expansion_impl
EverCrypt_CTR___proj__State__item__i(
  Spec_Agile_Cipher_cipher_alg a,
  EverCrypt_CTR_state_s projectee
)
{
  return projectee.i;
}

u8
*EverCrypt_CTR___proj__State__item__iv(
  Spec_Agile_Cipher_cipher_alg a,
  EverCrypt_CTR_state_s projectee
)
{
  return projectee.iv;
}

u32
EverCrypt_CTR___proj__State__item__iv_len(
  Spec_Agile_Cipher_cipher_alg a,
  EverCrypt_CTR_state_s projectee
)
{
  return projectee.iv_len;
}

u8
*EverCrypt_CTR___proj__State__item__xkey(
  Spec_Agile_Cipher_cipher_alg a,
  EverCrypt_CTR_state_s projectee
)
{
  return projectee.xkey;
}

u32
EverCrypt_CTR___proj__State__item__ctr(
  Spec_Agile_Cipher_cipher_alg a,
  EverCrypt_CTR_state_s projectee
)
{
  return projectee.ctr;
}

u8 EverCrypt_CTR_xor8(u8 a, u8 b)
{
  return a ^ b;
}

Spec_Agile_Cipher_cipher_alg EverCrypt_CTR_alg_of_state(EverCrypt_CTR_state_s *s)
{
  EverCrypt_CTR_state_s scrut = *s;
  Spec_Cipher_Expansion_impl i1 = scrut.i;
  return Spec_Cipher_Expansion_cipher_alg_of_impl(i1);
}

static Spec_Cipher_Expansion_impl
EverCrypt_CTR_vale_impl_of_alg(Spec_Agile_Cipher_cipher_alg a)
{
  switch (a)
  {
    case Spec_Agile_Cipher_AES128:
      {
        return Spec_Cipher_Expansion_Vale_AES128;
      }
    case Spec_Agile_Cipher_AES256:
      {
        return Spec_Cipher_Expansion_Vale_AES256;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

EverCrypt_Error_error_code
EverCrypt_CTR_create_in(
  Spec_Agile_Cipher_cipher_alg a,
  EverCrypt_CTR_state_s **dst,
  u8 *k1,
  u8 *iv,
  u32 iv_len,
  u32 c
)
{
  switch (a)
  {
    case Spec_Agile_Cipher_AES128:
      {
        bool has_aesni1 = EverCrypt_AutoConfig2_has_aesni();
        bool has_pclmulqdq1 = EverCrypt_AutoConfig2_has_pclmulqdq();
        bool has_avx1 = EverCrypt_AutoConfig2_has_avx();
        bool has_sse1 = EverCrypt_AutoConfig2_has_sse();
        if (iv_len < (u32)12U)
        {
          return EverCrypt_Error_InvalidIVLength;
        }
        else
        {
          #if EVERCRYPT_TARGETCONFIG_X64
          if (has_aesni1 && has_pclmulqdq1 && has_avx1 && has_sse1)
          {
            u8 *ek = KRML_HOST_CALLOC((u32)304U, sizeof (u8));
            u8 *keys_b = ek;
            u8 *hkeys_b = ek + (u32)176U;
            u64 scrut = aes128_key_expansion(k1, keys_b);
            u64 scrut0 = aes128_keyhash_init(keys_b, hkeys_b);
            u8 *iv_ = KRML_HOST_CALLOC((u32)16U, sizeof (u8));
            memcpy(iv_, iv, iv_len * sizeof iv[0U]);
            KRML_CHECK_SIZE(sizeof (EverCrypt_CTR_state_s), (u32)1U);
            {
              EverCrypt_CTR_state_s *p = KRML_HOST_MALLOC(sizeof (EverCrypt_CTR_state_s));
              p[0U]
              =
                (
                  (EverCrypt_CTR_state_s){
                    .i = EverCrypt_CTR_vale_impl_of_alg(Spec_Cipher_Expansion_cipher_alg_of_impl(Spec_Cipher_Expansion_Vale_AES128)),
                    .iv = iv_,
                    .iv_len = iv_len,
                    .xkey = ek,
                    .ctr = c
                  }
                );
              *dst = p;
              return EverCrypt_Error_Success;
            }
          }
          #endif
          return EverCrypt_Error_UnsupportedAlgorithm;
        }
        break;
      }
    case Spec_Agile_Cipher_AES256:
      {
        bool has_aesni1 = EverCrypt_AutoConfig2_has_aesni();
        bool has_pclmulqdq1 = EverCrypt_AutoConfig2_has_pclmulqdq();
        bool has_avx1 = EverCrypt_AutoConfig2_has_avx();
        bool has_sse1 = EverCrypt_AutoConfig2_has_sse();
        if (iv_len < (u32)12U)
        {
          return EverCrypt_Error_InvalidIVLength;
        }
        else
        {
          #if EVERCRYPT_TARGETCONFIG_X64
          if (has_aesni1 && has_pclmulqdq1 && has_avx1 && has_sse1)
          {
            u8 *ek = KRML_HOST_CALLOC((u32)368U, sizeof (u8));
            u8 *keys_b = ek;
            u8 *hkeys_b = ek + (u32)240U;
            u64 scrut = aes256_key_expansion(k1, keys_b);
            u64 scrut0 = aes256_keyhash_init(keys_b, hkeys_b);
            u8 *iv_ = KRML_HOST_CALLOC((u32)16U, sizeof (u8));
            memcpy(iv_, iv, iv_len * sizeof iv[0U]);
            KRML_CHECK_SIZE(sizeof (EverCrypt_CTR_state_s), (u32)1U);
            {
              EverCrypt_CTR_state_s *p = KRML_HOST_MALLOC(sizeof (EverCrypt_CTR_state_s));
              p[0U]
              =
                (
                  (EverCrypt_CTR_state_s){
                    .i = EverCrypt_CTR_vale_impl_of_alg(Spec_Cipher_Expansion_cipher_alg_of_impl(Spec_Cipher_Expansion_Vale_AES256)),
                    .iv = iv_,
                    .iv_len = iv_len,
                    .xkey = ek,
                    .ctr = c
                  }
                );
              *dst = p;
              return EverCrypt_Error_Success;
            }
          }
          #endif
          return EverCrypt_Error_UnsupportedAlgorithm;
        }
        break;
      }
    case Spec_Agile_Cipher_CHACHA20:
      {
        u8 *ek = KRML_HOST_CALLOC((u32)32U, sizeof (u8));
        memcpy(ek, k1, (u32)32U * sizeof k1[0U]);
        KRML_CHECK_SIZE(sizeof (u8), iv_len);
        {
          u8 *iv_ = KRML_HOST_CALLOC(iv_len, sizeof (u8));
          memcpy(iv_, iv, iv_len * sizeof iv[0U]);
          KRML_CHECK_SIZE(sizeof (EverCrypt_CTR_state_s), (u32)1U);
          {
            EverCrypt_CTR_state_s *p = KRML_HOST_MALLOC(sizeof (EverCrypt_CTR_state_s));
            p[0U]
            =
              (
                (EverCrypt_CTR_state_s){
                  .i = Spec_Cipher_Expansion_Hacl_CHACHA20,
                  .iv = iv_,
                  .iv_len = (u32)12U,
                  .xkey = ek,
                  .ctr = c
                }
              );
            *dst = p;
            return EverCrypt_Error_Success;
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

void EverCrypt_CTR_init(EverCrypt_CTR_state_s *p, u8 *k1, u8 *iv, u32 iv_len, u32 c)
{
  EverCrypt_CTR_state_s scrut0 = *p;
  u8 *ek = scrut0.xkey;
  u8 *iv_ = scrut0.iv;
  Spec_Cipher_Expansion_impl i1 = scrut0.i;
  memcpy(iv_, iv, iv_len * sizeof iv[0U]);
  switch (i1)
  {
    case Spec_Cipher_Expansion_Vale_AES128:
      {
        u8 *keys_b = ek;
        u8 *hkeys_b = ek + (u32)176U;
        u64 scrut = aes128_key_expansion(k1, keys_b);
        u64 scrut1 = aes128_keyhash_init(keys_b, hkeys_b);
        break;
      }
    case Spec_Cipher_Expansion_Vale_AES256:
      {
        u8 *keys_b = ek;
        u8 *hkeys_b = ek + (u32)240U;
        u64 scrut = aes256_key_expansion(k1, keys_b);
        u64 scrut1 = aes256_keyhash_init(keys_b, hkeys_b);
        break;
      }
    case Spec_Cipher_Expansion_Hacl_CHACHA20:
      {
        memcpy(ek, k1, (u32)32U * sizeof k1[0U]);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  *p = ((EverCrypt_CTR_state_s){ .i = i1, .iv = iv_, .iv_len = iv_len, .xkey = ek, .ctr = c });
}

void EverCrypt_CTR_update_block(EverCrypt_CTR_state_s *p, u8 *dst, u8 *src)
{
  EverCrypt_CTR_state_s scrut0 = *p;
  Spec_Cipher_Expansion_impl i1 = scrut0.i;
  u8 *iv = scrut0.iv;
  u8 *ek = scrut0.xkey;
  u32 c01 = scrut0.ctr;
  EverCrypt_CTR_state_s scrut1;
  u32 c020;
  u8 *ek10;
  u32 iv_len10;
  u8 *iv10;
  EverCrypt_CTR_state_s scrut2;
  u32 c02;
  u8 *ek1;
  u32 iv_len1;
  u8 *iv1;
  switch (i1)
  {
    case Spec_Cipher_Expansion_Vale_AES128:
      {
        scrut1 = *p;
        c020 = scrut1.ctr;
        ek10 = scrut1.xkey;
        iv_len10 = scrut1.iv_len;
        iv10 = scrut1.iv;
        {
          u8 ctr_block1[16U] = { 0U };
          uint128_t uu____0;
          uint128_t c;
          u8 *uu____1;
          memcpy(ctr_block1, iv10, iv_len10 * sizeof iv10[0U]);
          uu____0 = load128_be(ctr_block1);
          c = uu____0 + (uint128_t)(u64)c020;
          store128_le(ctr_block1, c);
          uu____1 = ek10;
          {
            u8 inout_b[16U] = { 0U };
            u32 num_blocks = (u32)(u64)16U / (u32)16U;
            u32 num_bytes_ = num_blocks * (u32)16U;
            u8 *in_b_ = src;
            u8 *out_b_ = dst;
            u64 scrut;
            u32 c4;
            memcpy(inout_b, src + num_bytes_, (u32)(u64)16U % (u32)16U * sizeof src[0U]);
            scrut =
              gctr128_bytes(in_b_,
                (u64)16U,
                out_b_,
                inout_b,
                uu____1,
                ctr_block1,
                (u64)num_blocks);
            memcpy(dst + num_bytes_, inout_b, (u32)(u64)16U % (u32)16U * sizeof inout_b[0U]);
            c4 = c020 + (u32)1U;
            *p
            =
              (
                (EverCrypt_CTR_state_s){
                  .i = Spec_Cipher_Expansion_Vale_AES128,
                  .iv = iv10,
                  .iv_len = iv_len10,
                  .xkey = ek10,
                  .ctr = c4
                }
              );
          }
        }
        break;
      }
    case Spec_Cipher_Expansion_Vale_AES256:
      {
        scrut2 = *p;
        c02 = scrut2.ctr;
        ek1 = scrut2.xkey;
        iv_len1 = scrut2.iv_len;
        iv1 = scrut2.iv;
        {
          u8 ctr_block1[16U] = { 0U };
          uint128_t uu____2;
          uint128_t c;
          u8 *uu____3;
          memcpy(ctr_block1, iv1, iv_len1 * sizeof iv1[0U]);
          uu____2 = load128_be(ctr_block1);
          c = uu____2 + (uint128_t)(u64)c02;
          store128_le(ctr_block1, c);
          uu____3 = ek1;
          {
            u8 inout_b[16U] = { 0U };
            u32 num_blocks = (u32)(u64)16U / (u32)16U;
            u32 num_bytes_ = num_blocks * (u32)16U;
            u8 *in_b_ = src;
            u8 *out_b_ = dst;
            u64 scrut;
            u32 c4;
            memcpy(inout_b, src + num_bytes_, (u32)(u64)16U % (u32)16U * sizeof src[0U]);
            scrut =
              gctr256_bytes(in_b_,
                (u64)16U,
                out_b_,
                inout_b,
                uu____3,
                ctr_block1,
                (u64)num_blocks);
            memcpy(dst + num_bytes_, inout_b, (u32)(u64)16U % (u32)16U * sizeof inout_b[0U]);
            c4 = c02 + (u32)1U;
            *p
            =
              (
                (EverCrypt_CTR_state_s){
                  .i = Spec_Cipher_Expansion_Vale_AES256,
                  .iv = iv1,
                  .iv_len = iv_len1,
                  .xkey = ek1,
                  .ctr = c4
                }
              );
          }
        }
        break;
      }
    case Spec_Cipher_Expansion_Hacl_CHACHA20:
      {
        u32 ctx[16U] = { 0U };
        Hacl_Impl_Chacha20_chacha20_init(ctx, ek, iv, (u32)0U);
        Hacl_Impl_Chacha20_chacha20_encrypt_block(ctx, dst, c01, src);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

void EverCrypt_CTR_free(EverCrypt_CTR_state_s *p)
{
  EverCrypt_CTR_state_s scrut = *p;
  u8 *iv = scrut.iv;
  u8 *ek = scrut.xkey;
  KRML_HOST_FREE(iv);
  KRML_HOST_FREE(ek);
  KRML_HOST_FREE(p);
}

