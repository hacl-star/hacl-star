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
  uint8_t *iv;
  uint32_t iv_len;
  uint8_t *xkey;
  uint32_t ctr;
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

uint8_t
*EverCrypt_CTR___proj__State__item__iv(
  Spec_Agile_Cipher_cipher_alg a,
  EverCrypt_CTR_state_s projectee
)
{
  return projectee.iv;
}

uint32_t
EverCrypt_CTR___proj__State__item__iv_len(
  Spec_Agile_Cipher_cipher_alg a,
  EverCrypt_CTR_state_s projectee
)
{
  return projectee.iv_len;
}

uint8_t
*EverCrypt_CTR___proj__State__item__xkey(
  Spec_Agile_Cipher_cipher_alg a,
  EverCrypt_CTR_state_s projectee
)
{
  return projectee.xkey;
}

uint32_t
EverCrypt_CTR___proj__State__item__ctr(
  Spec_Agile_Cipher_cipher_alg a,
  EverCrypt_CTR_state_s projectee
)
{
  return projectee.ctr;
}

uint8_t EverCrypt_CTR_xor8(uint8_t a, uint8_t b)
{
  return a ^ b;
}

Spec_Agile_Cipher_cipher_alg EverCrypt_CTR_alg_of_state(EverCrypt_CTR_state_s *s)
{
  EverCrypt_CTR_state_s scrut = *s;
  Spec_Cipher_Expansion_impl i = scrut.i;
  return Spec_Cipher_Expansion_cipher_alg_of_impl(i);
}

static Spec_Cipher_Expansion_impl vale_impl_of_alg(Spec_Agile_Cipher_cipher_alg a)
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
        KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

EverCrypt_Error_error_code
EverCrypt_CTR_create_in(
  Spec_Agile_Cipher_cipher_alg a,
  EverCrypt_CTR_state_s **dst,
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint32_t c
)
{
  switch (a)
  {
    case Spec_Agile_Cipher_AES128:
      {
        bool has_aesni = EverCrypt_AutoConfig2_has_aesni();
        bool has_pclmulqdq = EverCrypt_AutoConfig2_has_pclmulqdq();
        bool has_avx = EverCrypt_AutoConfig2_has_avx();
        bool has_sse = EverCrypt_AutoConfig2_has_sse();
        if (iv_len < (uint32_t)12U)
        {
          return EverCrypt_Error_InvalidIVLength;
        }
        #if EVERCRYPT_TARGETCONFIG_X64
        if (has_aesni && has_pclmulqdq && has_avx && has_sse)
        {
          uint8_t *ek = KRML_HOST_CALLOC((uint32_t)304U, sizeof (uint8_t));
          uint8_t *keys_b = ek;
          uint8_t *hkeys_b = ek + (uint32_t)176U;
          uint64_t scrut = aes128_key_expansion(k, keys_b);
          uint64_t scrut0 = aes128_keyhash_init(keys_b, hkeys_b);
          uint8_t *iv_ = KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint8_t));
          memcpy(iv_, iv, iv_len * sizeof (iv[0U]));
          {
            EverCrypt_CTR_state_s lit;
            lit.i =
              vale_impl_of_alg(Spec_Cipher_Expansion_cipher_alg_of_impl(Spec_Cipher_Expansion_Vale_AES128));
            lit.iv = iv_;
            lit.iv_len = iv_len;
            lit.xkey = ek;
            lit.ctr = c;
            KRML_CHECK_SIZE(sizeof (EverCrypt_CTR_state_s), (uint32_t)1U);
            {
              EverCrypt_CTR_state_s *p = KRML_HOST_MALLOC(sizeof (EverCrypt_CTR_state_s));
              p[0U] = lit;
              *dst = p;
              return EverCrypt_Error_Success;
            }
          }
        }
        #endif
        return EverCrypt_Error_UnsupportedAlgorithm;
      }
    case Spec_Agile_Cipher_AES256:
      {
        bool has_aesni = EverCrypt_AutoConfig2_has_aesni();
        bool has_pclmulqdq = EverCrypt_AutoConfig2_has_pclmulqdq();
        bool has_avx = EverCrypt_AutoConfig2_has_avx();
        bool has_sse = EverCrypt_AutoConfig2_has_sse();
        if (iv_len < (uint32_t)12U)
        {
          return EverCrypt_Error_InvalidIVLength;
        }
        #if EVERCRYPT_TARGETCONFIG_X64
        if (has_aesni && has_pclmulqdq && has_avx && has_sse)
        {
          uint8_t *ek = KRML_HOST_CALLOC((uint32_t)368U, sizeof (uint8_t));
          uint8_t *keys_b = ek;
          uint8_t *hkeys_b = ek + (uint32_t)240U;
          uint64_t scrut = aes256_key_expansion(k, keys_b);
          uint64_t scrut0 = aes256_keyhash_init(keys_b, hkeys_b);
          uint8_t *iv_ = KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint8_t));
          memcpy(iv_, iv, iv_len * sizeof (iv[0U]));
          {
            EverCrypt_CTR_state_s lit;
            lit.i =
              vale_impl_of_alg(Spec_Cipher_Expansion_cipher_alg_of_impl(Spec_Cipher_Expansion_Vale_AES256));
            lit.iv = iv_;
            lit.iv_len = iv_len;
            lit.xkey = ek;
            lit.ctr = c;
            KRML_CHECK_SIZE(sizeof (EverCrypt_CTR_state_s), (uint32_t)1U);
            {
              EverCrypt_CTR_state_s *p = KRML_HOST_MALLOC(sizeof (EverCrypt_CTR_state_s));
              p[0U] = lit;
              *dst = p;
              return EverCrypt_Error_Success;
            }
          }
        }
        #endif
        return EverCrypt_Error_UnsupportedAlgorithm;
      }
    case Spec_Agile_Cipher_CHACHA20:
      {
        uint8_t *ek = KRML_HOST_CALLOC((uint32_t)32U, sizeof (uint8_t));
        memcpy(ek, k, (uint32_t)32U * sizeof (k[0U]));
        KRML_CHECK_SIZE(sizeof (uint8_t), iv_len);
        {
          uint8_t *iv_ = KRML_HOST_CALLOC(iv_len, sizeof (uint8_t));
          memcpy(iv_, iv, iv_len * sizeof (iv[0U]));
          {
            EverCrypt_CTR_state_s lit;
            lit.i = Spec_Cipher_Expansion_Hacl_CHACHA20;
            lit.iv = iv_;
            lit.iv_len = (uint32_t)12U;
            lit.xkey = ek;
            lit.ctr = c;
            KRML_CHECK_SIZE(sizeof (EverCrypt_CTR_state_s), (uint32_t)1U);
            {
              EverCrypt_CTR_state_s *p = KRML_HOST_MALLOC(sizeof (EverCrypt_CTR_state_s));
              p[0U] = lit;
              *dst = p;
              return EverCrypt_Error_Success;
            }
          }
        }
        break;
      }
    default:
      {
        KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

void
EverCrypt_CTR_init(
  EverCrypt_CTR_state_s *p,
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint32_t c
)
{
  EverCrypt_CTR_state_s scrut0 = *p;
  uint8_t *ek = scrut0.xkey;
  uint8_t *iv_ = scrut0.iv;
  Spec_Cipher_Expansion_impl i = scrut0.i;
  memcpy(iv_, iv, iv_len * sizeof (iv[0U]));
  switch (i)
  {
    case Spec_Cipher_Expansion_Vale_AES128:
      {
        #if EVERCRYPT_TARGETCONFIG_X64
        uint8_t *keys_b = ek;
        uint8_t *hkeys_b = ek + (uint32_t)176U;
        uint64_t scrut = aes128_key_expansion(k, keys_b);
        uint64_t scrut1 = aes128_keyhash_init(keys_b, hkeys_b);
        #endif
        break;
      }
    case Spec_Cipher_Expansion_Vale_AES256:
      {
        #if EVERCRYPT_TARGETCONFIG_X64
        uint8_t *keys_b = ek;
        uint8_t *hkeys_b = ek + (uint32_t)240U;
        uint64_t scrut = aes256_key_expansion(k, keys_b);
        uint64_t scrut1 = aes256_keyhash_init(keys_b, hkeys_b);
        #endif
        break;
      }
    case Spec_Cipher_Expansion_Hacl_CHACHA20:
      {
        memcpy(ek, k, (uint32_t)32U * sizeof (k[0U]));
        break;
      }
    default:
      {
        KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  {
    EverCrypt_CTR_state_s lit;
    lit.i = i;
    lit.iv = iv_;
    lit.iv_len = iv_len;
    lit.xkey = ek;
    lit.ctr = c;
    *p = lit;
  }
}

void EverCrypt_CTR_update_block(EverCrypt_CTR_state_s *p, uint8_t *dst, uint8_t *src)
{
  EverCrypt_CTR_state_s scrut0 = *p;
  Spec_Cipher_Expansion_impl i = scrut0.i;
  uint8_t *iv = scrut0.iv;
  uint8_t *ek = scrut0.xkey;
  uint32_t c0 = scrut0.ctr;
  switch (i)
  {
    case Spec_Cipher_Expansion_Vale_AES128:
      {
        #if EVERCRYPT_TARGETCONFIG_X64
        EverCrypt_CTR_state_s scrut1 = *p;
        uint32_t c01 = scrut1.ctr;
        uint8_t *ek1 = scrut1.xkey;
        uint32_t iv_len1 = scrut1.iv_len;
        uint8_t *iv1 = scrut1.iv;
        uint8_t ctr_block[16U] = { 0U };
        FStar_UInt128_uint128 uu____0;
        FStar_UInt128_uint128 c;
        uint8_t *uu____1;
        memcpy(ctr_block, iv1, iv_len1 * sizeof (iv1[0U]));
        uu____0 = load128_be(ctr_block);
        c = FStar_UInt128_add_mod(uu____0, FStar_UInt128_uint64_to_uint128((uint64_t)c01));
        store128_le(ctr_block, c);
        uu____1 = ek1;
        {
          uint8_t inout_b[16U] = { 0U };
          uint32_t num_blocks = (uint32_t)(uint64_t)16U / (uint32_t)16U;
          uint32_t num_bytes_ = num_blocks * (uint32_t)16U;
          uint8_t *in_b_ = src;
          uint8_t *out_b_ = dst;
          uint64_t scrut;
          uint32_t c1;
          memcpy(inout_b,
            src + num_bytes_,
            (uint32_t)(uint64_t)16U % (uint32_t)16U * sizeof (src[0U]));
          scrut =
            gctr128_bytes(in_b_,
              (uint64_t)16U,
              out_b_,
              inout_b,
              uu____1,
              ctr_block,
              (uint64_t)num_blocks);
          memcpy(dst + num_bytes_,
            inout_b,
            (uint32_t)(uint64_t)16U % (uint32_t)16U * sizeof (inout_b[0U]));
          c1 = c01 + (uint32_t)1U;
          {
            EverCrypt_CTR_state_s lit;
            lit.i = Spec_Cipher_Expansion_Vale_AES128;
            lit.iv = iv1;
            lit.iv_len = iv_len1;
            lit.xkey = ek1;
            lit.ctr = c1;
            *p = lit;
          }
        }
        #endif
        break;
      }
    case Spec_Cipher_Expansion_Vale_AES256:
      {
        #if EVERCRYPT_TARGETCONFIG_X64
        EverCrypt_CTR_state_s scrut1 = *p;
        uint32_t c01 = scrut1.ctr;
        uint8_t *ek1 = scrut1.xkey;
        uint32_t iv_len1 = scrut1.iv_len;
        uint8_t *iv1 = scrut1.iv;
        uint8_t ctr_block[16U] = { 0U };
        FStar_UInt128_uint128 uu____2;
        FStar_UInt128_uint128 c;
        uint8_t *uu____3;
        memcpy(ctr_block, iv1, iv_len1 * sizeof (iv1[0U]));
        uu____2 = load128_be(ctr_block);
        c = FStar_UInt128_add_mod(uu____2, FStar_UInt128_uint64_to_uint128((uint64_t)c01));
        store128_le(ctr_block, c);
        uu____3 = ek1;
        {
          uint8_t inout_b[16U] = { 0U };
          uint32_t num_blocks = (uint32_t)(uint64_t)16U / (uint32_t)16U;
          uint32_t num_bytes_ = num_blocks * (uint32_t)16U;
          uint8_t *in_b_ = src;
          uint8_t *out_b_ = dst;
          uint64_t scrut;
          uint32_t c1;
          memcpy(inout_b,
            src + num_bytes_,
            (uint32_t)(uint64_t)16U % (uint32_t)16U * sizeof (src[0U]));
          scrut =
            gctr256_bytes(in_b_,
              (uint64_t)16U,
              out_b_,
              inout_b,
              uu____3,
              ctr_block,
              (uint64_t)num_blocks);
          memcpy(dst + num_bytes_,
            inout_b,
            (uint32_t)(uint64_t)16U % (uint32_t)16U * sizeof (inout_b[0U]));
          c1 = c01 + (uint32_t)1U;
          {
            EverCrypt_CTR_state_s lit;
            lit.i = Spec_Cipher_Expansion_Vale_AES256;
            lit.iv = iv1;
            lit.iv_len = iv_len1;
            lit.xkey = ek1;
            lit.ctr = c1;
            *p = lit;
          }
        }
        #endif
        break;
      }
    case Spec_Cipher_Expansion_Hacl_CHACHA20:
      {
        uint32_t ctx[16U] = { 0U };
        Hacl_Impl_Chacha20_chacha20_init(ctx, ek, iv, (uint32_t)0U);
        Hacl_Impl_Chacha20_chacha20_encrypt_block(ctx, dst, c0, src);
        break;
      }
    default:
      {
        KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

void EverCrypt_CTR_free(EverCrypt_CTR_state_s *p)
{
  EverCrypt_CTR_state_s scrut = *p;
  uint8_t *iv = scrut.iv;
  uint8_t *ek = scrut.xkey;
  KRML_HOST_FREE(iv);
  KRML_HOST_FREE(ek);
  KRML_HOST_FREE(p);
}

