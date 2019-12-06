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
  uint8_t *k1,
  uint8_t *iv,
  uint32_t iv_len,
  uint32_t c
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
        if (iv_len < (uint32_t)12U)
        {
          return EverCrypt_Error_InvalidIVLength;
        }
        #if EVERCRYPT_TARGETCONFIG_X64
        if (has_aesni1 && has_pclmulqdq1 && has_avx1 && has_sse1)
        {
          uint8_t *ek = KRML_HOST_CALLOC((uint32_t)304U, sizeof (uint8_t));
          uint8_t *keys_b = ek;
          uint8_t *hkeys_b = ek + (uint32_t)176U;
          uint64_t scrut = aes128_key_expansion(k1, keys_b);
          uint64_t scrut0 = aes128_keyhash_init(keys_b, hkeys_b);
          uint8_t *iv_ = KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint8_t));
          memcpy(iv_, iv, iv_len * sizeof iv[0U]);
          KRML_CHECK_SIZE(sizeof (EverCrypt_CTR_state_s), (uint32_t)1U);
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
        #endif
        return EverCrypt_Error_UnsupportedAlgorithm;
      }
    case Spec_Agile_Cipher_AES256:
      {
        bool has_aesni1 = EverCrypt_AutoConfig2_has_aesni();
        bool has_pclmulqdq1 = EverCrypt_AutoConfig2_has_pclmulqdq();
        bool has_avx1 = EverCrypt_AutoConfig2_has_avx();
        bool has_sse1 = EverCrypt_AutoConfig2_has_sse();
        if (iv_len < (uint32_t)12U)
        {
          return EverCrypt_Error_InvalidIVLength;
        }
        #if EVERCRYPT_TARGETCONFIG_X64
        if (has_aesni1 && has_pclmulqdq1 && has_avx1 && has_sse1)
        {
          uint8_t *ek = KRML_HOST_CALLOC((uint32_t)368U, sizeof (uint8_t));
          uint8_t *keys_b = ek;
          uint8_t *hkeys_b = ek + (uint32_t)240U;
          uint64_t scrut = aes256_key_expansion(k1, keys_b);
          uint64_t scrut0 = aes256_keyhash_init(keys_b, hkeys_b);
          uint8_t *iv_ = KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint8_t));
          memcpy(iv_, iv, iv_len * sizeof iv[0U]);
          KRML_CHECK_SIZE(sizeof (EverCrypt_CTR_state_s), (uint32_t)1U);
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
        #endif
        return EverCrypt_Error_UnsupportedAlgorithm;
      }
    case Spec_Agile_Cipher_CHACHA20:
      {
        uint8_t *ek = KRML_HOST_CALLOC((uint32_t)32U, sizeof (uint8_t));
        memcpy(ek, k1, (uint32_t)32U * sizeof k1[0U]);
        KRML_CHECK_SIZE(sizeof (uint8_t), iv_len);
        uint8_t *iv_ = KRML_HOST_CALLOC(iv_len, sizeof (uint8_t));
        memcpy(iv_, iv, iv_len * sizeof iv[0U]);
        KRML_CHECK_SIZE(sizeof (EverCrypt_CTR_state_s), (uint32_t)1U);
        EverCrypt_CTR_state_s *p = KRML_HOST_MALLOC(sizeof (EverCrypt_CTR_state_s));
        p[0U]
        =
          (
            (EverCrypt_CTR_state_s){
              .i = Spec_Cipher_Expansion_Hacl_CHACHA20,
              .iv = iv_,
              .iv_len = (uint32_t)12U,
              .xkey = ek,
              .ctr = c
            }
          );
        *dst = p;
        return EverCrypt_Error_Success;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

void
EverCrypt_CTR_init(
  EverCrypt_CTR_state_s *p,
  uint8_t *k1,
  uint8_t *iv,
  uint32_t iv_len,
  uint32_t c
)
{
  EverCrypt_CTR_state_s scrut0 = *p;
  uint8_t *ek = scrut0.xkey;
  uint8_t *iv_ = scrut0.iv;
  Spec_Cipher_Expansion_impl i1 = scrut0.i;
  memcpy(iv_, iv, iv_len * sizeof iv[0U]);
  switch (i1)
  {
    case Spec_Cipher_Expansion_Vale_AES128:
      {
        uint8_t *keys_b = ek;
        uint8_t *hkeys_b = ek + (uint32_t)176U;
        uint64_t scrut = aes128_key_expansion(k1, keys_b);
        uint64_t scrut1 = aes128_keyhash_init(keys_b, hkeys_b);
        break;
      }
    case Spec_Cipher_Expansion_Vale_AES256:
      {
        uint8_t *keys_b = ek;
        uint8_t *hkeys_b = ek + (uint32_t)240U;
        uint64_t scrut = aes256_key_expansion(k1, keys_b);
        uint64_t scrut1 = aes256_keyhash_init(keys_b, hkeys_b);
        break;
      }
    case Spec_Cipher_Expansion_Hacl_CHACHA20:
      {
        memcpy(ek, k1, (uint32_t)32U * sizeof k1[0U]);
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

void EverCrypt_CTR_update_block(EverCrypt_CTR_state_s *p, uint8_t *dst, uint8_t *src)
{
  EverCrypt_CTR_state_s scrut = *p;
  Spec_Cipher_Expansion_impl i1 = scrut.i;
  uint8_t *iv = scrut.iv;
  uint8_t *ek = scrut.xkey;
  uint32_t c01 = scrut.ctr;
  switch (i1)
  {
    case Spec_Cipher_Expansion_Vale_AES128:
      {
        EverCrypt_CTR_state_s scrut0 = *p;
        uint32_t c02 = scrut0.ctr;
        uint8_t *ek1 = scrut0.xkey;
        uint32_t iv_len1 = scrut0.iv_len;
        uint8_t *iv1 = scrut0.iv;
        uint8_t ctr_block1[16U] = { 0U };
        memcpy(ctr_block1, iv1, iv_len1 * sizeof iv1[0U]);
        uint128_t uu____0 = load128_be(ctr_block1);
        uint128_t c = uu____0 + (uint128_t)(uint64_t)c02;
        store128_le(ctr_block1, c);
        uint8_t *uu____1 = ek1;
        uint8_t inout_b[16U] = { 0U };
        uint32_t num_blocks = (uint32_t)(uint64_t)16U / (uint32_t)16U;
        uint32_t num_bytes_ = num_blocks * (uint32_t)16U;
        uint8_t *in_b_ = src;
        uint8_t *out_b_ = dst;
        memcpy(inout_b, src + num_bytes_, (uint32_t)(uint64_t)16U % (uint32_t)16U * sizeof src[0U]);
        uint64_t
        scrut1 =
          gctr128_bytes(in_b_,
            (uint64_t)16U,
            out_b_,
            inout_b,
            uu____1,
            ctr_block1,
            (uint64_t)num_blocks);
        memcpy(dst + num_bytes_,
          inout_b,
          (uint32_t)(uint64_t)16U % (uint32_t)16U * sizeof inout_b[0U]);
        uint32_t c4 = c02 + (uint32_t)1U;
        *p
        =
          (
            (EverCrypt_CTR_state_s){
              .i = Spec_Cipher_Expansion_Vale_AES128,
              .iv = iv1,
              .iv_len = iv_len1,
              .xkey = ek1,
              .ctr = c4
            }
          );
        break;
      }
    case Spec_Cipher_Expansion_Vale_AES256:
      {
        EverCrypt_CTR_state_s scrut0 = *p;
        uint32_t c02 = scrut0.ctr;
        uint8_t *ek1 = scrut0.xkey;
        uint32_t iv_len1 = scrut0.iv_len;
        uint8_t *iv1 = scrut0.iv;
        uint8_t ctr_block1[16U] = { 0U };
        memcpy(ctr_block1, iv1, iv_len1 * sizeof iv1[0U]);
        uint128_t uu____2 = load128_be(ctr_block1);
        uint128_t c = uu____2 + (uint128_t)(uint64_t)c02;
        store128_le(ctr_block1, c);
        uint8_t *uu____3 = ek1;
        uint8_t inout_b[16U] = { 0U };
        uint32_t num_blocks = (uint32_t)(uint64_t)16U / (uint32_t)16U;
        uint32_t num_bytes_ = num_blocks * (uint32_t)16U;
        uint8_t *in_b_ = src;
        uint8_t *out_b_ = dst;
        memcpy(inout_b, src + num_bytes_, (uint32_t)(uint64_t)16U % (uint32_t)16U * sizeof src[0U]);
        uint64_t
        scrut1 =
          gctr256_bytes(in_b_,
            (uint64_t)16U,
            out_b_,
            inout_b,
            uu____3,
            ctr_block1,
            (uint64_t)num_blocks);
        memcpy(dst + num_bytes_,
          inout_b,
          (uint32_t)(uint64_t)16U % (uint32_t)16U * sizeof inout_b[0U]);
        uint32_t c4 = c02 + (uint32_t)1U;
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
        break;
      }
    case Spec_Cipher_Expansion_Hacl_CHACHA20:
      {
        uint32_t ctx[16U] = { 0U };
        Hacl_Impl_Chacha20_chacha20_init(ctx, ek, iv, (uint32_t)0U);
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
  uint8_t *iv = scrut.iv;
  uint8_t *ek = scrut.xkey;
  KRML_HOST_FREE(iv);
  KRML_HOST_FREE(ek);
  KRML_HOST_FREE(p);
}

