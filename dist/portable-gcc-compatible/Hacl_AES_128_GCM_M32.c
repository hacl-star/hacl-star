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


#include "Hacl_AES_128_GCM_M32.h"

#include "internal/Hacl_AES_128_BitSlice.h"

/* SNIPPET_START: Hacl_AES_128_GCM_M32_aes_gcm_ctx_len */

uint32_t Hacl_AES_128_GCM_M32_aes_gcm_ctx_len = (uint32_t)396U;

/* SNIPPET_END: Hacl_AES_128_GCM_M32_aes_gcm_ctx_len */

/* SNIPPET_START: Hacl_AES_128_GCM_M32_aes128_gcm_init */

void Hacl_AES_128_GCM_M32_aes128_gcm_init(uint64_t *ctx, uint8_t *key, uint8_t *nonce)
{
  uint8_t gcm_key[16U] = { 0U };
  uint8_t tag_mix[16U] = { 0U };
  uint8_t nonce0[12U] = { 0U };
  uint64_t *aes_ctx = ctx;
  uint64_t *gcm_ctx = ctx + (uint32_t)128U;
  Hacl_AES_128_BitSlice_aes128_init(aes_ctx, key, nonce0);
  Hacl_AES_128_BitSlice_aes128_key_block(gcm_key, aes_ctx, (uint32_t)0U);
  Hacl_AES_128_BitSlice_aes128_set_nonce(aes_ctx, nonce);
  Hacl_AES_128_BitSlice_aes128_key_block(tag_mix, aes_ctx, (uint32_t)1U);
  Hacl_Gf128_PreComp_gcm_init(gcm_ctx, gcm_key);
  uint64_t u = load64_le(tag_mix);
  ctx[394U] = u;
  uint64_t u0 = load64_le(tag_mix + (uint32_t)8U);
  ctx[395U] = u0;
}

/* SNIPPET_END: Hacl_AES_128_GCM_M32_aes128_gcm_init */

/* SNIPPET_START: Hacl_AES_128_GCM_M32_aes128_gcm_encrypt */

void
Hacl_AES_128_GCM_M32_aes128_gcm_encrypt(
  uint64_t *ctx,
  uint32_t len,
  uint8_t *out,
  uint8_t *text,
  uint32_t aad_len,
  uint8_t *aad
)
{
  uint8_t tmp[16U] = { 0U };
  uint8_t *cip = out;
  uint64_t *aes_ctx = ctx;
  uint64_t *gcm_ctx = ctx + (uint32_t)128U;
  uint64_t *tag_mix = ctx + (uint32_t)394U;
  Hacl_Impl_AES_Generic_aes128_ctr_bitslice(len, cip, text, aes_ctx, (uint32_t)2U);
  Hacl_Gf128_PreComp_gcm_update_blocks_padded(gcm_ctx, aad_len, aad);
  Hacl_Gf128_PreComp_gcm_update_blocks_padded(gcm_ctx, len, cip);
  store64_be(tmp, (uint64_t)(aad_len * (uint32_t)8U));
  store64_be(tmp + (uint32_t)8U, (uint64_t)(len * (uint32_t)8U));
  Hacl_Gf128_PreComp_gcm_update_blocks(gcm_ctx, (uint32_t)16U, tmp);
  Hacl_Gf128_PreComp_gcm_emit(tmp, gcm_ctx);
  uint64_t u0 = load64_le(tmp);
  uint64_t tmp0 = u0;
  uint64_t u = load64_le(tmp + (uint32_t)8U);
  uint64_t tmp1 = u;
  uint64_t tmp01 = tmp0 ^ tag_mix[0U];
  uint64_t tmp11 = tmp1 ^ tag_mix[1U];
  store64_le(out + len, tmp01);
  store64_le(out + len + (uint32_t)8U, tmp11);
}

/* SNIPPET_END: Hacl_AES_128_GCM_M32_aes128_gcm_encrypt */

/* SNIPPET_START: Hacl_AES_128_GCM_M32_aes128_gcm_decrypt */

bool
Hacl_AES_128_GCM_M32_aes128_gcm_decrypt(
  uint64_t *ctx,
  uint32_t len,
  uint8_t *out,
  uint8_t *cipher,
  uint32_t aad_len,
  uint8_t *aad
)
{
  uint8_t scratch[18U] = { 0U };
  uint8_t *text = scratch;
  uint8_t *result = scratch + (uint32_t)17U;
  uint8_t *ciphertext = cipher;
  uint8_t *tag = cipher + len;
  uint64_t *aes_ctx = ctx;
  uint64_t *gcm_ctx = ctx + (uint32_t)128U;
  uint64_t *tag_mix = ctx + (uint32_t)394U;
  Hacl_Gf128_PreComp_gcm_update_blocks_padded(gcm_ctx, aad_len, aad);
  Hacl_Gf128_PreComp_gcm_update_blocks_padded(gcm_ctx, len, ciphertext);
  store64_be(text, (uint64_t)(aad_len * (uint32_t)8U));
  store64_be(text + (uint32_t)8U, (uint64_t)(len * (uint32_t)8U));
  Hacl_Gf128_PreComp_gcm_update_blocks(gcm_ctx, (uint32_t)16U, text);
  Hacl_Gf128_PreComp_gcm_emit(text, gcm_ctx);
  uint64_t u0 = load64_le(text);
  uint64_t text0 = u0;
  uint64_t u = load64_le(text + (uint32_t)8U);
  uint64_t text1 = u;
  uint64_t text01 = text0 ^ tag_mix[0U];
  uint64_t text11 = text1 ^ tag_mix[1U];
  store64_le(text, text01);
  store64_le(text + (uint32_t)8U, text11);
  KRML_MAYBE_FOR16(i,
    (uint32_t)0U,
    (uint32_t)16U,
    (uint32_t)1U,
    result[0U] = result[0U] | (text[i] ^ tag[i]););
  uint8_t res8 = result[0U];
  if (res8 == (uint8_t)0U)
  {
    Hacl_Impl_AES_Generic_aes128_ctr_bitslice(len, out, ciphertext, aes_ctx, (uint32_t)2U);
    return true;
  }
  return false;
}

/* SNIPPET_END: Hacl_AES_128_GCM_M32_aes128_gcm_decrypt */

