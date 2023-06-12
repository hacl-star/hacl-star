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


#include "Hacl_AES_128_GCM_NI.h"

/* SNIPPET_START: Hacl_AES_128_GCM_NI_aes128_gcm_init */

void
Hacl_AES_128_GCM_NI_aes128_gcm_init(
  Lib_IntVector_Intrinsics_vec128 *ctx,
  uint8_t *key,
  uint8_t *nonce
)
{
  uint8_t gcm_key[16U] = { 0U };
  uint8_t tag_mix[16U] = { 0U };
  uint8_t nonce0[12U] = { 0U };
  Lib_IntVector_Intrinsics_vec128 *aes_ctx = ctx;
  Lib_IntVector_Intrinsics_vec128 *gcm_ctx = ctx + (uint32_t)16U;
  Hacl_AES_128_NI_aes128_init(aes_ctx, key, nonce0);
  Hacl_AES_128_NI_aes128_key_block(gcm_key, aes_ctx, (uint32_t)0U);
  Hacl_AES_128_NI_aes128_set_nonce(aes_ctx, nonce);
  Hacl_AES_128_NI_aes128_key_block(tag_mix, aes_ctx, (uint32_t)1U);
  Hacl_Gf128_NI_gcm_init(gcm_ctx, gcm_key);
  ctx[21U] = Lib_IntVector_Intrinsics_vec128_load128_le(tag_mix);
}

/* SNIPPET_END: Hacl_AES_128_GCM_NI_aes128_gcm_init */

/* SNIPPET_START: Hacl_AES_128_GCM_NI_aes128_gcm_encrypt */

void
Hacl_AES_128_GCM_NI_aes128_gcm_encrypt(
  Lib_IntVector_Intrinsics_vec128 *ctx,
  uint32_t len,
  uint8_t *out,
  uint8_t *text,
  uint32_t aad_len,
  uint8_t *aad
)
{
  uint8_t *cip = out;
  Lib_IntVector_Intrinsics_vec128 *aes_ctx = ctx;
  uint32_t blocks64 = len / (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < blocks64; i++)
  {
    uint32_t ctr = (uint32_t)2U + i * (uint32_t)4U;
    uint8_t *ib = text + i * (uint32_t)64U;
    uint8_t *ob = cip + i * (uint32_t)64U;
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 st[4U] KRML_POST_ALIGN(16) = { 0U };
    Lib_IntVector_Intrinsics_vec128 *kex = aes_ctx + (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *n = aes_ctx;
    uint32_t counter = ctr;
    uint32_t counter0 = htobe32(counter);
    uint32_t counter1 = htobe32(counter + (uint32_t)1U);
    uint32_t counter2 = htobe32(counter + (uint32_t)2U);
    uint32_t counter3 = htobe32(counter + (uint32_t)3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
    uint32_t klen = (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)10U * klen;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    KRML_MAYBE_FOR9(i0,
      (uint32_t)0U,
      (uint32_t)9U,
      (uint32_t)1U,
      Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i0 * (uint32_t)1U;
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]););
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
    Lib_IntVector_Intrinsics_vec128 v0 = Lib_IntVector_Intrinsics_vec128_load128_le(ib);
    Lib_IntVector_Intrinsics_vec128
    v1 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)16U);
    Lib_IntVector_Intrinsics_vec128
    v2 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)32U);
    Lib_IntVector_Intrinsics_vec128
    v3 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v0, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)48U, v31);
  }
  uint32_t rem = len % (uint32_t)64U;
  uint8_t last[64U] = { 0U };
  if (rem > (uint32_t)0U)
  {
    uint32_t ctr = (uint32_t)2U + blocks64 * (uint32_t)4U;
    uint8_t *ib = text + blocks64 * (uint32_t)64U;
    uint8_t *ob = cip + blocks64 * (uint32_t)64U;
    memcpy(last, ib, rem * sizeof (uint8_t));
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 st[4U] KRML_POST_ALIGN(16) = { 0U };
    Lib_IntVector_Intrinsics_vec128 *kex = aes_ctx + (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *n = aes_ctx;
    uint32_t counter = ctr;
    uint32_t counter0 = htobe32(counter);
    uint32_t counter1 = htobe32(counter + (uint32_t)1U);
    uint32_t counter2 = htobe32(counter + (uint32_t)2U);
    uint32_t counter3 = htobe32(counter + (uint32_t)3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
    uint32_t klen = (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)10U * klen;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    KRML_MAYBE_FOR9(i,
      (uint32_t)0U,
      (uint32_t)9U,
      (uint32_t)1U,
      Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i * (uint32_t)1U;
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]););
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
    Lib_IntVector_Intrinsics_vec128 v0 = Lib_IntVector_Intrinsics_vec128_load128_le(last);
    Lib_IntVector_Intrinsics_vec128
    v1 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)16U);
    Lib_IntVector_Intrinsics_vec128
    v2 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)32U);
    Lib_IntVector_Intrinsics_vec128
    v3 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v0, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(last, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)48U, v31);
    memcpy(ob, last, rem * sizeof (uint8_t));
  }
  Lib_IntVector_Intrinsics_vec128 *gcm_ctx = ctx + (uint32_t)16U;
  Lib_IntVector_Intrinsics_vec128 tag_mix = ctx[21U];
  Hacl_Gf128_NI_gcm_update_padded(gcm_ctx, aad_len, aad);
  Hacl_Gf128_NI_gcm_update_padded(gcm_ctx, len, cip);
  uint8_t tmp[16U] = { 0U };
  store64_be(tmp, (uint64_t)(aad_len * (uint32_t)8U));
  store64_be(tmp + (uint32_t)8U, (uint64_t)(len * (uint32_t)8U));
  Hacl_Gf128_NI_gcm_update_blocks(gcm_ctx, (uint32_t)16U, tmp);
  Hacl_Gf128_NI_gcm_emit(tmp, gcm_ctx);
  Lib_IntVector_Intrinsics_vec128 tmp_vec = Lib_IntVector_Intrinsics_vec128_load128_le(tmp);
  Lib_IntVector_Intrinsics_vec128
  tmp_vec1 = Lib_IntVector_Intrinsics_vec128_xor(tmp_vec, tag_mix);
  Lib_IntVector_Intrinsics_vec128_store128_le(out + len, tmp_vec1);
}

/* SNIPPET_END: Hacl_AES_128_GCM_NI_aes128_gcm_encrypt */

/* SNIPPET_START: Hacl_AES_128_GCM_NI_aes128_gcm_decrypt */

bool
Hacl_AES_128_GCM_NI_aes128_gcm_decrypt(
  Lib_IntVector_Intrinsics_vec128 *ctx,
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
  Lib_IntVector_Intrinsics_vec128 *aes_ctx = ctx;
  Lib_IntVector_Intrinsics_vec128 *gcm_ctx = ctx + (uint32_t)16U;
  Lib_IntVector_Intrinsics_vec128 tag_mix = ctx[21U];
  Hacl_Gf128_NI_gcm_update_padded(gcm_ctx, aad_len, aad);
  Hacl_Gf128_NI_gcm_update_padded(gcm_ctx, len, ciphertext);
  store64_be(text, (uint64_t)(aad_len * (uint32_t)8U));
  store64_be(text + (uint32_t)8U, (uint64_t)(len * (uint32_t)8U));
  Hacl_Gf128_NI_gcm_update_blocks(gcm_ctx, (uint32_t)16U, text);
  Hacl_Gf128_NI_gcm_emit(text, gcm_ctx);
  Lib_IntVector_Intrinsics_vec128 text_vec = Lib_IntVector_Intrinsics_vec128_load128_le(text);
  Lib_IntVector_Intrinsics_vec128
  text_vec1 = Lib_IntVector_Intrinsics_vec128_xor(text_vec, tag_mix);
  Lib_IntVector_Intrinsics_vec128_store128_le(text, text_vec1);
  KRML_MAYBE_FOR16(i,
    (uint32_t)0U,
    (uint32_t)16U,
    (uint32_t)1U,
    result[0U] = result[0U] | (text[i] ^ tag[i]););
  uint8_t res8 = result[0U];
  if (res8 == (uint8_t)0U)
  {
    uint32_t blocks64 = len / (uint32_t)64U;
    for (uint32_t i = (uint32_t)0U; i < blocks64; i++)
    {
      uint32_t ctr = (uint32_t)2U + i * (uint32_t)4U;
      uint8_t *ib = ciphertext + i * (uint32_t)64U;
      uint8_t *ob = out + i * (uint32_t)64U;
      KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 st[4U] KRML_POST_ALIGN(16) = { 0U };
      Lib_IntVector_Intrinsics_vec128 *kex = aes_ctx + (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec128 *n = aes_ctx;
      uint32_t counter = ctr;
      uint32_t counter0 = htobe32(counter);
      uint32_t counter1 = htobe32(counter + (uint32_t)1U);
      uint32_t counter2 = htobe32(counter + (uint32_t)2U);
      uint32_t counter3 = htobe32(counter + (uint32_t)3U);
      Lib_IntVector_Intrinsics_vec128 nonce0 = n[0U];
      st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
      st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
      st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
      st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
      uint32_t klen = (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec128 *k0 = kex;
      Lib_IntVector_Intrinsics_vec128 *kr = kex + klen;
      Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)10U * klen;
      st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
      st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
      st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
      st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
      KRML_MAYBE_FOR9(i0,
        (uint32_t)0U,
        (uint32_t)9U,
        (uint32_t)1U,
        Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i0 * (uint32_t)1U;
        st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
        st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
        st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
        st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]););
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
      Lib_IntVector_Intrinsics_vec128 v0 = Lib_IntVector_Intrinsics_vec128_load128_le(ib);
      Lib_IntVector_Intrinsics_vec128
      v1 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)16U);
      Lib_IntVector_Intrinsics_vec128
      v2 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)32U);
      Lib_IntVector_Intrinsics_vec128
      v3 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)48U);
      Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v0, st[0U]);
      Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
      Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
      Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
      Lib_IntVector_Intrinsics_vec128_store128_le(ob, v01);
      Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)16U, v11);
      Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)32U, v21);
      Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)48U, v31);
    }
    uint32_t rem = len % (uint32_t)64U;
    uint8_t last[64U] = { 0U };
    if (rem > (uint32_t)0U)
    {
      uint32_t ctr = (uint32_t)2U + blocks64 * (uint32_t)4U;
      uint8_t *ib = ciphertext + blocks64 * (uint32_t)64U;
      uint8_t *ob = out + blocks64 * (uint32_t)64U;
      memcpy(last, ib, rem * sizeof (uint8_t));
      KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 st[4U] KRML_POST_ALIGN(16) = { 0U };
      Lib_IntVector_Intrinsics_vec128 *kex = aes_ctx + (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec128 *n = aes_ctx;
      uint32_t counter = ctr;
      uint32_t counter0 = htobe32(counter);
      uint32_t counter1 = htobe32(counter + (uint32_t)1U);
      uint32_t counter2 = htobe32(counter + (uint32_t)2U);
      uint32_t counter3 = htobe32(counter + (uint32_t)3U);
      Lib_IntVector_Intrinsics_vec128 nonce0 = n[0U];
      st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
      st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
      st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
      st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
      uint32_t klen = (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec128 *k0 = kex;
      Lib_IntVector_Intrinsics_vec128 *kr = kex + klen;
      Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)10U * klen;
      st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
      st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
      st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
      st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
      KRML_MAYBE_FOR9(i,
        (uint32_t)0U,
        (uint32_t)9U,
        (uint32_t)1U,
        Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i * (uint32_t)1U;
        st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
        st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
        st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
        st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]););
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
      Lib_IntVector_Intrinsics_vec128 v0 = Lib_IntVector_Intrinsics_vec128_load128_le(last);
      Lib_IntVector_Intrinsics_vec128
      v1 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)16U);
      Lib_IntVector_Intrinsics_vec128
      v2 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)32U);
      Lib_IntVector_Intrinsics_vec128
      v3 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)48U);
      Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v0, st[0U]);
      Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
      Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
      Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
      Lib_IntVector_Intrinsics_vec128_store128_le(last, v01);
      Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)16U, v11);
      Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)32U, v21);
      Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)48U, v31);
      memcpy(ob, last, rem * sizeof (uint8_t));
    }
    return true;
  }
  return false;
}

/* SNIPPET_END: Hacl_AES_128_GCM_NI_aes128_gcm_decrypt */

