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


#include "Hacl_AES_256_CTR32_NI.h"

/**
Allocate AES-256 context buffer using malloc for key expansion and nonce
*/
Lib_IntVector_Intrinsics_vec128 *Hacl_AES_256_CTR32_NI_context_malloc(void)
{
  Lib_IntVector_Intrinsics_vec128
  *buf =
    (Lib_IntVector_Intrinsics_vec128 *)KRML_ALIGNED_MALLOC(16,
      sizeof (Lib_IntVector_Intrinsics_vec128) * 16U);
  memset(buf, 0U, 16U * sizeof (Lib_IntVector_Intrinsics_vec128));
  return buf;
}

/**
Free AES-256 context buffer
*/
void Hacl_AES_256_CTR32_NI_context_free(Lib_IntVector_Intrinsics_vec128 *s)
{
  KRML_ALIGNED_FREE(s);
}

/**
Initiate AES-256 context buffer with key expansion and nonce
*/
void
Hacl_AES_256_CTR32_NI_init(Lib_IntVector_Intrinsics_vec128 *ctx, uint8_t *key, uint8_t *nonce)
{
  Lib_IntVector_Intrinsics_vec128 *kex = ctx + 1U;
  Lib_IntVector_Intrinsics_vec128 *n = ctx;
  uint8_t nb[16U] = { 0U };
  memcpy(nb, nonce, 12U * sizeof (uint8_t));
  n[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb);
  uint32_t klen = 1U;
  Lib_IntVector_Intrinsics_vec128 *next00 = kex;
  Lib_IntVector_Intrinsics_vec128 *next10 = kex + klen;
  next00[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(key);
  next10[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(key + 16U);
  uint32_t klen0 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev00 = kex + klen0 * 0U;
  Lib_IntVector_Intrinsics_vec128 *prev10 = kex + klen0 * 1U;
  Lib_IntVector_Intrinsics_vec128 *next01 = kex + klen0 * 2U;
  Lib_IntVector_Intrinsics_vec128 *next11 = kex + klen0 * 3U;
  Lib_IntVector_Intrinsics_vec128
  v0 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev10[0U], 0x01U);
  next01[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v0, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key1 = prev00[0U];
  Lib_IntVector_Intrinsics_vec128
  key2 =
    Lib_IntVector_Intrinsics_vec128_xor(key1,
      Lib_IntVector_Intrinsics_vec128_shift_left(key1, 32U));
  Lib_IntVector_Intrinsics_vec128
  key3 =
    Lib_IntVector_Intrinsics_vec128_xor(key2,
      Lib_IntVector_Intrinsics_vec128_shift_left(key2, 32U));
  Lib_IntVector_Intrinsics_vec128
  key4 =
    Lib_IntVector_Intrinsics_vec128_xor(key3,
      Lib_IntVector_Intrinsics_vec128_shift_left(key3, 32U));
  next01[0U] = Lib_IntVector_Intrinsics_vec128_xor(key4, next01[0U]);
  Lib_IntVector_Intrinsics_vec128
  v1 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next01[0U], 0U);
  next11[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v1, 2U, 2U, 2U, 2U);
  Lib_IntVector_Intrinsics_vec128 key10 = prev10[0U];
  Lib_IntVector_Intrinsics_vec128
  key20 =
    Lib_IntVector_Intrinsics_vec128_xor(key10,
      Lib_IntVector_Intrinsics_vec128_shift_left(key10, 32U));
  Lib_IntVector_Intrinsics_vec128
  key30 =
    Lib_IntVector_Intrinsics_vec128_xor(key20,
      Lib_IntVector_Intrinsics_vec128_shift_left(key20, 32U));
  Lib_IntVector_Intrinsics_vec128
  key40 =
    Lib_IntVector_Intrinsics_vec128_xor(key30,
      Lib_IntVector_Intrinsics_vec128_shift_left(key30, 32U));
  next11[0U] = Lib_IntVector_Intrinsics_vec128_xor(key40, next11[0U]);
  uint32_t klen1 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev01 = kex + klen1 * 2U;
  Lib_IntVector_Intrinsics_vec128 *prev11 = kex + klen1 * 3U;
  Lib_IntVector_Intrinsics_vec128 *next02 = kex + klen1 * 4U;
  Lib_IntVector_Intrinsics_vec128 *next12 = kex + klen1 * 5U;
  Lib_IntVector_Intrinsics_vec128
  v2 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev11[0U], 0x02U);
  next02[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v2, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key11 = prev01[0U];
  Lib_IntVector_Intrinsics_vec128
  key21 =
    Lib_IntVector_Intrinsics_vec128_xor(key11,
      Lib_IntVector_Intrinsics_vec128_shift_left(key11, 32U));
  Lib_IntVector_Intrinsics_vec128
  key31 =
    Lib_IntVector_Intrinsics_vec128_xor(key21,
      Lib_IntVector_Intrinsics_vec128_shift_left(key21, 32U));
  Lib_IntVector_Intrinsics_vec128
  key41 =
    Lib_IntVector_Intrinsics_vec128_xor(key31,
      Lib_IntVector_Intrinsics_vec128_shift_left(key31, 32U));
  next02[0U] = Lib_IntVector_Intrinsics_vec128_xor(key41, next02[0U]);
  Lib_IntVector_Intrinsics_vec128
  v3 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next02[0U], 0U);
  next12[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v3, 2U, 2U, 2U, 2U);
  Lib_IntVector_Intrinsics_vec128 key12 = prev11[0U];
  Lib_IntVector_Intrinsics_vec128
  key22 =
    Lib_IntVector_Intrinsics_vec128_xor(key12,
      Lib_IntVector_Intrinsics_vec128_shift_left(key12, 32U));
  Lib_IntVector_Intrinsics_vec128
  key32 =
    Lib_IntVector_Intrinsics_vec128_xor(key22,
      Lib_IntVector_Intrinsics_vec128_shift_left(key22, 32U));
  Lib_IntVector_Intrinsics_vec128
  key42 =
    Lib_IntVector_Intrinsics_vec128_xor(key32,
      Lib_IntVector_Intrinsics_vec128_shift_left(key32, 32U));
  next12[0U] = Lib_IntVector_Intrinsics_vec128_xor(key42, next12[0U]);
  uint32_t klen2 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev02 = kex + klen2 * 4U;
  Lib_IntVector_Intrinsics_vec128 *prev12 = kex + klen2 * 5U;
  Lib_IntVector_Intrinsics_vec128 *next03 = kex + klen2 * 6U;
  Lib_IntVector_Intrinsics_vec128 *next13 = kex + klen2 * 7U;
  Lib_IntVector_Intrinsics_vec128
  v4 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev12[0U], 0x04U);
  next03[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v4, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key13 = prev02[0U];
  Lib_IntVector_Intrinsics_vec128
  key23 =
    Lib_IntVector_Intrinsics_vec128_xor(key13,
      Lib_IntVector_Intrinsics_vec128_shift_left(key13, 32U));
  Lib_IntVector_Intrinsics_vec128
  key33 =
    Lib_IntVector_Intrinsics_vec128_xor(key23,
      Lib_IntVector_Intrinsics_vec128_shift_left(key23, 32U));
  Lib_IntVector_Intrinsics_vec128
  key43 =
    Lib_IntVector_Intrinsics_vec128_xor(key33,
      Lib_IntVector_Intrinsics_vec128_shift_left(key33, 32U));
  next03[0U] = Lib_IntVector_Intrinsics_vec128_xor(key43, next03[0U]);
  Lib_IntVector_Intrinsics_vec128
  v5 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next03[0U], 0U);
  next13[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v5, 2U, 2U, 2U, 2U);
  Lib_IntVector_Intrinsics_vec128 key14 = prev12[0U];
  Lib_IntVector_Intrinsics_vec128
  key24 =
    Lib_IntVector_Intrinsics_vec128_xor(key14,
      Lib_IntVector_Intrinsics_vec128_shift_left(key14, 32U));
  Lib_IntVector_Intrinsics_vec128
  key34 =
    Lib_IntVector_Intrinsics_vec128_xor(key24,
      Lib_IntVector_Intrinsics_vec128_shift_left(key24, 32U));
  Lib_IntVector_Intrinsics_vec128
  key44 =
    Lib_IntVector_Intrinsics_vec128_xor(key34,
      Lib_IntVector_Intrinsics_vec128_shift_left(key34, 32U));
  next13[0U] = Lib_IntVector_Intrinsics_vec128_xor(key44, next13[0U]);
  uint32_t klen3 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev03 = kex + klen3 * 6U;
  Lib_IntVector_Intrinsics_vec128 *prev13 = kex + klen3 * 7U;
  Lib_IntVector_Intrinsics_vec128 *next04 = kex + klen3 * 8U;
  Lib_IntVector_Intrinsics_vec128 *next14 = kex + klen3 * 9U;
  Lib_IntVector_Intrinsics_vec128
  v6 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev13[0U], 0x08U);
  next04[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v6, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key15 = prev03[0U];
  Lib_IntVector_Intrinsics_vec128
  key25 =
    Lib_IntVector_Intrinsics_vec128_xor(key15,
      Lib_IntVector_Intrinsics_vec128_shift_left(key15, 32U));
  Lib_IntVector_Intrinsics_vec128
  key35 =
    Lib_IntVector_Intrinsics_vec128_xor(key25,
      Lib_IntVector_Intrinsics_vec128_shift_left(key25, 32U));
  Lib_IntVector_Intrinsics_vec128
  key45 =
    Lib_IntVector_Intrinsics_vec128_xor(key35,
      Lib_IntVector_Intrinsics_vec128_shift_left(key35, 32U));
  next04[0U] = Lib_IntVector_Intrinsics_vec128_xor(key45, next04[0U]);
  Lib_IntVector_Intrinsics_vec128
  v7 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next04[0U], 0U);
  next14[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v7, 2U, 2U, 2U, 2U);
  Lib_IntVector_Intrinsics_vec128 key16 = prev13[0U];
  Lib_IntVector_Intrinsics_vec128
  key26 =
    Lib_IntVector_Intrinsics_vec128_xor(key16,
      Lib_IntVector_Intrinsics_vec128_shift_left(key16, 32U));
  Lib_IntVector_Intrinsics_vec128
  key36 =
    Lib_IntVector_Intrinsics_vec128_xor(key26,
      Lib_IntVector_Intrinsics_vec128_shift_left(key26, 32U));
  Lib_IntVector_Intrinsics_vec128
  key46 =
    Lib_IntVector_Intrinsics_vec128_xor(key36,
      Lib_IntVector_Intrinsics_vec128_shift_left(key36, 32U));
  next14[0U] = Lib_IntVector_Intrinsics_vec128_xor(key46, next14[0U]);
  uint32_t klen4 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev04 = kex + klen4 * 8U;
  Lib_IntVector_Intrinsics_vec128 *prev14 = kex + klen4 * 9U;
  Lib_IntVector_Intrinsics_vec128 *next05 = kex + klen4 * 10U;
  Lib_IntVector_Intrinsics_vec128 *next15 = kex + klen4 * 11U;
  Lib_IntVector_Intrinsics_vec128
  v8 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev14[0U], 0x10U);
  next05[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v8, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key17 = prev04[0U];
  Lib_IntVector_Intrinsics_vec128
  key27 =
    Lib_IntVector_Intrinsics_vec128_xor(key17,
      Lib_IntVector_Intrinsics_vec128_shift_left(key17, 32U));
  Lib_IntVector_Intrinsics_vec128
  key37 =
    Lib_IntVector_Intrinsics_vec128_xor(key27,
      Lib_IntVector_Intrinsics_vec128_shift_left(key27, 32U));
  Lib_IntVector_Intrinsics_vec128
  key47 =
    Lib_IntVector_Intrinsics_vec128_xor(key37,
      Lib_IntVector_Intrinsics_vec128_shift_left(key37, 32U));
  next05[0U] = Lib_IntVector_Intrinsics_vec128_xor(key47, next05[0U]);
  Lib_IntVector_Intrinsics_vec128
  v9 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next05[0U], 0U);
  next15[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v9, 2U, 2U, 2U, 2U);
  Lib_IntVector_Intrinsics_vec128 key18 = prev14[0U];
  Lib_IntVector_Intrinsics_vec128
  key28 =
    Lib_IntVector_Intrinsics_vec128_xor(key18,
      Lib_IntVector_Intrinsics_vec128_shift_left(key18, 32U));
  Lib_IntVector_Intrinsics_vec128
  key38 =
    Lib_IntVector_Intrinsics_vec128_xor(key28,
      Lib_IntVector_Intrinsics_vec128_shift_left(key28, 32U));
  Lib_IntVector_Intrinsics_vec128
  key48 =
    Lib_IntVector_Intrinsics_vec128_xor(key38,
      Lib_IntVector_Intrinsics_vec128_shift_left(key38, 32U));
  next15[0U] = Lib_IntVector_Intrinsics_vec128_xor(key48, next15[0U]);
  uint32_t klen5 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev05 = kex + klen5 * 10U;
  Lib_IntVector_Intrinsics_vec128 *prev15 = kex + klen5 * 11U;
  Lib_IntVector_Intrinsics_vec128 *next06 = kex + klen5 * 12U;
  Lib_IntVector_Intrinsics_vec128 *next1 = kex + klen5 * 13U;
  Lib_IntVector_Intrinsics_vec128
  v10 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev15[0U], 0x20U);
  next06[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v10, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key19 = prev05[0U];
  Lib_IntVector_Intrinsics_vec128
  key29 =
    Lib_IntVector_Intrinsics_vec128_xor(key19,
      Lib_IntVector_Intrinsics_vec128_shift_left(key19, 32U));
  Lib_IntVector_Intrinsics_vec128
  key39 =
    Lib_IntVector_Intrinsics_vec128_xor(key29,
      Lib_IntVector_Intrinsics_vec128_shift_left(key29, 32U));
  Lib_IntVector_Intrinsics_vec128
  key49 =
    Lib_IntVector_Intrinsics_vec128_xor(key39,
      Lib_IntVector_Intrinsics_vec128_shift_left(key39, 32U));
  next06[0U] = Lib_IntVector_Intrinsics_vec128_xor(key49, next06[0U]);
  Lib_IntVector_Intrinsics_vec128
  v11 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next06[0U], 0U);
  next1[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v11, 2U, 2U, 2U, 2U);
  Lib_IntVector_Intrinsics_vec128 key110 = prev15[0U];
  Lib_IntVector_Intrinsics_vec128
  key210 =
    Lib_IntVector_Intrinsics_vec128_xor(key110,
      Lib_IntVector_Intrinsics_vec128_shift_left(key110, 32U));
  Lib_IntVector_Intrinsics_vec128
  key310 =
    Lib_IntVector_Intrinsics_vec128_xor(key210,
      Lib_IntVector_Intrinsics_vec128_shift_left(key210, 32U));
  Lib_IntVector_Intrinsics_vec128
  key410 =
    Lib_IntVector_Intrinsics_vec128_xor(key310,
      Lib_IntVector_Intrinsics_vec128_shift_left(key310, 32U));
  next1[0U] = Lib_IntVector_Intrinsics_vec128_xor(key410, next1[0U]);
  uint32_t klen6 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev0 = kex + klen6 * 12U;
  Lib_IntVector_Intrinsics_vec128 *prev1 = kex + klen6 * 13U;
  Lib_IntVector_Intrinsics_vec128 *next0 = kex + klen6 * 14U;
  Lib_IntVector_Intrinsics_vec128
  v = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev1[0U], 0x40U);
  next0[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key111 = prev0[0U];
  Lib_IntVector_Intrinsics_vec128
  key211 =
    Lib_IntVector_Intrinsics_vec128_xor(key111,
      Lib_IntVector_Intrinsics_vec128_shift_left(key111, 32U));
  Lib_IntVector_Intrinsics_vec128
  key311 =
    Lib_IntVector_Intrinsics_vec128_xor(key211,
      Lib_IntVector_Intrinsics_vec128_shift_left(key211, 32U));
  Lib_IntVector_Intrinsics_vec128
  key411 =
    Lib_IntVector_Intrinsics_vec128_xor(key311,
      Lib_IntVector_Intrinsics_vec128_shift_left(key311, 32U));
  next0[0U] = Lib_IntVector_Intrinsics_vec128_xor(key411, next0[0U]);
}

/**
Set nonce in AES-256 context buffer
*/
void Hacl_AES_256_CTR32_NI_set_nonce(Lib_IntVector_Intrinsics_vec128 *ctx, uint8_t *nonce)
{
  Lib_IntVector_Intrinsics_vec128 *n = ctx;
  uint8_t nb[16U] = { 0U };
  memcpy(nb, nonce, 12U * sizeof (uint8_t));
  n[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb);
}

/**
Process number of bytes in AES-CTR32 mode.

  Given that `ctx` is initiated with AES-256 key and nonce, and
  
  `counter` is the initial value of counter state.
*/
void
Hacl_AES_256_CTR32_NI_ctr(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  Lib_IntVector_Intrinsics_vec128 *ctx,
  uint32_t c
)
{
  uint32_t rem = len % 64U;
  uint32_t nb = len / 64U;
  uint32_t rem1 = len % 64U;
  for (uint32_t i = 0U; i < nb; i++)
  {
    uint8_t *uu____0 = out + i * 64U;
    uint8_t *uu____1 = inp + i * 64U;
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 st[4U] KRML_POST_ALIGN(16) = { 0U };
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + 1U;
    Lib_IntVector_Intrinsics_vec128 *n = ctx;
    uint32_t counter0 = htobe32(c + i * 4U);
    uint32_t counter1 = htobe32(c + i * 4U + 1U);
    uint32_t counter2 = htobe32(c + i * 4U + 2U);
    uint32_t counter3 = htobe32(c + i * 4U + 3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, 3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, 3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, 3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, 3U);
    uint32_t klen = 1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + 14U * klen;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    KRML_MAYBE_FOR13(i0,
      0U,
      13U,
      1U,
      Lib_IntVector_Intrinsics_vec128 *k = kr + i0 * 1U;
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(k[0U], st[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(k[0U], st[1U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(k[0U], st[2U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(k[0U], st[3U]););
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[1U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[2U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[3U]);
    Lib_IntVector_Intrinsics_vec128 v0 = Lib_IntVector_Intrinsics_vec128_load128_le(uu____1);
    Lib_IntVector_Intrinsics_vec128 v1 = Lib_IntVector_Intrinsics_vec128_load128_le(uu____1 + 16U);
    Lib_IntVector_Intrinsics_vec128 v2 = Lib_IntVector_Intrinsics_vec128_load128_le(uu____1 + 32U);
    Lib_IntVector_Intrinsics_vec128 v3 = Lib_IntVector_Intrinsics_vec128_load128_le(uu____1 + 48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v0, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(uu____0, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(uu____0 + 16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(uu____0 + 32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(uu____0 + 48U, v31);
  }
  if (rem1 > 0U)
  {
    uint8_t *uu____2 = out + nb * 64U;
    uint8_t last[64U] = { 0U };
    memcpy(last, inp + nb * 64U, rem * sizeof (uint8_t));
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 st[4U] KRML_POST_ALIGN(16) = { 0U };
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + 1U;
    Lib_IntVector_Intrinsics_vec128 *n = ctx;
    uint32_t counter0 = htobe32(c + nb * 4U);
    uint32_t counter1 = htobe32(c + nb * 4U + 1U);
    uint32_t counter2 = htobe32(c + nb * 4U + 2U);
    uint32_t counter3 = htobe32(c + nb * 4U + 3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, 3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, 3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, 3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, 3U);
    uint32_t klen = 1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + 14U * klen;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    KRML_MAYBE_FOR13(i,
      0U,
      13U,
      1U,
      Lib_IntVector_Intrinsics_vec128 *k = kr + i * 1U;
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(k[0U], st[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(k[0U], st[1U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(k[0U], st[2U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(k[0U], st[3U]););
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[1U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[2U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[3U]);
    Lib_IntVector_Intrinsics_vec128 v0 = Lib_IntVector_Intrinsics_vec128_load128_le(last);
    Lib_IntVector_Intrinsics_vec128 v1 = Lib_IntVector_Intrinsics_vec128_load128_le(last + 16U);
    Lib_IntVector_Intrinsics_vec128 v2 = Lib_IntVector_Intrinsics_vec128_load128_le(last + 32U);
    Lib_IntVector_Intrinsics_vec128 v3 = Lib_IntVector_Intrinsics_vec128_load128_le(last + 48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v0, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(last, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + 16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + 32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + 48U, v31);
    memcpy(uu____2, last, rem * sizeof (uint8_t));
    return;
  }
}

/**
Initiate AES-CTR32-256 context with key and nonce, and

  encrypt number of bytes in AES-CTR32 mode.
  
  `counter` is the initial value of counter state.
*/
void
Hacl_AES_256_CTR32_NI_ctr_encrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint8_t *k,
  uint8_t *n,
  uint32_t c
)
{
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 ctx[16U] KRML_POST_ALIGN(16) = { 0U };
  Lib_IntVector_Intrinsics_vec128 *kex0 = ctx + 1U;
  Lib_IntVector_Intrinsics_vec128 *n10 = ctx;
  uint8_t nb0[16U] = { 0U };
  memcpy(nb0, n, 12U * sizeof (uint8_t));
  n10[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb0);
  uint32_t klen = 1U;
  Lib_IntVector_Intrinsics_vec128 *next00 = kex0;
  Lib_IntVector_Intrinsics_vec128 *next10 = kex0 + klen;
  next00[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(k);
  next10[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(k + 16U);
  uint32_t klen0 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev00 = kex0 + klen0 * 0U;
  Lib_IntVector_Intrinsics_vec128 *prev10 = kex0 + klen0 * 1U;
  Lib_IntVector_Intrinsics_vec128 *next01 = kex0 + klen0 * 2U;
  Lib_IntVector_Intrinsics_vec128 *next11 = kex0 + klen0 * 3U;
  Lib_IntVector_Intrinsics_vec128
  v0 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev10[0U], 0x01U);
  next01[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v0, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key = prev00[0U];
  Lib_IntVector_Intrinsics_vec128
  key1 =
    Lib_IntVector_Intrinsics_vec128_xor(key,
      Lib_IntVector_Intrinsics_vec128_shift_left(key, 32U));
  Lib_IntVector_Intrinsics_vec128
  key2 =
    Lib_IntVector_Intrinsics_vec128_xor(key1,
      Lib_IntVector_Intrinsics_vec128_shift_left(key1, 32U));
  Lib_IntVector_Intrinsics_vec128
  key3 =
    Lib_IntVector_Intrinsics_vec128_xor(key2,
      Lib_IntVector_Intrinsics_vec128_shift_left(key2, 32U));
  next01[0U] = Lib_IntVector_Intrinsics_vec128_xor(key3, next01[0U]);
  Lib_IntVector_Intrinsics_vec128
  v4 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next01[0U], 0U);
  next11[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v4, 2U, 2U, 2U, 2U);
  Lib_IntVector_Intrinsics_vec128 key0 = prev10[0U];
  Lib_IntVector_Intrinsics_vec128
  key10 =
    Lib_IntVector_Intrinsics_vec128_xor(key0,
      Lib_IntVector_Intrinsics_vec128_shift_left(key0, 32U));
  Lib_IntVector_Intrinsics_vec128
  key20 =
    Lib_IntVector_Intrinsics_vec128_xor(key10,
      Lib_IntVector_Intrinsics_vec128_shift_left(key10, 32U));
  Lib_IntVector_Intrinsics_vec128
  key30 =
    Lib_IntVector_Intrinsics_vec128_xor(key20,
      Lib_IntVector_Intrinsics_vec128_shift_left(key20, 32U));
  next11[0U] = Lib_IntVector_Intrinsics_vec128_xor(key30, next11[0U]);
  uint32_t klen1 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev01 = kex0 + klen1 * 2U;
  Lib_IntVector_Intrinsics_vec128 *prev11 = kex0 + klen1 * 3U;
  Lib_IntVector_Intrinsics_vec128 *next02 = kex0 + klen1 * 4U;
  Lib_IntVector_Intrinsics_vec128 *next12 = kex0 + klen1 * 5U;
  Lib_IntVector_Intrinsics_vec128
  v5 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev11[0U], 0x02U);
  next02[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v5, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key4 = prev01[0U];
  Lib_IntVector_Intrinsics_vec128
  key11 =
    Lib_IntVector_Intrinsics_vec128_xor(key4,
      Lib_IntVector_Intrinsics_vec128_shift_left(key4, 32U));
  Lib_IntVector_Intrinsics_vec128
  key21 =
    Lib_IntVector_Intrinsics_vec128_xor(key11,
      Lib_IntVector_Intrinsics_vec128_shift_left(key11, 32U));
  Lib_IntVector_Intrinsics_vec128
  key31 =
    Lib_IntVector_Intrinsics_vec128_xor(key21,
      Lib_IntVector_Intrinsics_vec128_shift_left(key21, 32U));
  next02[0U] = Lib_IntVector_Intrinsics_vec128_xor(key31, next02[0U]);
  Lib_IntVector_Intrinsics_vec128
  v6 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next02[0U], 0U);
  next12[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v6, 2U, 2U, 2U, 2U);
  Lib_IntVector_Intrinsics_vec128 key5 = prev11[0U];
  Lib_IntVector_Intrinsics_vec128
  key12 =
    Lib_IntVector_Intrinsics_vec128_xor(key5,
      Lib_IntVector_Intrinsics_vec128_shift_left(key5, 32U));
  Lib_IntVector_Intrinsics_vec128
  key22 =
    Lib_IntVector_Intrinsics_vec128_xor(key12,
      Lib_IntVector_Intrinsics_vec128_shift_left(key12, 32U));
  Lib_IntVector_Intrinsics_vec128
  key32 =
    Lib_IntVector_Intrinsics_vec128_xor(key22,
      Lib_IntVector_Intrinsics_vec128_shift_left(key22, 32U));
  next12[0U] = Lib_IntVector_Intrinsics_vec128_xor(key32, next12[0U]);
  uint32_t klen2 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev02 = kex0 + klen2 * 4U;
  Lib_IntVector_Intrinsics_vec128 *prev12 = kex0 + klen2 * 5U;
  Lib_IntVector_Intrinsics_vec128 *next03 = kex0 + klen2 * 6U;
  Lib_IntVector_Intrinsics_vec128 *next13 = kex0 + klen2 * 7U;
  Lib_IntVector_Intrinsics_vec128
  v7 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev12[0U], 0x04U);
  next03[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v7, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key6 = prev02[0U];
  Lib_IntVector_Intrinsics_vec128
  key13 =
    Lib_IntVector_Intrinsics_vec128_xor(key6,
      Lib_IntVector_Intrinsics_vec128_shift_left(key6, 32U));
  Lib_IntVector_Intrinsics_vec128
  key23 =
    Lib_IntVector_Intrinsics_vec128_xor(key13,
      Lib_IntVector_Intrinsics_vec128_shift_left(key13, 32U));
  Lib_IntVector_Intrinsics_vec128
  key33 =
    Lib_IntVector_Intrinsics_vec128_xor(key23,
      Lib_IntVector_Intrinsics_vec128_shift_left(key23, 32U));
  next03[0U] = Lib_IntVector_Intrinsics_vec128_xor(key33, next03[0U]);
  Lib_IntVector_Intrinsics_vec128
  v8 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next03[0U], 0U);
  next13[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v8, 2U, 2U, 2U, 2U);
  Lib_IntVector_Intrinsics_vec128 key7 = prev12[0U];
  Lib_IntVector_Intrinsics_vec128
  key14 =
    Lib_IntVector_Intrinsics_vec128_xor(key7,
      Lib_IntVector_Intrinsics_vec128_shift_left(key7, 32U));
  Lib_IntVector_Intrinsics_vec128
  key24 =
    Lib_IntVector_Intrinsics_vec128_xor(key14,
      Lib_IntVector_Intrinsics_vec128_shift_left(key14, 32U));
  Lib_IntVector_Intrinsics_vec128
  key34 =
    Lib_IntVector_Intrinsics_vec128_xor(key24,
      Lib_IntVector_Intrinsics_vec128_shift_left(key24, 32U));
  next13[0U] = Lib_IntVector_Intrinsics_vec128_xor(key34, next13[0U]);
  uint32_t klen3 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev03 = kex0 + klen3 * 6U;
  Lib_IntVector_Intrinsics_vec128 *prev13 = kex0 + klen3 * 7U;
  Lib_IntVector_Intrinsics_vec128 *next04 = kex0 + klen3 * 8U;
  Lib_IntVector_Intrinsics_vec128 *next14 = kex0 + klen3 * 9U;
  Lib_IntVector_Intrinsics_vec128
  v9 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev13[0U], 0x08U);
  next04[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v9, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key8 = prev03[0U];
  Lib_IntVector_Intrinsics_vec128
  key15 =
    Lib_IntVector_Intrinsics_vec128_xor(key8,
      Lib_IntVector_Intrinsics_vec128_shift_left(key8, 32U));
  Lib_IntVector_Intrinsics_vec128
  key25 =
    Lib_IntVector_Intrinsics_vec128_xor(key15,
      Lib_IntVector_Intrinsics_vec128_shift_left(key15, 32U));
  Lib_IntVector_Intrinsics_vec128
  key35 =
    Lib_IntVector_Intrinsics_vec128_xor(key25,
      Lib_IntVector_Intrinsics_vec128_shift_left(key25, 32U));
  next04[0U] = Lib_IntVector_Intrinsics_vec128_xor(key35, next04[0U]);
  Lib_IntVector_Intrinsics_vec128
  v10 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next04[0U], 0U);
  next14[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v10, 2U, 2U, 2U, 2U);
  Lib_IntVector_Intrinsics_vec128 key9 = prev13[0U];
  Lib_IntVector_Intrinsics_vec128
  key16 =
    Lib_IntVector_Intrinsics_vec128_xor(key9,
      Lib_IntVector_Intrinsics_vec128_shift_left(key9, 32U));
  Lib_IntVector_Intrinsics_vec128
  key26 =
    Lib_IntVector_Intrinsics_vec128_xor(key16,
      Lib_IntVector_Intrinsics_vec128_shift_left(key16, 32U));
  Lib_IntVector_Intrinsics_vec128
  key36 =
    Lib_IntVector_Intrinsics_vec128_xor(key26,
      Lib_IntVector_Intrinsics_vec128_shift_left(key26, 32U));
  next14[0U] = Lib_IntVector_Intrinsics_vec128_xor(key36, next14[0U]);
  uint32_t klen4 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev04 = kex0 + klen4 * 8U;
  Lib_IntVector_Intrinsics_vec128 *prev14 = kex0 + klen4 * 9U;
  Lib_IntVector_Intrinsics_vec128 *next05 = kex0 + klen4 * 10U;
  Lib_IntVector_Intrinsics_vec128 *next15 = kex0 + klen4 * 11U;
  Lib_IntVector_Intrinsics_vec128
  v12 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev14[0U], 0x10U);
  next05[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v12, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key17 = prev04[0U];
  Lib_IntVector_Intrinsics_vec128
  key18 =
    Lib_IntVector_Intrinsics_vec128_xor(key17,
      Lib_IntVector_Intrinsics_vec128_shift_left(key17, 32U));
  Lib_IntVector_Intrinsics_vec128
  key27 =
    Lib_IntVector_Intrinsics_vec128_xor(key18,
      Lib_IntVector_Intrinsics_vec128_shift_left(key18, 32U));
  Lib_IntVector_Intrinsics_vec128
  key37 =
    Lib_IntVector_Intrinsics_vec128_xor(key27,
      Lib_IntVector_Intrinsics_vec128_shift_left(key27, 32U));
  next05[0U] = Lib_IntVector_Intrinsics_vec128_xor(key37, next05[0U]);
  Lib_IntVector_Intrinsics_vec128
  v13 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next05[0U], 0U);
  next15[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v13, 2U, 2U, 2U, 2U);
  Lib_IntVector_Intrinsics_vec128 key19 = prev14[0U];
  Lib_IntVector_Intrinsics_vec128
  key110 =
    Lib_IntVector_Intrinsics_vec128_xor(key19,
      Lib_IntVector_Intrinsics_vec128_shift_left(key19, 32U));
  Lib_IntVector_Intrinsics_vec128
  key28 =
    Lib_IntVector_Intrinsics_vec128_xor(key110,
      Lib_IntVector_Intrinsics_vec128_shift_left(key110, 32U));
  Lib_IntVector_Intrinsics_vec128
  key38 =
    Lib_IntVector_Intrinsics_vec128_xor(key28,
      Lib_IntVector_Intrinsics_vec128_shift_left(key28, 32U));
  next15[0U] = Lib_IntVector_Intrinsics_vec128_xor(key38, next15[0U]);
  uint32_t klen5 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev05 = kex0 + klen5 * 10U;
  Lib_IntVector_Intrinsics_vec128 *prev15 = kex0 + klen5 * 11U;
  Lib_IntVector_Intrinsics_vec128 *next06 = kex0 + klen5 * 12U;
  Lib_IntVector_Intrinsics_vec128 *next1 = kex0 + klen5 * 13U;
  Lib_IntVector_Intrinsics_vec128
  v14 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev15[0U], 0x20U);
  next06[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v14, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key29 = prev05[0U];
  Lib_IntVector_Intrinsics_vec128
  key111 =
    Lib_IntVector_Intrinsics_vec128_xor(key29,
      Lib_IntVector_Intrinsics_vec128_shift_left(key29, 32U));
  Lib_IntVector_Intrinsics_vec128
  key210 =
    Lib_IntVector_Intrinsics_vec128_xor(key111,
      Lib_IntVector_Intrinsics_vec128_shift_left(key111, 32U));
  Lib_IntVector_Intrinsics_vec128
  key39 =
    Lib_IntVector_Intrinsics_vec128_xor(key210,
      Lib_IntVector_Intrinsics_vec128_shift_left(key210, 32U));
  next06[0U] = Lib_IntVector_Intrinsics_vec128_xor(key39, next06[0U]);
  Lib_IntVector_Intrinsics_vec128
  v15 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next06[0U], 0U);
  next1[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v15, 2U, 2U, 2U, 2U);
  Lib_IntVector_Intrinsics_vec128 key40 = prev15[0U];
  Lib_IntVector_Intrinsics_vec128
  key112 =
    Lib_IntVector_Intrinsics_vec128_xor(key40,
      Lib_IntVector_Intrinsics_vec128_shift_left(key40, 32U));
  Lib_IntVector_Intrinsics_vec128
  key211 =
    Lib_IntVector_Intrinsics_vec128_xor(key112,
      Lib_IntVector_Intrinsics_vec128_shift_left(key112, 32U));
  Lib_IntVector_Intrinsics_vec128
  key310 =
    Lib_IntVector_Intrinsics_vec128_xor(key211,
      Lib_IntVector_Intrinsics_vec128_shift_left(key211, 32U));
  next1[0U] = Lib_IntVector_Intrinsics_vec128_xor(key310, next1[0U]);
  uint32_t klen6 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev0 = kex0 + klen6 * 12U;
  Lib_IntVector_Intrinsics_vec128 *prev1 = kex0 + klen6 * 13U;
  Lib_IntVector_Intrinsics_vec128 *next0 = kex0 + klen6 * 14U;
  Lib_IntVector_Intrinsics_vec128
  v = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev1[0U], 0x40U);
  next0[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key41 = prev0[0U];
  Lib_IntVector_Intrinsics_vec128
  key113 =
    Lib_IntVector_Intrinsics_vec128_xor(key41,
      Lib_IntVector_Intrinsics_vec128_shift_left(key41, 32U));
  Lib_IntVector_Intrinsics_vec128
  key212 =
    Lib_IntVector_Intrinsics_vec128_xor(key113,
      Lib_IntVector_Intrinsics_vec128_shift_left(key113, 32U));
  Lib_IntVector_Intrinsics_vec128
  key311 =
    Lib_IntVector_Intrinsics_vec128_xor(key212,
      Lib_IntVector_Intrinsics_vec128_shift_left(key212, 32U));
  next0[0U] = Lib_IntVector_Intrinsics_vec128_xor(key311, next0[0U]);
  uint32_t rem = len % 64U;
  uint32_t nb = len / 64U;
  uint32_t rem1 = len % 64U;
  for (uint32_t i = 0U; i < nb; i++)
  {
    uint8_t *uu____0 = out + i * 64U;
    uint8_t *uu____1 = inp + i * 64U;
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 st[4U] KRML_POST_ALIGN(16) = { 0U };
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + 1U;
    Lib_IntVector_Intrinsics_vec128 *n1 = ctx;
    uint32_t counter0 = htobe32(c + i * 4U);
    uint32_t counter1 = htobe32(c + i * 4U + 1U);
    uint32_t counter2 = htobe32(c + i * 4U + 2U);
    uint32_t counter3 = htobe32(c + i * 4U + 3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n1[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, 3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, 3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, 3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, 3U);
    uint32_t klen7 = 1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen7;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + 14U * klen7;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    KRML_MAYBE_FOR13(i0,
      0U,
      13U,
      1U,
      Lib_IntVector_Intrinsics_vec128 *k1 = kr + i0 * 1U;
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(k1[0U], st[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(k1[0U], st[1U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(k1[0U], st[2U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(k1[0U], st[3U]););
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[1U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[2U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[3U]);
    Lib_IntVector_Intrinsics_vec128 v00 = Lib_IntVector_Intrinsics_vec128_load128_le(uu____1);
    Lib_IntVector_Intrinsics_vec128 v1 = Lib_IntVector_Intrinsics_vec128_load128_le(uu____1 + 16U);
    Lib_IntVector_Intrinsics_vec128 v2 = Lib_IntVector_Intrinsics_vec128_load128_le(uu____1 + 32U);
    Lib_IntVector_Intrinsics_vec128 v3 = Lib_IntVector_Intrinsics_vec128_load128_le(uu____1 + 48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v00, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(uu____0, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(uu____0 + 16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(uu____0 + 32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(uu____0 + 48U, v31);
  }
  if (rem1 > 0U)
  {
    uint8_t *uu____2 = out + nb * 64U;
    uint8_t last[64U] = { 0U };
    memcpy(last, inp + nb * 64U, rem * sizeof (uint8_t));
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 st[4U] KRML_POST_ALIGN(16) = { 0U };
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + 1U;
    Lib_IntVector_Intrinsics_vec128 *n1 = ctx;
    uint32_t counter0 = htobe32(c + nb * 4U);
    uint32_t counter1 = htobe32(c + nb * 4U + 1U);
    uint32_t counter2 = htobe32(c + nb * 4U + 2U);
    uint32_t counter3 = htobe32(c + nb * 4U + 3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n1[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, 3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, 3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, 3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, 3U);
    uint32_t klen7 = 1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen7;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + 14U * klen7;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    KRML_MAYBE_FOR13(i,
      0U,
      13U,
      1U,
      Lib_IntVector_Intrinsics_vec128 *k1 = kr + i * 1U;
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(k1[0U], st[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(k1[0U], st[1U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(k1[0U], st[2U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(k1[0U], st[3U]););
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[1U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[2U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[3U]);
    Lib_IntVector_Intrinsics_vec128 v00 = Lib_IntVector_Intrinsics_vec128_load128_le(last);
    Lib_IntVector_Intrinsics_vec128 v1 = Lib_IntVector_Intrinsics_vec128_load128_le(last + 16U);
    Lib_IntVector_Intrinsics_vec128 v2 = Lib_IntVector_Intrinsics_vec128_load128_le(last + 32U);
    Lib_IntVector_Intrinsics_vec128 v3 = Lib_IntVector_Intrinsics_vec128_load128_le(last + 48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v00, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(last, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + 16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + 32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + 48U, v31);
    memcpy(uu____2, last, rem * sizeof (uint8_t));
  }
}

/**
Initiate AES-CTR32-256 context with key and nonce, and

  decrypt number of bytes in AES-CTR32 mode.
  
  `counter` is the initial value of counter state.
  
  Decryption uses the forward version of AES cipher
*/
void
Hacl_AES_256_CTR32_NI_ctr_decrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint8_t *k,
  uint8_t *n,
  uint32_t c
)
{
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 ctx[16U] KRML_POST_ALIGN(16) = { 0U };
  Lib_IntVector_Intrinsics_vec128 *kex0 = ctx + 1U;
  Lib_IntVector_Intrinsics_vec128 *n10 = ctx;
  uint8_t nb0[16U] = { 0U };
  memcpy(nb0, n, 12U * sizeof (uint8_t));
  n10[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb0);
  uint32_t klen = 1U;
  Lib_IntVector_Intrinsics_vec128 *next00 = kex0;
  Lib_IntVector_Intrinsics_vec128 *next10 = kex0 + klen;
  next00[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(k);
  next10[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(k + 16U);
  uint32_t klen0 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev00 = kex0 + klen0 * 0U;
  Lib_IntVector_Intrinsics_vec128 *prev10 = kex0 + klen0 * 1U;
  Lib_IntVector_Intrinsics_vec128 *next01 = kex0 + klen0 * 2U;
  Lib_IntVector_Intrinsics_vec128 *next11 = kex0 + klen0 * 3U;
  Lib_IntVector_Intrinsics_vec128
  v0 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev10[0U], 0x01U);
  next01[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v0, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key = prev00[0U];
  Lib_IntVector_Intrinsics_vec128
  key1 =
    Lib_IntVector_Intrinsics_vec128_xor(key,
      Lib_IntVector_Intrinsics_vec128_shift_left(key, 32U));
  Lib_IntVector_Intrinsics_vec128
  key2 =
    Lib_IntVector_Intrinsics_vec128_xor(key1,
      Lib_IntVector_Intrinsics_vec128_shift_left(key1, 32U));
  Lib_IntVector_Intrinsics_vec128
  key3 =
    Lib_IntVector_Intrinsics_vec128_xor(key2,
      Lib_IntVector_Intrinsics_vec128_shift_left(key2, 32U));
  next01[0U] = Lib_IntVector_Intrinsics_vec128_xor(key3, next01[0U]);
  Lib_IntVector_Intrinsics_vec128
  v4 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next01[0U], 0U);
  next11[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v4, 2U, 2U, 2U, 2U);
  Lib_IntVector_Intrinsics_vec128 key0 = prev10[0U];
  Lib_IntVector_Intrinsics_vec128
  key10 =
    Lib_IntVector_Intrinsics_vec128_xor(key0,
      Lib_IntVector_Intrinsics_vec128_shift_left(key0, 32U));
  Lib_IntVector_Intrinsics_vec128
  key20 =
    Lib_IntVector_Intrinsics_vec128_xor(key10,
      Lib_IntVector_Intrinsics_vec128_shift_left(key10, 32U));
  Lib_IntVector_Intrinsics_vec128
  key30 =
    Lib_IntVector_Intrinsics_vec128_xor(key20,
      Lib_IntVector_Intrinsics_vec128_shift_left(key20, 32U));
  next11[0U] = Lib_IntVector_Intrinsics_vec128_xor(key30, next11[0U]);
  uint32_t klen1 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev01 = kex0 + klen1 * 2U;
  Lib_IntVector_Intrinsics_vec128 *prev11 = kex0 + klen1 * 3U;
  Lib_IntVector_Intrinsics_vec128 *next02 = kex0 + klen1 * 4U;
  Lib_IntVector_Intrinsics_vec128 *next12 = kex0 + klen1 * 5U;
  Lib_IntVector_Intrinsics_vec128
  v5 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev11[0U], 0x02U);
  next02[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v5, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key4 = prev01[0U];
  Lib_IntVector_Intrinsics_vec128
  key11 =
    Lib_IntVector_Intrinsics_vec128_xor(key4,
      Lib_IntVector_Intrinsics_vec128_shift_left(key4, 32U));
  Lib_IntVector_Intrinsics_vec128
  key21 =
    Lib_IntVector_Intrinsics_vec128_xor(key11,
      Lib_IntVector_Intrinsics_vec128_shift_left(key11, 32U));
  Lib_IntVector_Intrinsics_vec128
  key31 =
    Lib_IntVector_Intrinsics_vec128_xor(key21,
      Lib_IntVector_Intrinsics_vec128_shift_left(key21, 32U));
  next02[0U] = Lib_IntVector_Intrinsics_vec128_xor(key31, next02[0U]);
  Lib_IntVector_Intrinsics_vec128
  v6 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next02[0U], 0U);
  next12[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v6, 2U, 2U, 2U, 2U);
  Lib_IntVector_Intrinsics_vec128 key5 = prev11[0U];
  Lib_IntVector_Intrinsics_vec128
  key12 =
    Lib_IntVector_Intrinsics_vec128_xor(key5,
      Lib_IntVector_Intrinsics_vec128_shift_left(key5, 32U));
  Lib_IntVector_Intrinsics_vec128
  key22 =
    Lib_IntVector_Intrinsics_vec128_xor(key12,
      Lib_IntVector_Intrinsics_vec128_shift_left(key12, 32U));
  Lib_IntVector_Intrinsics_vec128
  key32 =
    Lib_IntVector_Intrinsics_vec128_xor(key22,
      Lib_IntVector_Intrinsics_vec128_shift_left(key22, 32U));
  next12[0U] = Lib_IntVector_Intrinsics_vec128_xor(key32, next12[0U]);
  uint32_t klen2 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev02 = kex0 + klen2 * 4U;
  Lib_IntVector_Intrinsics_vec128 *prev12 = kex0 + klen2 * 5U;
  Lib_IntVector_Intrinsics_vec128 *next03 = kex0 + klen2 * 6U;
  Lib_IntVector_Intrinsics_vec128 *next13 = kex0 + klen2 * 7U;
  Lib_IntVector_Intrinsics_vec128
  v7 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev12[0U], 0x04U);
  next03[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v7, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key6 = prev02[0U];
  Lib_IntVector_Intrinsics_vec128
  key13 =
    Lib_IntVector_Intrinsics_vec128_xor(key6,
      Lib_IntVector_Intrinsics_vec128_shift_left(key6, 32U));
  Lib_IntVector_Intrinsics_vec128
  key23 =
    Lib_IntVector_Intrinsics_vec128_xor(key13,
      Lib_IntVector_Intrinsics_vec128_shift_left(key13, 32U));
  Lib_IntVector_Intrinsics_vec128
  key33 =
    Lib_IntVector_Intrinsics_vec128_xor(key23,
      Lib_IntVector_Intrinsics_vec128_shift_left(key23, 32U));
  next03[0U] = Lib_IntVector_Intrinsics_vec128_xor(key33, next03[0U]);
  Lib_IntVector_Intrinsics_vec128
  v8 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next03[0U], 0U);
  next13[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v8, 2U, 2U, 2U, 2U);
  Lib_IntVector_Intrinsics_vec128 key7 = prev12[0U];
  Lib_IntVector_Intrinsics_vec128
  key14 =
    Lib_IntVector_Intrinsics_vec128_xor(key7,
      Lib_IntVector_Intrinsics_vec128_shift_left(key7, 32U));
  Lib_IntVector_Intrinsics_vec128
  key24 =
    Lib_IntVector_Intrinsics_vec128_xor(key14,
      Lib_IntVector_Intrinsics_vec128_shift_left(key14, 32U));
  Lib_IntVector_Intrinsics_vec128
  key34 =
    Lib_IntVector_Intrinsics_vec128_xor(key24,
      Lib_IntVector_Intrinsics_vec128_shift_left(key24, 32U));
  next13[0U] = Lib_IntVector_Intrinsics_vec128_xor(key34, next13[0U]);
  uint32_t klen3 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev03 = kex0 + klen3 * 6U;
  Lib_IntVector_Intrinsics_vec128 *prev13 = kex0 + klen3 * 7U;
  Lib_IntVector_Intrinsics_vec128 *next04 = kex0 + klen3 * 8U;
  Lib_IntVector_Intrinsics_vec128 *next14 = kex0 + klen3 * 9U;
  Lib_IntVector_Intrinsics_vec128
  v9 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev13[0U], 0x08U);
  next04[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v9, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key8 = prev03[0U];
  Lib_IntVector_Intrinsics_vec128
  key15 =
    Lib_IntVector_Intrinsics_vec128_xor(key8,
      Lib_IntVector_Intrinsics_vec128_shift_left(key8, 32U));
  Lib_IntVector_Intrinsics_vec128
  key25 =
    Lib_IntVector_Intrinsics_vec128_xor(key15,
      Lib_IntVector_Intrinsics_vec128_shift_left(key15, 32U));
  Lib_IntVector_Intrinsics_vec128
  key35 =
    Lib_IntVector_Intrinsics_vec128_xor(key25,
      Lib_IntVector_Intrinsics_vec128_shift_left(key25, 32U));
  next04[0U] = Lib_IntVector_Intrinsics_vec128_xor(key35, next04[0U]);
  Lib_IntVector_Intrinsics_vec128
  v10 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next04[0U], 0U);
  next14[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v10, 2U, 2U, 2U, 2U);
  Lib_IntVector_Intrinsics_vec128 key9 = prev13[0U];
  Lib_IntVector_Intrinsics_vec128
  key16 =
    Lib_IntVector_Intrinsics_vec128_xor(key9,
      Lib_IntVector_Intrinsics_vec128_shift_left(key9, 32U));
  Lib_IntVector_Intrinsics_vec128
  key26 =
    Lib_IntVector_Intrinsics_vec128_xor(key16,
      Lib_IntVector_Intrinsics_vec128_shift_left(key16, 32U));
  Lib_IntVector_Intrinsics_vec128
  key36 =
    Lib_IntVector_Intrinsics_vec128_xor(key26,
      Lib_IntVector_Intrinsics_vec128_shift_left(key26, 32U));
  next14[0U] = Lib_IntVector_Intrinsics_vec128_xor(key36, next14[0U]);
  uint32_t klen4 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev04 = kex0 + klen4 * 8U;
  Lib_IntVector_Intrinsics_vec128 *prev14 = kex0 + klen4 * 9U;
  Lib_IntVector_Intrinsics_vec128 *next05 = kex0 + klen4 * 10U;
  Lib_IntVector_Intrinsics_vec128 *next15 = kex0 + klen4 * 11U;
  Lib_IntVector_Intrinsics_vec128
  v12 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev14[0U], 0x10U);
  next05[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v12, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key17 = prev04[0U];
  Lib_IntVector_Intrinsics_vec128
  key18 =
    Lib_IntVector_Intrinsics_vec128_xor(key17,
      Lib_IntVector_Intrinsics_vec128_shift_left(key17, 32U));
  Lib_IntVector_Intrinsics_vec128
  key27 =
    Lib_IntVector_Intrinsics_vec128_xor(key18,
      Lib_IntVector_Intrinsics_vec128_shift_left(key18, 32U));
  Lib_IntVector_Intrinsics_vec128
  key37 =
    Lib_IntVector_Intrinsics_vec128_xor(key27,
      Lib_IntVector_Intrinsics_vec128_shift_left(key27, 32U));
  next05[0U] = Lib_IntVector_Intrinsics_vec128_xor(key37, next05[0U]);
  Lib_IntVector_Intrinsics_vec128
  v13 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next05[0U], 0U);
  next15[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v13, 2U, 2U, 2U, 2U);
  Lib_IntVector_Intrinsics_vec128 key19 = prev14[0U];
  Lib_IntVector_Intrinsics_vec128
  key110 =
    Lib_IntVector_Intrinsics_vec128_xor(key19,
      Lib_IntVector_Intrinsics_vec128_shift_left(key19, 32U));
  Lib_IntVector_Intrinsics_vec128
  key28 =
    Lib_IntVector_Intrinsics_vec128_xor(key110,
      Lib_IntVector_Intrinsics_vec128_shift_left(key110, 32U));
  Lib_IntVector_Intrinsics_vec128
  key38 =
    Lib_IntVector_Intrinsics_vec128_xor(key28,
      Lib_IntVector_Intrinsics_vec128_shift_left(key28, 32U));
  next15[0U] = Lib_IntVector_Intrinsics_vec128_xor(key38, next15[0U]);
  uint32_t klen5 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev05 = kex0 + klen5 * 10U;
  Lib_IntVector_Intrinsics_vec128 *prev15 = kex0 + klen5 * 11U;
  Lib_IntVector_Intrinsics_vec128 *next06 = kex0 + klen5 * 12U;
  Lib_IntVector_Intrinsics_vec128 *next1 = kex0 + klen5 * 13U;
  Lib_IntVector_Intrinsics_vec128
  v14 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev15[0U], 0x20U);
  next06[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v14, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key29 = prev05[0U];
  Lib_IntVector_Intrinsics_vec128
  key111 =
    Lib_IntVector_Intrinsics_vec128_xor(key29,
      Lib_IntVector_Intrinsics_vec128_shift_left(key29, 32U));
  Lib_IntVector_Intrinsics_vec128
  key210 =
    Lib_IntVector_Intrinsics_vec128_xor(key111,
      Lib_IntVector_Intrinsics_vec128_shift_left(key111, 32U));
  Lib_IntVector_Intrinsics_vec128
  key39 =
    Lib_IntVector_Intrinsics_vec128_xor(key210,
      Lib_IntVector_Intrinsics_vec128_shift_left(key210, 32U));
  next06[0U] = Lib_IntVector_Intrinsics_vec128_xor(key39, next06[0U]);
  Lib_IntVector_Intrinsics_vec128
  v15 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next06[0U], 0U);
  next1[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v15, 2U, 2U, 2U, 2U);
  Lib_IntVector_Intrinsics_vec128 key40 = prev15[0U];
  Lib_IntVector_Intrinsics_vec128
  key112 =
    Lib_IntVector_Intrinsics_vec128_xor(key40,
      Lib_IntVector_Intrinsics_vec128_shift_left(key40, 32U));
  Lib_IntVector_Intrinsics_vec128
  key211 =
    Lib_IntVector_Intrinsics_vec128_xor(key112,
      Lib_IntVector_Intrinsics_vec128_shift_left(key112, 32U));
  Lib_IntVector_Intrinsics_vec128
  key310 =
    Lib_IntVector_Intrinsics_vec128_xor(key211,
      Lib_IntVector_Intrinsics_vec128_shift_left(key211, 32U));
  next1[0U] = Lib_IntVector_Intrinsics_vec128_xor(key310, next1[0U]);
  uint32_t klen6 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev0 = kex0 + klen6 * 12U;
  Lib_IntVector_Intrinsics_vec128 *prev1 = kex0 + klen6 * 13U;
  Lib_IntVector_Intrinsics_vec128 *next0 = kex0 + klen6 * 14U;
  Lib_IntVector_Intrinsics_vec128
  v = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev1[0U], 0x40U);
  next0[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key41 = prev0[0U];
  Lib_IntVector_Intrinsics_vec128
  key113 =
    Lib_IntVector_Intrinsics_vec128_xor(key41,
      Lib_IntVector_Intrinsics_vec128_shift_left(key41, 32U));
  Lib_IntVector_Intrinsics_vec128
  key212 =
    Lib_IntVector_Intrinsics_vec128_xor(key113,
      Lib_IntVector_Intrinsics_vec128_shift_left(key113, 32U));
  Lib_IntVector_Intrinsics_vec128
  key311 =
    Lib_IntVector_Intrinsics_vec128_xor(key212,
      Lib_IntVector_Intrinsics_vec128_shift_left(key212, 32U));
  next0[0U] = Lib_IntVector_Intrinsics_vec128_xor(key311, next0[0U]);
  uint32_t rem = len % 64U;
  uint32_t nb = len / 64U;
  uint32_t rem1 = len % 64U;
  for (uint32_t i = 0U; i < nb; i++)
  {
    uint8_t *uu____0 = out + i * 64U;
    uint8_t *uu____1 = inp + i * 64U;
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 st[4U] KRML_POST_ALIGN(16) = { 0U };
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + 1U;
    Lib_IntVector_Intrinsics_vec128 *n1 = ctx;
    uint32_t counter0 = htobe32(c + i * 4U);
    uint32_t counter1 = htobe32(c + i * 4U + 1U);
    uint32_t counter2 = htobe32(c + i * 4U + 2U);
    uint32_t counter3 = htobe32(c + i * 4U + 3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n1[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, 3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, 3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, 3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, 3U);
    uint32_t klen7 = 1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen7;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + 14U * klen7;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    KRML_MAYBE_FOR13(i0,
      0U,
      13U,
      1U,
      Lib_IntVector_Intrinsics_vec128 *k1 = kr + i0 * 1U;
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(k1[0U], st[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(k1[0U], st[1U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(k1[0U], st[2U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(k1[0U], st[3U]););
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[1U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[2U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[3U]);
    Lib_IntVector_Intrinsics_vec128 v00 = Lib_IntVector_Intrinsics_vec128_load128_le(uu____1);
    Lib_IntVector_Intrinsics_vec128 v1 = Lib_IntVector_Intrinsics_vec128_load128_le(uu____1 + 16U);
    Lib_IntVector_Intrinsics_vec128 v2 = Lib_IntVector_Intrinsics_vec128_load128_le(uu____1 + 32U);
    Lib_IntVector_Intrinsics_vec128 v3 = Lib_IntVector_Intrinsics_vec128_load128_le(uu____1 + 48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v00, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(uu____0, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(uu____0 + 16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(uu____0 + 32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(uu____0 + 48U, v31);
  }
  if (rem1 > 0U)
  {
    uint8_t *uu____2 = out + nb * 64U;
    uint8_t last[64U] = { 0U };
    memcpy(last, inp + nb * 64U, rem * sizeof (uint8_t));
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 st[4U] KRML_POST_ALIGN(16) = { 0U };
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + 1U;
    Lib_IntVector_Intrinsics_vec128 *n1 = ctx;
    uint32_t counter0 = htobe32(c + nb * 4U);
    uint32_t counter1 = htobe32(c + nb * 4U + 1U);
    uint32_t counter2 = htobe32(c + nb * 4U + 2U);
    uint32_t counter3 = htobe32(c + nb * 4U + 3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n1[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, 3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, 3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, 3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, 3U);
    uint32_t klen7 = 1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen7;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + 14U * klen7;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    KRML_MAYBE_FOR13(i,
      0U,
      13U,
      1U,
      Lib_IntVector_Intrinsics_vec128 *k1 = kr + i * 1U;
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(k1[0U], st[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(k1[0U], st[1U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(k1[0U], st[2U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(k1[0U], st[3U]););
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[1U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[2U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(kn[0U], st[3U]);
    Lib_IntVector_Intrinsics_vec128 v00 = Lib_IntVector_Intrinsics_vec128_load128_le(last);
    Lib_IntVector_Intrinsics_vec128 v1 = Lib_IntVector_Intrinsics_vec128_load128_le(last + 16U);
    Lib_IntVector_Intrinsics_vec128 v2 = Lib_IntVector_Intrinsics_vec128_load128_le(last + 32U);
    Lib_IntVector_Intrinsics_vec128 v3 = Lib_IntVector_Intrinsics_vec128_load128_le(last + 48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v00, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(last, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + 16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + 32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + 48U, v31);
    memcpy(uu____2, last, rem * sizeof (uint8_t));
  }
}

