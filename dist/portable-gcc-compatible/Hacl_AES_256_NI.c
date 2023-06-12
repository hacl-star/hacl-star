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


#include "Hacl_AES_256_NI.h"

/* SNIPPET_START: Hacl_AES_256_NI_aes256_init */

void
Hacl_AES_256_NI_aes256_init(Lib_IntVector_Intrinsics_vec128 *ctx, uint8_t *key, uint8_t *nonce)
{
  Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *n = ctx;
  uint32_t klen = (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *next0 = kex;
  Lib_IntVector_Intrinsics_vec128 *next1 = kex + klen;
  next0[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(key);
  next1[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(key + (uint32_t)16U);
  Lib_IntVector_Intrinsics_vec128 *prev0 = next0;
  Lib_IntVector_Intrinsics_vec128 *prev1 = next1;
  Lib_IntVector_Intrinsics_vec128 *next01 = kex + klen * (uint32_t)2U;
  Lib_IntVector_Intrinsics_vec128 *next11 = kex + klen * (uint32_t)3U;
  Lib_IntVector_Intrinsics_vec128
  v0 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev1[0U], (uint8_t)0x01U);
  next01[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v0,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key1 = prev0[0U];
  Lib_IntVector_Intrinsics_vec128
  key2 =
    Lib_IntVector_Intrinsics_vec128_xor(key1,
      Lib_IntVector_Intrinsics_vec128_shift_left(key1, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key3 =
    Lib_IntVector_Intrinsics_vec128_xor(key2,
      Lib_IntVector_Intrinsics_vec128_shift_left(key2, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key4 =
    Lib_IntVector_Intrinsics_vec128_xor(key3,
      Lib_IntVector_Intrinsics_vec128_shift_left(key3, (uint32_t)32U));
  next01[0U] = Lib_IntVector_Intrinsics_vec128_xor(next01[0U], key4);
  Lib_IntVector_Intrinsics_vec128
  v1 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next01[0U], (uint8_t)0U);
  next11[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v1,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key10 = prev1[0U];
  Lib_IntVector_Intrinsics_vec128
  key20 =
    Lib_IntVector_Intrinsics_vec128_xor(key10,
      Lib_IntVector_Intrinsics_vec128_shift_left(key10, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key30 =
    Lib_IntVector_Intrinsics_vec128_xor(key20,
      Lib_IntVector_Intrinsics_vec128_shift_left(key20, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key40 =
    Lib_IntVector_Intrinsics_vec128_xor(key30,
      Lib_IntVector_Intrinsics_vec128_shift_left(key30, (uint32_t)32U));
  next11[0U] = Lib_IntVector_Intrinsics_vec128_xor(next11[0U], key40);
  Lib_IntVector_Intrinsics_vec128 *prev01 = next01;
  Lib_IntVector_Intrinsics_vec128 *prev11 = next11;
  Lib_IntVector_Intrinsics_vec128 *next02 = kex + klen * (uint32_t)4U;
  Lib_IntVector_Intrinsics_vec128 *next12 = kex + klen * (uint32_t)5U;
  Lib_IntVector_Intrinsics_vec128
  v2 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev11[0U], (uint8_t)0x02U);
  next02[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v2,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key11 = prev01[0U];
  Lib_IntVector_Intrinsics_vec128
  key21 =
    Lib_IntVector_Intrinsics_vec128_xor(key11,
      Lib_IntVector_Intrinsics_vec128_shift_left(key11, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key31 =
    Lib_IntVector_Intrinsics_vec128_xor(key21,
      Lib_IntVector_Intrinsics_vec128_shift_left(key21, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key41 =
    Lib_IntVector_Intrinsics_vec128_xor(key31,
      Lib_IntVector_Intrinsics_vec128_shift_left(key31, (uint32_t)32U));
  next02[0U] = Lib_IntVector_Intrinsics_vec128_xor(next02[0U], key41);
  Lib_IntVector_Intrinsics_vec128
  v3 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next02[0U], (uint8_t)0U);
  next12[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v3,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key12 = prev11[0U];
  Lib_IntVector_Intrinsics_vec128
  key22 =
    Lib_IntVector_Intrinsics_vec128_xor(key12,
      Lib_IntVector_Intrinsics_vec128_shift_left(key12, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key32 =
    Lib_IntVector_Intrinsics_vec128_xor(key22,
      Lib_IntVector_Intrinsics_vec128_shift_left(key22, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key42 =
    Lib_IntVector_Intrinsics_vec128_xor(key32,
      Lib_IntVector_Intrinsics_vec128_shift_left(key32, (uint32_t)32U));
  next12[0U] = Lib_IntVector_Intrinsics_vec128_xor(next12[0U], key42);
  Lib_IntVector_Intrinsics_vec128 *prev02 = next02;
  Lib_IntVector_Intrinsics_vec128 *prev12 = next12;
  Lib_IntVector_Intrinsics_vec128 *next03 = kex + klen * (uint32_t)6U;
  Lib_IntVector_Intrinsics_vec128 *next13 = kex + klen * (uint32_t)7U;
  Lib_IntVector_Intrinsics_vec128
  v4 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev12[0U], (uint8_t)0x04U);
  next03[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v4,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key13 = prev02[0U];
  Lib_IntVector_Intrinsics_vec128
  key23 =
    Lib_IntVector_Intrinsics_vec128_xor(key13,
      Lib_IntVector_Intrinsics_vec128_shift_left(key13, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key33 =
    Lib_IntVector_Intrinsics_vec128_xor(key23,
      Lib_IntVector_Intrinsics_vec128_shift_left(key23, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key43 =
    Lib_IntVector_Intrinsics_vec128_xor(key33,
      Lib_IntVector_Intrinsics_vec128_shift_left(key33, (uint32_t)32U));
  next03[0U] = Lib_IntVector_Intrinsics_vec128_xor(next03[0U], key43);
  Lib_IntVector_Intrinsics_vec128
  v5 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next03[0U], (uint8_t)0U);
  next13[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v5,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key14 = prev12[0U];
  Lib_IntVector_Intrinsics_vec128
  key24 =
    Lib_IntVector_Intrinsics_vec128_xor(key14,
      Lib_IntVector_Intrinsics_vec128_shift_left(key14, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key34 =
    Lib_IntVector_Intrinsics_vec128_xor(key24,
      Lib_IntVector_Intrinsics_vec128_shift_left(key24, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key44 =
    Lib_IntVector_Intrinsics_vec128_xor(key34,
      Lib_IntVector_Intrinsics_vec128_shift_left(key34, (uint32_t)32U));
  next13[0U] = Lib_IntVector_Intrinsics_vec128_xor(next13[0U], key44);
  Lib_IntVector_Intrinsics_vec128 *prev03 = next03;
  Lib_IntVector_Intrinsics_vec128 *prev13 = next13;
  Lib_IntVector_Intrinsics_vec128 *next04 = kex + klen * (uint32_t)8U;
  Lib_IntVector_Intrinsics_vec128 *next14 = kex + klen * (uint32_t)9U;
  Lib_IntVector_Intrinsics_vec128
  v6 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev13[0U], (uint8_t)0x08U);
  next04[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v6,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key15 = prev03[0U];
  Lib_IntVector_Intrinsics_vec128
  key25 =
    Lib_IntVector_Intrinsics_vec128_xor(key15,
      Lib_IntVector_Intrinsics_vec128_shift_left(key15, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key35 =
    Lib_IntVector_Intrinsics_vec128_xor(key25,
      Lib_IntVector_Intrinsics_vec128_shift_left(key25, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key45 =
    Lib_IntVector_Intrinsics_vec128_xor(key35,
      Lib_IntVector_Intrinsics_vec128_shift_left(key35, (uint32_t)32U));
  next04[0U] = Lib_IntVector_Intrinsics_vec128_xor(next04[0U], key45);
  Lib_IntVector_Intrinsics_vec128
  v7 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next04[0U], (uint8_t)0U);
  next14[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v7,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key16 = prev13[0U];
  Lib_IntVector_Intrinsics_vec128
  key26 =
    Lib_IntVector_Intrinsics_vec128_xor(key16,
      Lib_IntVector_Intrinsics_vec128_shift_left(key16, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key36 =
    Lib_IntVector_Intrinsics_vec128_xor(key26,
      Lib_IntVector_Intrinsics_vec128_shift_left(key26, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key46 =
    Lib_IntVector_Intrinsics_vec128_xor(key36,
      Lib_IntVector_Intrinsics_vec128_shift_left(key36, (uint32_t)32U));
  next14[0U] = Lib_IntVector_Intrinsics_vec128_xor(next14[0U], key46);
  Lib_IntVector_Intrinsics_vec128 *prev04 = next04;
  Lib_IntVector_Intrinsics_vec128 *prev14 = next14;
  Lib_IntVector_Intrinsics_vec128 *next05 = kex + klen * (uint32_t)10U;
  Lib_IntVector_Intrinsics_vec128 *next15 = kex + klen * (uint32_t)11U;
  Lib_IntVector_Intrinsics_vec128
  v8 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev14[0U], (uint8_t)0x10U);
  next05[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v8,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key17 = prev04[0U];
  Lib_IntVector_Intrinsics_vec128
  key27 =
    Lib_IntVector_Intrinsics_vec128_xor(key17,
      Lib_IntVector_Intrinsics_vec128_shift_left(key17, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key37 =
    Lib_IntVector_Intrinsics_vec128_xor(key27,
      Lib_IntVector_Intrinsics_vec128_shift_left(key27, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key47 =
    Lib_IntVector_Intrinsics_vec128_xor(key37,
      Lib_IntVector_Intrinsics_vec128_shift_left(key37, (uint32_t)32U));
  next05[0U] = Lib_IntVector_Intrinsics_vec128_xor(next05[0U], key47);
  Lib_IntVector_Intrinsics_vec128
  v9 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next05[0U], (uint8_t)0U);
  next15[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v9,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key18 = prev14[0U];
  Lib_IntVector_Intrinsics_vec128
  key28 =
    Lib_IntVector_Intrinsics_vec128_xor(key18,
      Lib_IntVector_Intrinsics_vec128_shift_left(key18, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key38 =
    Lib_IntVector_Intrinsics_vec128_xor(key28,
      Lib_IntVector_Intrinsics_vec128_shift_left(key28, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key48 =
    Lib_IntVector_Intrinsics_vec128_xor(key38,
      Lib_IntVector_Intrinsics_vec128_shift_left(key38, (uint32_t)32U));
  next15[0U] = Lib_IntVector_Intrinsics_vec128_xor(next15[0U], key48);
  Lib_IntVector_Intrinsics_vec128 *prev05 = next05;
  Lib_IntVector_Intrinsics_vec128 *prev15 = next15;
  Lib_IntVector_Intrinsics_vec128 *next06 = kex + klen * (uint32_t)12U;
  Lib_IntVector_Intrinsics_vec128 *next16 = kex + klen * (uint32_t)13U;
  Lib_IntVector_Intrinsics_vec128
  v10 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev15[0U], (uint8_t)0x20U);
  next06[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v10,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key19 = prev05[0U];
  Lib_IntVector_Intrinsics_vec128
  key29 =
    Lib_IntVector_Intrinsics_vec128_xor(key19,
      Lib_IntVector_Intrinsics_vec128_shift_left(key19, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key39 =
    Lib_IntVector_Intrinsics_vec128_xor(key29,
      Lib_IntVector_Intrinsics_vec128_shift_left(key29, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key49 =
    Lib_IntVector_Intrinsics_vec128_xor(key39,
      Lib_IntVector_Intrinsics_vec128_shift_left(key39, (uint32_t)32U));
  next06[0U] = Lib_IntVector_Intrinsics_vec128_xor(next06[0U], key49);
  Lib_IntVector_Intrinsics_vec128
  v11 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next06[0U], (uint8_t)0U);
  next16[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v11,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key110 = prev15[0U];
  Lib_IntVector_Intrinsics_vec128
  key210 =
    Lib_IntVector_Intrinsics_vec128_xor(key110,
      Lib_IntVector_Intrinsics_vec128_shift_left(key110, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key310 =
    Lib_IntVector_Intrinsics_vec128_xor(key210,
      Lib_IntVector_Intrinsics_vec128_shift_left(key210, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key410 =
    Lib_IntVector_Intrinsics_vec128_xor(key310,
      Lib_IntVector_Intrinsics_vec128_shift_left(key310, (uint32_t)32U));
  next16[0U] = Lib_IntVector_Intrinsics_vec128_xor(next16[0U], key410);
  Lib_IntVector_Intrinsics_vec128 *prev06 = next06;
  Lib_IntVector_Intrinsics_vec128 *prev16 = next16;
  Lib_IntVector_Intrinsics_vec128 *next07 = kex + klen * (uint32_t)14U;
  Lib_IntVector_Intrinsics_vec128
  v = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev16[0U], (uint8_t)0x40U);
  next07[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key111 = prev06[0U];
  Lib_IntVector_Intrinsics_vec128
  key211 =
    Lib_IntVector_Intrinsics_vec128_xor(key111,
      Lib_IntVector_Intrinsics_vec128_shift_left(key111, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key311 =
    Lib_IntVector_Intrinsics_vec128_xor(key211,
      Lib_IntVector_Intrinsics_vec128_shift_left(key211, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key411 =
    Lib_IntVector_Intrinsics_vec128_xor(key311,
      Lib_IntVector_Intrinsics_vec128_shift_left(key311, (uint32_t)32U));
  next07[0U] = Lib_IntVector_Intrinsics_vec128_xor(next07[0U], key411);
  uint8_t nb[16U] = { 0U };
  memcpy(nb, nonce, (uint32_t)12U * sizeof (uint8_t));
  n[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb);
}

/* SNIPPET_END: Hacl_AES_256_NI_aes256_init */

/* SNIPPET_START: Hacl_AES_256_NI_aes256_set_nonce */

void Hacl_AES_256_NI_aes256_set_nonce(Lib_IntVector_Intrinsics_vec128 *ctx, uint8_t *nonce)
{
  Lib_IntVector_Intrinsics_vec128 *n = ctx;
  uint8_t nb[16U] = { 0U };
  memcpy(nb, nonce, (uint32_t)12U * sizeof (uint8_t));
  n[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb);
}

/* SNIPPET_END: Hacl_AES_256_NI_aes256_set_nonce */

/* SNIPPET_START: Hacl_AES_256_NI_aes256_key_block */

void
Hacl_AES_256_NI_aes256_key_block(
  uint8_t *kb,
  Lib_IntVector_Intrinsics_vec128 *ctx,
  uint32_t counter
)
{
  Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *n = ctx;
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 st[4U] KRML_POST_ALIGN(16) = { 0U };
  uint32_t counter1 = counter;
  uint32_t counter0 = htobe32(counter1);
  uint32_t counter11 = htobe32(counter1 + (uint32_t)1U);
  uint32_t counter2 = htobe32(counter1 + (uint32_t)2U);
  uint32_t counter3 = htobe32(counter1 + (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 nonce0 = n[0U];
  st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
  st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter11, (uint32_t)3U);
  st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
  st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
  uint32_t klen = (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *k0 = kex;
  Lib_IntVector_Intrinsics_vec128 *kr = kex + klen;
  Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)14U * klen;
  st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
  st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
  st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
  st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
  KRML_MAYBE_FOR13(i,
    (uint32_t)0U,
    (uint32_t)13U,
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
  Lib_IntVector_Intrinsics_vec128_store128_le(kb, st[0U]);
}

/* SNIPPET_END: Hacl_AES_256_NI_aes256_key_block */

/* SNIPPET_START: Hacl_AES_256_NI_aes256_ctr */

void
Hacl_AES_256_NI_aes256_ctr(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  Lib_IntVector_Intrinsics_vec128 *ctx,
  uint32_t c
)
{
  uint32_t blocks64 = len / (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < blocks64; i++)
  {
    uint32_t ctr = c + i * (uint32_t)4U;
    uint8_t *ib = inp + i * (uint32_t)64U;
    uint8_t *ob = out + i * (uint32_t)64U;
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 st[4U] KRML_POST_ALIGN(16) = { 0U };
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *n = ctx;
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
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)14U * klen;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    KRML_MAYBE_FOR13(i0,
      (uint32_t)0U,
      (uint32_t)13U,
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
    uint32_t ctr = c + blocks64 * (uint32_t)4U;
    uint8_t *ib = inp + blocks64 * (uint32_t)64U;
    uint8_t *ob = out + blocks64 * (uint32_t)64U;
    memcpy(last, ib, rem * sizeof (uint8_t));
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 st[4U] KRML_POST_ALIGN(16) = { 0U };
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *n = ctx;
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
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)14U * klen;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    KRML_MAYBE_FOR13(i,
      (uint32_t)0U,
      (uint32_t)13U,
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
}

/* SNIPPET_END: Hacl_AES_256_NI_aes256_ctr */

/* SNIPPET_START: Hacl_AES_256_NI_aes256_ctr_encrypt */

inline void
Hacl_AES_256_NI_aes256_ctr_encrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint8_t *k,
  uint8_t *n,
  uint32_t c
)
{
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 ctx[16U] KRML_POST_ALIGN(16) = { 0U };
  Lib_IntVector_Intrinsics_vec128 *kex0 = ctx + (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *n10 = ctx;
  uint32_t klen = (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *next0 = kex0;
  Lib_IntVector_Intrinsics_vec128 *next1 = kex0 + klen;
  next0[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(k);
  next1[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(k + (uint32_t)16U);
  Lib_IntVector_Intrinsics_vec128 *prev0 = next0;
  Lib_IntVector_Intrinsics_vec128 *prev1 = next1;
  Lib_IntVector_Intrinsics_vec128 *next01 = kex0 + klen * (uint32_t)2U;
  Lib_IntVector_Intrinsics_vec128 *next11 = kex0 + klen * (uint32_t)3U;
  Lib_IntVector_Intrinsics_vec128
  v0 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev1[0U], (uint8_t)0x01U);
  next01[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v0,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key = prev0[0U];
  Lib_IntVector_Intrinsics_vec128
  key1 =
    Lib_IntVector_Intrinsics_vec128_xor(key,
      Lib_IntVector_Intrinsics_vec128_shift_left(key, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key2 =
    Lib_IntVector_Intrinsics_vec128_xor(key1,
      Lib_IntVector_Intrinsics_vec128_shift_left(key1, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key3 =
    Lib_IntVector_Intrinsics_vec128_xor(key2,
      Lib_IntVector_Intrinsics_vec128_shift_left(key2, (uint32_t)32U));
  next01[0U] = Lib_IntVector_Intrinsics_vec128_xor(next01[0U], key3);
  Lib_IntVector_Intrinsics_vec128
  v4 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next01[0U], (uint8_t)0U);
  next11[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v4,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key0 = prev1[0U];
  Lib_IntVector_Intrinsics_vec128
  key10 =
    Lib_IntVector_Intrinsics_vec128_xor(key0,
      Lib_IntVector_Intrinsics_vec128_shift_left(key0, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key20 =
    Lib_IntVector_Intrinsics_vec128_xor(key10,
      Lib_IntVector_Intrinsics_vec128_shift_left(key10, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key30 =
    Lib_IntVector_Intrinsics_vec128_xor(key20,
      Lib_IntVector_Intrinsics_vec128_shift_left(key20, (uint32_t)32U));
  next11[0U] = Lib_IntVector_Intrinsics_vec128_xor(next11[0U], key30);
  Lib_IntVector_Intrinsics_vec128 *prev01 = next01;
  Lib_IntVector_Intrinsics_vec128 *prev11 = next11;
  Lib_IntVector_Intrinsics_vec128 *next02 = kex0 + klen * (uint32_t)4U;
  Lib_IntVector_Intrinsics_vec128 *next12 = kex0 + klen * (uint32_t)5U;
  Lib_IntVector_Intrinsics_vec128
  v5 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev11[0U], (uint8_t)0x02U);
  next02[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v5,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key4 = prev01[0U];
  Lib_IntVector_Intrinsics_vec128
  key11 =
    Lib_IntVector_Intrinsics_vec128_xor(key4,
      Lib_IntVector_Intrinsics_vec128_shift_left(key4, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key21 =
    Lib_IntVector_Intrinsics_vec128_xor(key11,
      Lib_IntVector_Intrinsics_vec128_shift_left(key11, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key31 =
    Lib_IntVector_Intrinsics_vec128_xor(key21,
      Lib_IntVector_Intrinsics_vec128_shift_left(key21, (uint32_t)32U));
  next02[0U] = Lib_IntVector_Intrinsics_vec128_xor(next02[0U], key31);
  Lib_IntVector_Intrinsics_vec128
  v6 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next02[0U], (uint8_t)0U);
  next12[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v6,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key5 = prev11[0U];
  Lib_IntVector_Intrinsics_vec128
  key12 =
    Lib_IntVector_Intrinsics_vec128_xor(key5,
      Lib_IntVector_Intrinsics_vec128_shift_left(key5, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key22 =
    Lib_IntVector_Intrinsics_vec128_xor(key12,
      Lib_IntVector_Intrinsics_vec128_shift_left(key12, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key32 =
    Lib_IntVector_Intrinsics_vec128_xor(key22,
      Lib_IntVector_Intrinsics_vec128_shift_left(key22, (uint32_t)32U));
  next12[0U] = Lib_IntVector_Intrinsics_vec128_xor(next12[0U], key32);
  Lib_IntVector_Intrinsics_vec128 *prev02 = next02;
  Lib_IntVector_Intrinsics_vec128 *prev12 = next12;
  Lib_IntVector_Intrinsics_vec128 *next03 = kex0 + klen * (uint32_t)6U;
  Lib_IntVector_Intrinsics_vec128 *next13 = kex0 + klen * (uint32_t)7U;
  Lib_IntVector_Intrinsics_vec128
  v7 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev12[0U], (uint8_t)0x04U);
  next03[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v7,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key6 = prev02[0U];
  Lib_IntVector_Intrinsics_vec128
  key13 =
    Lib_IntVector_Intrinsics_vec128_xor(key6,
      Lib_IntVector_Intrinsics_vec128_shift_left(key6, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key23 =
    Lib_IntVector_Intrinsics_vec128_xor(key13,
      Lib_IntVector_Intrinsics_vec128_shift_left(key13, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key33 =
    Lib_IntVector_Intrinsics_vec128_xor(key23,
      Lib_IntVector_Intrinsics_vec128_shift_left(key23, (uint32_t)32U));
  next03[0U] = Lib_IntVector_Intrinsics_vec128_xor(next03[0U], key33);
  Lib_IntVector_Intrinsics_vec128
  v8 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next03[0U], (uint8_t)0U);
  next13[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v8,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key7 = prev12[0U];
  Lib_IntVector_Intrinsics_vec128
  key14 =
    Lib_IntVector_Intrinsics_vec128_xor(key7,
      Lib_IntVector_Intrinsics_vec128_shift_left(key7, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key24 =
    Lib_IntVector_Intrinsics_vec128_xor(key14,
      Lib_IntVector_Intrinsics_vec128_shift_left(key14, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key34 =
    Lib_IntVector_Intrinsics_vec128_xor(key24,
      Lib_IntVector_Intrinsics_vec128_shift_left(key24, (uint32_t)32U));
  next13[0U] = Lib_IntVector_Intrinsics_vec128_xor(next13[0U], key34);
  Lib_IntVector_Intrinsics_vec128 *prev03 = next03;
  Lib_IntVector_Intrinsics_vec128 *prev13 = next13;
  Lib_IntVector_Intrinsics_vec128 *next04 = kex0 + klen * (uint32_t)8U;
  Lib_IntVector_Intrinsics_vec128 *next14 = kex0 + klen * (uint32_t)9U;
  Lib_IntVector_Intrinsics_vec128
  v9 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev13[0U], (uint8_t)0x08U);
  next04[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v9,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key8 = prev03[0U];
  Lib_IntVector_Intrinsics_vec128
  key15 =
    Lib_IntVector_Intrinsics_vec128_xor(key8,
      Lib_IntVector_Intrinsics_vec128_shift_left(key8, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key25 =
    Lib_IntVector_Intrinsics_vec128_xor(key15,
      Lib_IntVector_Intrinsics_vec128_shift_left(key15, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key35 =
    Lib_IntVector_Intrinsics_vec128_xor(key25,
      Lib_IntVector_Intrinsics_vec128_shift_left(key25, (uint32_t)32U));
  next04[0U] = Lib_IntVector_Intrinsics_vec128_xor(next04[0U], key35);
  Lib_IntVector_Intrinsics_vec128
  v10 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next04[0U], (uint8_t)0U);
  next14[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v10,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key9 = prev13[0U];
  Lib_IntVector_Intrinsics_vec128
  key16 =
    Lib_IntVector_Intrinsics_vec128_xor(key9,
      Lib_IntVector_Intrinsics_vec128_shift_left(key9, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key26 =
    Lib_IntVector_Intrinsics_vec128_xor(key16,
      Lib_IntVector_Intrinsics_vec128_shift_left(key16, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key36 =
    Lib_IntVector_Intrinsics_vec128_xor(key26,
      Lib_IntVector_Intrinsics_vec128_shift_left(key26, (uint32_t)32U));
  next14[0U] = Lib_IntVector_Intrinsics_vec128_xor(next14[0U], key36);
  Lib_IntVector_Intrinsics_vec128 *prev04 = next04;
  Lib_IntVector_Intrinsics_vec128 *prev14 = next14;
  Lib_IntVector_Intrinsics_vec128 *next05 = kex0 + klen * (uint32_t)10U;
  Lib_IntVector_Intrinsics_vec128 *next15 = kex0 + klen * (uint32_t)11U;
  Lib_IntVector_Intrinsics_vec128
  v12 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev14[0U], (uint8_t)0x10U);
  next05[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v12,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key17 = prev04[0U];
  Lib_IntVector_Intrinsics_vec128
  key18 =
    Lib_IntVector_Intrinsics_vec128_xor(key17,
      Lib_IntVector_Intrinsics_vec128_shift_left(key17, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key27 =
    Lib_IntVector_Intrinsics_vec128_xor(key18,
      Lib_IntVector_Intrinsics_vec128_shift_left(key18, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key37 =
    Lib_IntVector_Intrinsics_vec128_xor(key27,
      Lib_IntVector_Intrinsics_vec128_shift_left(key27, (uint32_t)32U));
  next05[0U] = Lib_IntVector_Intrinsics_vec128_xor(next05[0U], key37);
  Lib_IntVector_Intrinsics_vec128
  v13 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next05[0U], (uint8_t)0U);
  next15[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v13,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key19 = prev14[0U];
  Lib_IntVector_Intrinsics_vec128
  key110 =
    Lib_IntVector_Intrinsics_vec128_xor(key19,
      Lib_IntVector_Intrinsics_vec128_shift_left(key19, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key28 =
    Lib_IntVector_Intrinsics_vec128_xor(key110,
      Lib_IntVector_Intrinsics_vec128_shift_left(key110, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key38 =
    Lib_IntVector_Intrinsics_vec128_xor(key28,
      Lib_IntVector_Intrinsics_vec128_shift_left(key28, (uint32_t)32U));
  next15[0U] = Lib_IntVector_Intrinsics_vec128_xor(next15[0U], key38);
  Lib_IntVector_Intrinsics_vec128 *prev05 = next05;
  Lib_IntVector_Intrinsics_vec128 *prev15 = next15;
  Lib_IntVector_Intrinsics_vec128 *next06 = kex0 + klen * (uint32_t)12U;
  Lib_IntVector_Intrinsics_vec128 *next16 = kex0 + klen * (uint32_t)13U;
  Lib_IntVector_Intrinsics_vec128
  v14 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev15[0U], (uint8_t)0x20U);
  next06[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v14,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key29 = prev05[0U];
  Lib_IntVector_Intrinsics_vec128
  key111 =
    Lib_IntVector_Intrinsics_vec128_xor(key29,
      Lib_IntVector_Intrinsics_vec128_shift_left(key29, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key210 =
    Lib_IntVector_Intrinsics_vec128_xor(key111,
      Lib_IntVector_Intrinsics_vec128_shift_left(key111, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key39 =
    Lib_IntVector_Intrinsics_vec128_xor(key210,
      Lib_IntVector_Intrinsics_vec128_shift_left(key210, (uint32_t)32U));
  next06[0U] = Lib_IntVector_Intrinsics_vec128_xor(next06[0U], key39);
  Lib_IntVector_Intrinsics_vec128
  v15 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next06[0U], (uint8_t)0U);
  next16[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v15,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key40 = prev15[0U];
  Lib_IntVector_Intrinsics_vec128
  key112 =
    Lib_IntVector_Intrinsics_vec128_xor(key40,
      Lib_IntVector_Intrinsics_vec128_shift_left(key40, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key211 =
    Lib_IntVector_Intrinsics_vec128_xor(key112,
      Lib_IntVector_Intrinsics_vec128_shift_left(key112, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key310 =
    Lib_IntVector_Intrinsics_vec128_xor(key211,
      Lib_IntVector_Intrinsics_vec128_shift_left(key211, (uint32_t)32U));
  next16[0U] = Lib_IntVector_Intrinsics_vec128_xor(next16[0U], key310);
  Lib_IntVector_Intrinsics_vec128 *prev06 = next06;
  Lib_IntVector_Intrinsics_vec128 *prev16 = next16;
  Lib_IntVector_Intrinsics_vec128 *next07 = kex0 + klen * (uint32_t)14U;
  Lib_IntVector_Intrinsics_vec128
  v = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev16[0U], (uint8_t)0x40U);
  next07[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key41 = prev06[0U];
  Lib_IntVector_Intrinsics_vec128
  key113 =
    Lib_IntVector_Intrinsics_vec128_xor(key41,
      Lib_IntVector_Intrinsics_vec128_shift_left(key41, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key212 =
    Lib_IntVector_Intrinsics_vec128_xor(key113,
      Lib_IntVector_Intrinsics_vec128_shift_left(key113, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key311 =
    Lib_IntVector_Intrinsics_vec128_xor(key212,
      Lib_IntVector_Intrinsics_vec128_shift_left(key212, (uint32_t)32U));
  next07[0U] = Lib_IntVector_Intrinsics_vec128_xor(next07[0U], key311);
  uint8_t nb[16U] = { 0U };
  memcpy(nb, n, (uint32_t)12U * sizeof (uint8_t));
  n10[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb);
  uint32_t blocks64 = len / (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < blocks64; i++)
  {
    uint32_t ctr = c + i * (uint32_t)4U;
    uint8_t *ib = inp + i * (uint32_t)64U;
    uint8_t *ob = out + i * (uint32_t)64U;
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 st[4U] KRML_POST_ALIGN(16) = { 0U };
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *n1 = ctx;
    uint32_t counter = ctr;
    uint32_t counter0 = htobe32(counter);
    uint32_t counter1 = htobe32(counter + (uint32_t)1U);
    uint32_t counter2 = htobe32(counter + (uint32_t)2U);
    uint32_t counter3 = htobe32(counter + (uint32_t)3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n1[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
    uint32_t klen0 = (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen0;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)14U * klen0;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    KRML_MAYBE_FOR13(i0,
      (uint32_t)0U,
      (uint32_t)13U,
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
    Lib_IntVector_Intrinsics_vec128 v00 = Lib_IntVector_Intrinsics_vec128_load128_le(ib);
    Lib_IntVector_Intrinsics_vec128
    v1 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)16U);
    Lib_IntVector_Intrinsics_vec128
    v2 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)32U);
    Lib_IntVector_Intrinsics_vec128
    v3 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v00, st[0U]);
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
    uint32_t ctr = c + blocks64 * (uint32_t)4U;
    uint8_t *ib = inp + blocks64 * (uint32_t)64U;
    uint8_t *ob = out + blocks64 * (uint32_t)64U;
    memcpy(last, ib, rem * sizeof (uint8_t));
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 st[4U] KRML_POST_ALIGN(16) = { 0U };
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *n1 = ctx;
    uint32_t counter = ctr;
    uint32_t counter0 = htobe32(counter);
    uint32_t counter1 = htobe32(counter + (uint32_t)1U);
    uint32_t counter2 = htobe32(counter + (uint32_t)2U);
    uint32_t counter3 = htobe32(counter + (uint32_t)3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n1[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
    uint32_t klen0 = (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen0;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)14U * klen0;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    KRML_MAYBE_FOR13(i,
      (uint32_t)0U,
      (uint32_t)13U,
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
    Lib_IntVector_Intrinsics_vec128 v00 = Lib_IntVector_Intrinsics_vec128_load128_le(last);
    Lib_IntVector_Intrinsics_vec128
    v1 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)16U);
    Lib_IntVector_Intrinsics_vec128
    v2 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)32U);
    Lib_IntVector_Intrinsics_vec128
    v3 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v00, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(last, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)48U, v31);
    memcpy(ob, last, rem * sizeof (uint8_t));
  }
}

/* SNIPPET_END: Hacl_AES_256_NI_aes256_ctr_encrypt */

/* SNIPPET_START: Hacl_AES_256_NI_aes256_ctr_decrypt */

inline void
Hacl_AES_256_NI_aes256_ctr_decrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint8_t *k,
  uint8_t *n,
  uint32_t c
)
{
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 ctx[16U] KRML_POST_ALIGN(16) = { 0U };
  Lib_IntVector_Intrinsics_vec128 *kex0 = ctx + (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *n10 = ctx;
  uint32_t klen = (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *next0 = kex0;
  Lib_IntVector_Intrinsics_vec128 *next1 = kex0 + klen;
  next0[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(k);
  next1[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(k + (uint32_t)16U);
  Lib_IntVector_Intrinsics_vec128 *prev0 = next0;
  Lib_IntVector_Intrinsics_vec128 *prev1 = next1;
  Lib_IntVector_Intrinsics_vec128 *next01 = kex0 + klen * (uint32_t)2U;
  Lib_IntVector_Intrinsics_vec128 *next11 = kex0 + klen * (uint32_t)3U;
  Lib_IntVector_Intrinsics_vec128
  v0 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev1[0U], (uint8_t)0x01U);
  next01[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v0,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key = prev0[0U];
  Lib_IntVector_Intrinsics_vec128
  key1 =
    Lib_IntVector_Intrinsics_vec128_xor(key,
      Lib_IntVector_Intrinsics_vec128_shift_left(key, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key2 =
    Lib_IntVector_Intrinsics_vec128_xor(key1,
      Lib_IntVector_Intrinsics_vec128_shift_left(key1, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key3 =
    Lib_IntVector_Intrinsics_vec128_xor(key2,
      Lib_IntVector_Intrinsics_vec128_shift_left(key2, (uint32_t)32U));
  next01[0U] = Lib_IntVector_Intrinsics_vec128_xor(next01[0U], key3);
  Lib_IntVector_Intrinsics_vec128
  v4 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next01[0U], (uint8_t)0U);
  next11[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v4,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key0 = prev1[0U];
  Lib_IntVector_Intrinsics_vec128
  key10 =
    Lib_IntVector_Intrinsics_vec128_xor(key0,
      Lib_IntVector_Intrinsics_vec128_shift_left(key0, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key20 =
    Lib_IntVector_Intrinsics_vec128_xor(key10,
      Lib_IntVector_Intrinsics_vec128_shift_left(key10, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key30 =
    Lib_IntVector_Intrinsics_vec128_xor(key20,
      Lib_IntVector_Intrinsics_vec128_shift_left(key20, (uint32_t)32U));
  next11[0U] = Lib_IntVector_Intrinsics_vec128_xor(next11[0U], key30);
  Lib_IntVector_Intrinsics_vec128 *prev01 = next01;
  Lib_IntVector_Intrinsics_vec128 *prev11 = next11;
  Lib_IntVector_Intrinsics_vec128 *next02 = kex0 + klen * (uint32_t)4U;
  Lib_IntVector_Intrinsics_vec128 *next12 = kex0 + klen * (uint32_t)5U;
  Lib_IntVector_Intrinsics_vec128
  v5 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev11[0U], (uint8_t)0x02U);
  next02[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v5,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key4 = prev01[0U];
  Lib_IntVector_Intrinsics_vec128
  key11 =
    Lib_IntVector_Intrinsics_vec128_xor(key4,
      Lib_IntVector_Intrinsics_vec128_shift_left(key4, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key21 =
    Lib_IntVector_Intrinsics_vec128_xor(key11,
      Lib_IntVector_Intrinsics_vec128_shift_left(key11, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key31 =
    Lib_IntVector_Intrinsics_vec128_xor(key21,
      Lib_IntVector_Intrinsics_vec128_shift_left(key21, (uint32_t)32U));
  next02[0U] = Lib_IntVector_Intrinsics_vec128_xor(next02[0U], key31);
  Lib_IntVector_Intrinsics_vec128
  v6 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next02[0U], (uint8_t)0U);
  next12[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v6,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key5 = prev11[0U];
  Lib_IntVector_Intrinsics_vec128
  key12 =
    Lib_IntVector_Intrinsics_vec128_xor(key5,
      Lib_IntVector_Intrinsics_vec128_shift_left(key5, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key22 =
    Lib_IntVector_Intrinsics_vec128_xor(key12,
      Lib_IntVector_Intrinsics_vec128_shift_left(key12, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key32 =
    Lib_IntVector_Intrinsics_vec128_xor(key22,
      Lib_IntVector_Intrinsics_vec128_shift_left(key22, (uint32_t)32U));
  next12[0U] = Lib_IntVector_Intrinsics_vec128_xor(next12[0U], key32);
  Lib_IntVector_Intrinsics_vec128 *prev02 = next02;
  Lib_IntVector_Intrinsics_vec128 *prev12 = next12;
  Lib_IntVector_Intrinsics_vec128 *next03 = kex0 + klen * (uint32_t)6U;
  Lib_IntVector_Intrinsics_vec128 *next13 = kex0 + klen * (uint32_t)7U;
  Lib_IntVector_Intrinsics_vec128
  v7 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev12[0U], (uint8_t)0x04U);
  next03[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v7,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key6 = prev02[0U];
  Lib_IntVector_Intrinsics_vec128
  key13 =
    Lib_IntVector_Intrinsics_vec128_xor(key6,
      Lib_IntVector_Intrinsics_vec128_shift_left(key6, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key23 =
    Lib_IntVector_Intrinsics_vec128_xor(key13,
      Lib_IntVector_Intrinsics_vec128_shift_left(key13, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key33 =
    Lib_IntVector_Intrinsics_vec128_xor(key23,
      Lib_IntVector_Intrinsics_vec128_shift_left(key23, (uint32_t)32U));
  next03[0U] = Lib_IntVector_Intrinsics_vec128_xor(next03[0U], key33);
  Lib_IntVector_Intrinsics_vec128
  v8 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next03[0U], (uint8_t)0U);
  next13[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v8,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key7 = prev12[0U];
  Lib_IntVector_Intrinsics_vec128
  key14 =
    Lib_IntVector_Intrinsics_vec128_xor(key7,
      Lib_IntVector_Intrinsics_vec128_shift_left(key7, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key24 =
    Lib_IntVector_Intrinsics_vec128_xor(key14,
      Lib_IntVector_Intrinsics_vec128_shift_left(key14, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key34 =
    Lib_IntVector_Intrinsics_vec128_xor(key24,
      Lib_IntVector_Intrinsics_vec128_shift_left(key24, (uint32_t)32U));
  next13[0U] = Lib_IntVector_Intrinsics_vec128_xor(next13[0U], key34);
  Lib_IntVector_Intrinsics_vec128 *prev03 = next03;
  Lib_IntVector_Intrinsics_vec128 *prev13 = next13;
  Lib_IntVector_Intrinsics_vec128 *next04 = kex0 + klen * (uint32_t)8U;
  Lib_IntVector_Intrinsics_vec128 *next14 = kex0 + klen * (uint32_t)9U;
  Lib_IntVector_Intrinsics_vec128
  v9 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev13[0U], (uint8_t)0x08U);
  next04[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v9,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key8 = prev03[0U];
  Lib_IntVector_Intrinsics_vec128
  key15 =
    Lib_IntVector_Intrinsics_vec128_xor(key8,
      Lib_IntVector_Intrinsics_vec128_shift_left(key8, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key25 =
    Lib_IntVector_Intrinsics_vec128_xor(key15,
      Lib_IntVector_Intrinsics_vec128_shift_left(key15, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key35 =
    Lib_IntVector_Intrinsics_vec128_xor(key25,
      Lib_IntVector_Intrinsics_vec128_shift_left(key25, (uint32_t)32U));
  next04[0U] = Lib_IntVector_Intrinsics_vec128_xor(next04[0U], key35);
  Lib_IntVector_Intrinsics_vec128
  v10 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next04[0U], (uint8_t)0U);
  next14[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v10,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key9 = prev13[0U];
  Lib_IntVector_Intrinsics_vec128
  key16 =
    Lib_IntVector_Intrinsics_vec128_xor(key9,
      Lib_IntVector_Intrinsics_vec128_shift_left(key9, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key26 =
    Lib_IntVector_Intrinsics_vec128_xor(key16,
      Lib_IntVector_Intrinsics_vec128_shift_left(key16, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key36 =
    Lib_IntVector_Intrinsics_vec128_xor(key26,
      Lib_IntVector_Intrinsics_vec128_shift_left(key26, (uint32_t)32U));
  next14[0U] = Lib_IntVector_Intrinsics_vec128_xor(next14[0U], key36);
  Lib_IntVector_Intrinsics_vec128 *prev04 = next04;
  Lib_IntVector_Intrinsics_vec128 *prev14 = next14;
  Lib_IntVector_Intrinsics_vec128 *next05 = kex0 + klen * (uint32_t)10U;
  Lib_IntVector_Intrinsics_vec128 *next15 = kex0 + klen * (uint32_t)11U;
  Lib_IntVector_Intrinsics_vec128
  v12 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev14[0U], (uint8_t)0x10U);
  next05[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v12,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key17 = prev04[0U];
  Lib_IntVector_Intrinsics_vec128
  key18 =
    Lib_IntVector_Intrinsics_vec128_xor(key17,
      Lib_IntVector_Intrinsics_vec128_shift_left(key17, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key27 =
    Lib_IntVector_Intrinsics_vec128_xor(key18,
      Lib_IntVector_Intrinsics_vec128_shift_left(key18, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key37 =
    Lib_IntVector_Intrinsics_vec128_xor(key27,
      Lib_IntVector_Intrinsics_vec128_shift_left(key27, (uint32_t)32U));
  next05[0U] = Lib_IntVector_Intrinsics_vec128_xor(next05[0U], key37);
  Lib_IntVector_Intrinsics_vec128
  v13 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next05[0U], (uint8_t)0U);
  next15[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v13,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key19 = prev14[0U];
  Lib_IntVector_Intrinsics_vec128
  key110 =
    Lib_IntVector_Intrinsics_vec128_xor(key19,
      Lib_IntVector_Intrinsics_vec128_shift_left(key19, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key28 =
    Lib_IntVector_Intrinsics_vec128_xor(key110,
      Lib_IntVector_Intrinsics_vec128_shift_left(key110, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key38 =
    Lib_IntVector_Intrinsics_vec128_xor(key28,
      Lib_IntVector_Intrinsics_vec128_shift_left(key28, (uint32_t)32U));
  next15[0U] = Lib_IntVector_Intrinsics_vec128_xor(next15[0U], key38);
  Lib_IntVector_Intrinsics_vec128 *prev05 = next05;
  Lib_IntVector_Intrinsics_vec128 *prev15 = next15;
  Lib_IntVector_Intrinsics_vec128 *next06 = kex0 + klen * (uint32_t)12U;
  Lib_IntVector_Intrinsics_vec128 *next16 = kex0 + klen * (uint32_t)13U;
  Lib_IntVector_Intrinsics_vec128
  v14 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev15[0U], (uint8_t)0x20U);
  next06[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v14,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key29 = prev05[0U];
  Lib_IntVector_Intrinsics_vec128
  key111 =
    Lib_IntVector_Intrinsics_vec128_xor(key29,
      Lib_IntVector_Intrinsics_vec128_shift_left(key29, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key210 =
    Lib_IntVector_Intrinsics_vec128_xor(key111,
      Lib_IntVector_Intrinsics_vec128_shift_left(key111, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key39 =
    Lib_IntVector_Intrinsics_vec128_xor(key210,
      Lib_IntVector_Intrinsics_vec128_shift_left(key210, (uint32_t)32U));
  next06[0U] = Lib_IntVector_Intrinsics_vec128_xor(next06[0U], key39);
  Lib_IntVector_Intrinsics_vec128
  v15 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next06[0U], (uint8_t)0U);
  next16[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v15,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key40 = prev15[0U];
  Lib_IntVector_Intrinsics_vec128
  key112 =
    Lib_IntVector_Intrinsics_vec128_xor(key40,
      Lib_IntVector_Intrinsics_vec128_shift_left(key40, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key211 =
    Lib_IntVector_Intrinsics_vec128_xor(key112,
      Lib_IntVector_Intrinsics_vec128_shift_left(key112, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key310 =
    Lib_IntVector_Intrinsics_vec128_xor(key211,
      Lib_IntVector_Intrinsics_vec128_shift_left(key211, (uint32_t)32U));
  next16[0U] = Lib_IntVector_Intrinsics_vec128_xor(next16[0U], key310);
  Lib_IntVector_Intrinsics_vec128 *prev06 = next06;
  Lib_IntVector_Intrinsics_vec128 *prev16 = next16;
  Lib_IntVector_Intrinsics_vec128 *next07 = kex0 + klen * (uint32_t)14U;
  Lib_IntVector_Intrinsics_vec128
  v = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev16[0U], (uint8_t)0x40U);
  next07[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key41 = prev06[0U];
  Lib_IntVector_Intrinsics_vec128
  key113 =
    Lib_IntVector_Intrinsics_vec128_xor(key41,
      Lib_IntVector_Intrinsics_vec128_shift_left(key41, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key212 =
    Lib_IntVector_Intrinsics_vec128_xor(key113,
      Lib_IntVector_Intrinsics_vec128_shift_left(key113, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key311 =
    Lib_IntVector_Intrinsics_vec128_xor(key212,
      Lib_IntVector_Intrinsics_vec128_shift_left(key212, (uint32_t)32U));
  next07[0U] = Lib_IntVector_Intrinsics_vec128_xor(next07[0U], key311);
  uint8_t nb[16U] = { 0U };
  memcpy(nb, n, (uint32_t)12U * sizeof (uint8_t));
  n10[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb);
  uint32_t blocks64 = len / (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < blocks64; i++)
  {
    uint32_t ctr = c + i * (uint32_t)4U;
    uint8_t *ib = inp + i * (uint32_t)64U;
    uint8_t *ob = out + i * (uint32_t)64U;
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 st[4U] KRML_POST_ALIGN(16) = { 0U };
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *n1 = ctx;
    uint32_t counter = ctr;
    uint32_t counter0 = htobe32(counter);
    uint32_t counter1 = htobe32(counter + (uint32_t)1U);
    uint32_t counter2 = htobe32(counter + (uint32_t)2U);
    uint32_t counter3 = htobe32(counter + (uint32_t)3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n1[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
    uint32_t klen0 = (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen0;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)14U * klen0;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    KRML_MAYBE_FOR13(i0,
      (uint32_t)0U,
      (uint32_t)13U,
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
    Lib_IntVector_Intrinsics_vec128 v00 = Lib_IntVector_Intrinsics_vec128_load128_le(ib);
    Lib_IntVector_Intrinsics_vec128
    v1 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)16U);
    Lib_IntVector_Intrinsics_vec128
    v2 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)32U);
    Lib_IntVector_Intrinsics_vec128
    v3 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v00, st[0U]);
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
    uint32_t ctr = c + blocks64 * (uint32_t)4U;
    uint8_t *ib = inp + blocks64 * (uint32_t)64U;
    uint8_t *ob = out + blocks64 * (uint32_t)64U;
    memcpy(last, ib, rem * sizeof (uint8_t));
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 st[4U] KRML_POST_ALIGN(16) = { 0U };
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *n1 = ctx;
    uint32_t counter = ctr;
    uint32_t counter0 = htobe32(counter);
    uint32_t counter1 = htobe32(counter + (uint32_t)1U);
    uint32_t counter2 = htobe32(counter + (uint32_t)2U);
    uint32_t counter3 = htobe32(counter + (uint32_t)3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n1[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
    uint32_t klen0 = (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen0;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)14U * klen0;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    KRML_MAYBE_FOR13(i,
      (uint32_t)0U,
      (uint32_t)13U,
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
    Lib_IntVector_Intrinsics_vec128 v00 = Lib_IntVector_Intrinsics_vec128_load128_le(last);
    Lib_IntVector_Intrinsics_vec128
    v1 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)16U);
    Lib_IntVector_Intrinsics_vec128
    v2 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)32U);
    Lib_IntVector_Intrinsics_vec128
    v3 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v00, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(last, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)48U, v31);
    memcpy(ob, last, rem * sizeof (uint8_t));
  }
}

/* SNIPPET_END: Hacl_AES_256_NI_aes256_ctr_decrypt */

