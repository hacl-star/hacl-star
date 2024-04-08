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


#include "Hacl_AES_128_CTR32_NI.h"

inline void
Hacl_AES_128_CTR32_NI_aes128_init(
  Lib_IntVector_Intrinsics_vec128 *ctx,
  uint8_t *key,
  uint8_t *nonce
)
{
  Lib_IntVector_Intrinsics_vec128 *kex = ctx + 1U;
  Lib_IntVector_Intrinsics_vec128 *n = ctx;
  uint8_t nb[16U] = { 0U };
  memcpy(nb, nonce, 12U * sizeof (uint8_t));
  n[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb);
  Lib_IntVector_Intrinsics_vec128 *uu____0 = kex;
  uu____0[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(key);
  uint32_t klen = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev0 = kex + klen * 0U;
  Lib_IntVector_Intrinsics_vec128 *next0 = kex + klen * 1U;
  Lib_IntVector_Intrinsics_vec128
  v0 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev0[0U], 0x01U);
  next0[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v0, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key1 = prev0[0U];
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
  next0[0U] = Lib_IntVector_Intrinsics_vec128_xor(key4, next0[0U]);
  uint32_t klen0 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev1 = kex + klen0 * 1U;
  Lib_IntVector_Intrinsics_vec128 *next1 = kex + klen0 * 2U;
  Lib_IntVector_Intrinsics_vec128
  v1 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev1[0U], 0x02U);
  next1[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v1, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key10 = prev1[0U];
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
  next1[0U] = Lib_IntVector_Intrinsics_vec128_xor(key40, next1[0U]);
  uint32_t klen1 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev2 = kex + klen1 * 2U;
  Lib_IntVector_Intrinsics_vec128 *next2 = kex + klen1 * 3U;
  Lib_IntVector_Intrinsics_vec128
  v2 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev2[0U], 0x04U);
  next2[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v2, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key11 = prev2[0U];
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
  next2[0U] = Lib_IntVector_Intrinsics_vec128_xor(key41, next2[0U]);
  uint32_t klen2 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev3 = kex + klen2 * 3U;
  Lib_IntVector_Intrinsics_vec128 *next3 = kex + klen2 * 4U;
  Lib_IntVector_Intrinsics_vec128
  v3 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev3[0U], 0x08U);
  next3[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v3, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key12 = prev3[0U];
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
  next3[0U] = Lib_IntVector_Intrinsics_vec128_xor(key42, next3[0U]);
  uint32_t klen3 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev4 = kex + klen3 * 4U;
  Lib_IntVector_Intrinsics_vec128 *next4 = kex + klen3 * 5U;
  Lib_IntVector_Intrinsics_vec128
  v4 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev4[0U], 0x10U);
  next4[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v4, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key13 = prev4[0U];
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
  next4[0U] = Lib_IntVector_Intrinsics_vec128_xor(key43, next4[0U]);
  uint32_t klen4 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev5 = kex + klen4 * 5U;
  Lib_IntVector_Intrinsics_vec128 *next5 = kex + klen4 * 6U;
  Lib_IntVector_Intrinsics_vec128
  v5 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev5[0U], 0x20U);
  next5[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v5, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key14 = prev5[0U];
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
  next5[0U] = Lib_IntVector_Intrinsics_vec128_xor(key44, next5[0U]);
  uint32_t klen5 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev6 = kex + klen5 * 6U;
  Lib_IntVector_Intrinsics_vec128 *next6 = kex + klen5 * 7U;
  Lib_IntVector_Intrinsics_vec128
  v6 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev6[0U], 0x40U);
  next6[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v6, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key15 = prev6[0U];
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
  next6[0U] = Lib_IntVector_Intrinsics_vec128_xor(key45, next6[0U]);
  uint32_t klen6 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev7 = kex + klen6 * 7U;
  Lib_IntVector_Intrinsics_vec128 *next7 = kex + klen6 * 8U;
  Lib_IntVector_Intrinsics_vec128
  v7 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev7[0U], 0x80U);
  next7[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v7, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key16 = prev7[0U];
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
  next7[0U] = Lib_IntVector_Intrinsics_vec128_xor(key46, next7[0U]);
  uint32_t klen7 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev8 = kex + klen7 * 8U;
  Lib_IntVector_Intrinsics_vec128 *next8 = kex + klen7 * 9U;
  Lib_IntVector_Intrinsics_vec128
  v8 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev8[0U], 0x1bU);
  next8[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v8, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key17 = prev8[0U];
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
  next8[0U] = Lib_IntVector_Intrinsics_vec128_xor(key47, next8[0U]);
  uint32_t klen8 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev = kex + klen8 * 9U;
  Lib_IntVector_Intrinsics_vec128 *next = kex + klen8 * 10U;
  Lib_IntVector_Intrinsics_vec128
  v = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev[0U], 0x36U);
  next[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key18 = prev[0U];
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
  next[0U] = Lib_IntVector_Intrinsics_vec128_xor(key48, next[0U]);
}

inline void
Hacl_AES_128_CTR32_NI_aes128_set_nonce(Lib_IntVector_Intrinsics_vec128 *ctx, uint8_t *nonce)
{
  Lib_IntVector_Intrinsics_vec128 *n = ctx;
  uint8_t nb[16U] = { 0U };
  memcpy(nb, nonce, 12U * sizeof (uint8_t));
  n[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb);
}

inline void
Hacl_AES_128_CTR32_NI_aes128_key_block(
  uint8_t *kb,
  Lib_IntVector_Intrinsics_vec128 *ctx,
  uint32_t counter
)
{
  Lib_IntVector_Intrinsics_vec128 *kex = ctx + 1U;
  Lib_IntVector_Intrinsics_vec128 *n = ctx;
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 st[4U] KRML_POST_ALIGN(16) = { 0U };
  uint32_t counter0 = htobe32(counter);
  uint32_t counter1 = htobe32(counter + 1U);
  uint32_t counter2 = htobe32(counter + 2U);
  uint32_t counter3 = htobe32(counter + 3U);
  Lib_IntVector_Intrinsics_vec128 nonce0 = n[0U];
  st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, 3U);
  st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, 3U);
  st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, 3U);
  st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, 3U);
  uint32_t klen = 1U;
  Lib_IntVector_Intrinsics_vec128 *k0 = kex;
  Lib_IntVector_Intrinsics_vec128 *kr = kex + klen;
  Lib_IntVector_Intrinsics_vec128 *kn = kex + 10U * klen;
  st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
  st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
  st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
  st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
  KRML_MAYBE_FOR9(i,
    0U,
    9U,
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
  Lib_IntVector_Intrinsics_vec128_store128_le(kb, st[0U]);
}

inline void
Hacl_AES_128_CTR32_NI_aes128_ctr_encrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint8_t *k,
  uint8_t *n,
  uint32_t c
)
{
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 ctx[12U] KRML_POST_ALIGN(16) = { 0U };
  Lib_IntVector_Intrinsics_vec128 *kex0 = ctx + 1U;
  Lib_IntVector_Intrinsics_vec128 *n10 = ctx;
  uint8_t nb0[16U] = { 0U };
  memcpy(nb0, n, 12U * sizeof (uint8_t));
  n10[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb0);
  Lib_IntVector_Intrinsics_vec128 *uu____0 = kex0;
  uu____0[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(k);
  uint32_t klen = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev0 = kex0 + klen * 0U;
  Lib_IntVector_Intrinsics_vec128 *next0 = kex0 + klen * 1U;
  Lib_IntVector_Intrinsics_vec128
  v0 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev0[0U], 0x01U);
  next0[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v0, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key = prev0[0U];
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
  next0[0U] = Lib_IntVector_Intrinsics_vec128_xor(key3, next0[0U]);
  uint32_t klen0 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev1 = kex0 + klen0 * 1U;
  Lib_IntVector_Intrinsics_vec128 *next1 = kex0 + klen0 * 2U;
  Lib_IntVector_Intrinsics_vec128
  v4 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev1[0U], 0x02U);
  next1[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v4, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key0 = prev1[0U];
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
  next1[0U] = Lib_IntVector_Intrinsics_vec128_xor(key30, next1[0U]);
  uint32_t klen1 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev2 = kex0 + klen1 * 2U;
  Lib_IntVector_Intrinsics_vec128 *next2 = kex0 + klen1 * 3U;
  Lib_IntVector_Intrinsics_vec128
  v5 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev2[0U], 0x04U);
  next2[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v5, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key4 = prev2[0U];
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
  next2[0U] = Lib_IntVector_Intrinsics_vec128_xor(key31, next2[0U]);
  uint32_t klen2 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev3 = kex0 + klen2 * 3U;
  Lib_IntVector_Intrinsics_vec128 *next3 = kex0 + klen2 * 4U;
  Lib_IntVector_Intrinsics_vec128
  v6 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev3[0U], 0x08U);
  next3[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v6, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key5 = prev3[0U];
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
  next3[0U] = Lib_IntVector_Intrinsics_vec128_xor(key32, next3[0U]);
  uint32_t klen3 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev4 = kex0 + klen3 * 4U;
  Lib_IntVector_Intrinsics_vec128 *next4 = kex0 + klen3 * 5U;
  Lib_IntVector_Intrinsics_vec128
  v7 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev4[0U], 0x10U);
  next4[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v7, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key6 = prev4[0U];
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
  next4[0U] = Lib_IntVector_Intrinsics_vec128_xor(key33, next4[0U]);
  uint32_t klen4 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev5 = kex0 + klen4 * 5U;
  Lib_IntVector_Intrinsics_vec128 *next5 = kex0 + klen4 * 6U;
  Lib_IntVector_Intrinsics_vec128
  v8 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev5[0U], 0x20U);
  next5[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v8, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key7 = prev5[0U];
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
  next5[0U] = Lib_IntVector_Intrinsics_vec128_xor(key34, next5[0U]);
  uint32_t klen5 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev6 = kex0 + klen5 * 6U;
  Lib_IntVector_Intrinsics_vec128 *next6 = kex0 + klen5 * 7U;
  Lib_IntVector_Intrinsics_vec128
  v9 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev6[0U], 0x40U);
  next6[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v9, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key8 = prev6[0U];
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
  next6[0U] = Lib_IntVector_Intrinsics_vec128_xor(key35, next6[0U]);
  uint32_t klen6 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev7 = kex0 + klen6 * 7U;
  Lib_IntVector_Intrinsics_vec128 *next7 = kex0 + klen6 * 8U;
  Lib_IntVector_Intrinsics_vec128
  v10 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev7[0U], 0x80U);
  next7[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v10, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key9 = prev7[0U];
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
  next7[0U] = Lib_IntVector_Intrinsics_vec128_xor(key36, next7[0U]);
  uint32_t klen7 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev8 = kex0 + klen7 * 8U;
  Lib_IntVector_Intrinsics_vec128 *next8 = kex0 + klen7 * 9U;
  Lib_IntVector_Intrinsics_vec128
  v12 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev8[0U], 0x1bU);
  next8[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v12, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key17 = prev8[0U];
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
  next8[0U] = Lib_IntVector_Intrinsics_vec128_xor(key37, next8[0U]);
  uint32_t klen8 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev = kex0 + klen8 * 9U;
  Lib_IntVector_Intrinsics_vec128 *next = kex0 + klen8 * 10U;
  Lib_IntVector_Intrinsics_vec128
  v = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev[0U], 0x36U);
  next[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key19 = prev[0U];
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
  next[0U] = Lib_IntVector_Intrinsics_vec128_xor(key38, next[0U]);
  uint32_t rem = len % 64U;
  uint32_t nb = len / 64U;
  uint32_t rem1 = len % 64U;
  for (uint32_t i = 0U; i < nb; i++)
  {
    uint8_t *uu____1 = out + i * 64U;
    uint8_t *uu____2 = inp + i * 64U;
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
    uint32_t klen9 = 1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen9;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + 10U * klen9;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    KRML_MAYBE_FOR9(i0,
      0U,
      9U,
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
    Lib_IntVector_Intrinsics_vec128 v00 = Lib_IntVector_Intrinsics_vec128_load128_le(uu____2);
    Lib_IntVector_Intrinsics_vec128 v1 = Lib_IntVector_Intrinsics_vec128_load128_le(uu____2 + 16U);
    Lib_IntVector_Intrinsics_vec128 v2 = Lib_IntVector_Intrinsics_vec128_load128_le(uu____2 + 32U);
    Lib_IntVector_Intrinsics_vec128 v3 = Lib_IntVector_Intrinsics_vec128_load128_le(uu____2 + 48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v00, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(uu____1, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(uu____1 + 16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(uu____1 + 32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(uu____1 + 48U, v31);
  }
  if (rem1 > 0U)
  {
    uint8_t *uu____3 = out + nb * 64U;
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
    uint32_t klen9 = 1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen9;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + 10U * klen9;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    KRML_MAYBE_FOR9(i,
      0U,
      9U,
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
    memcpy(uu____3, last, rem * sizeof (uint8_t));
  }
}

inline void
Hacl_AES_128_CTR32_NI_aes128_ctr_decrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint8_t *k,
  uint8_t *n,
  uint32_t c
)
{
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 ctx[12U] KRML_POST_ALIGN(16) = { 0U };
  Lib_IntVector_Intrinsics_vec128 *kex0 = ctx + 1U;
  Lib_IntVector_Intrinsics_vec128 *n10 = ctx;
  uint8_t nb0[16U] = { 0U };
  memcpy(nb0, n, 12U * sizeof (uint8_t));
  n10[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb0);
  Lib_IntVector_Intrinsics_vec128 *uu____0 = kex0;
  uu____0[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(k);
  uint32_t klen = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev0 = kex0 + klen * 0U;
  Lib_IntVector_Intrinsics_vec128 *next0 = kex0 + klen * 1U;
  Lib_IntVector_Intrinsics_vec128
  v0 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev0[0U], 0x01U);
  next0[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v0, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key = prev0[0U];
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
  next0[0U] = Lib_IntVector_Intrinsics_vec128_xor(key3, next0[0U]);
  uint32_t klen0 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev1 = kex0 + klen0 * 1U;
  Lib_IntVector_Intrinsics_vec128 *next1 = kex0 + klen0 * 2U;
  Lib_IntVector_Intrinsics_vec128
  v4 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev1[0U], 0x02U);
  next1[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v4, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key0 = prev1[0U];
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
  next1[0U] = Lib_IntVector_Intrinsics_vec128_xor(key30, next1[0U]);
  uint32_t klen1 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev2 = kex0 + klen1 * 2U;
  Lib_IntVector_Intrinsics_vec128 *next2 = kex0 + klen1 * 3U;
  Lib_IntVector_Intrinsics_vec128
  v5 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev2[0U], 0x04U);
  next2[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v5, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key4 = prev2[0U];
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
  next2[0U] = Lib_IntVector_Intrinsics_vec128_xor(key31, next2[0U]);
  uint32_t klen2 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev3 = kex0 + klen2 * 3U;
  Lib_IntVector_Intrinsics_vec128 *next3 = kex0 + klen2 * 4U;
  Lib_IntVector_Intrinsics_vec128
  v6 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev3[0U], 0x08U);
  next3[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v6, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key5 = prev3[0U];
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
  next3[0U] = Lib_IntVector_Intrinsics_vec128_xor(key32, next3[0U]);
  uint32_t klen3 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev4 = kex0 + klen3 * 4U;
  Lib_IntVector_Intrinsics_vec128 *next4 = kex0 + klen3 * 5U;
  Lib_IntVector_Intrinsics_vec128
  v7 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev4[0U], 0x10U);
  next4[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v7, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key6 = prev4[0U];
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
  next4[0U] = Lib_IntVector_Intrinsics_vec128_xor(key33, next4[0U]);
  uint32_t klen4 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev5 = kex0 + klen4 * 5U;
  Lib_IntVector_Intrinsics_vec128 *next5 = kex0 + klen4 * 6U;
  Lib_IntVector_Intrinsics_vec128
  v8 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev5[0U], 0x20U);
  next5[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v8, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key7 = prev5[0U];
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
  next5[0U] = Lib_IntVector_Intrinsics_vec128_xor(key34, next5[0U]);
  uint32_t klen5 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev6 = kex0 + klen5 * 6U;
  Lib_IntVector_Intrinsics_vec128 *next6 = kex0 + klen5 * 7U;
  Lib_IntVector_Intrinsics_vec128
  v9 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev6[0U], 0x40U);
  next6[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v9, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key8 = prev6[0U];
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
  next6[0U] = Lib_IntVector_Intrinsics_vec128_xor(key35, next6[0U]);
  uint32_t klen6 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev7 = kex0 + klen6 * 7U;
  Lib_IntVector_Intrinsics_vec128 *next7 = kex0 + klen6 * 8U;
  Lib_IntVector_Intrinsics_vec128
  v10 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev7[0U], 0x80U);
  next7[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v10, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key9 = prev7[0U];
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
  next7[0U] = Lib_IntVector_Intrinsics_vec128_xor(key36, next7[0U]);
  uint32_t klen7 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev8 = kex0 + klen7 * 8U;
  Lib_IntVector_Intrinsics_vec128 *next8 = kex0 + klen7 * 9U;
  Lib_IntVector_Intrinsics_vec128
  v12 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev8[0U], 0x1bU);
  next8[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v12, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key17 = prev8[0U];
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
  next8[0U] = Lib_IntVector_Intrinsics_vec128_xor(key37, next8[0U]);
  uint32_t klen8 = 1U;
  Lib_IntVector_Intrinsics_vec128 *prev = kex0 + klen8 * 9U;
  Lib_IntVector_Intrinsics_vec128 *next = kex0 + klen8 * 10U;
  Lib_IntVector_Intrinsics_vec128
  v = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev[0U], 0x36U);
  next[0U] = Lib_IntVector_Intrinsics_vec128_shuffle32(v, 3U, 3U, 3U, 3U);
  Lib_IntVector_Intrinsics_vec128 key19 = prev[0U];
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
  next[0U] = Lib_IntVector_Intrinsics_vec128_xor(key38, next[0U]);
  uint32_t rem = len % 64U;
  uint32_t nb = len / 64U;
  uint32_t rem1 = len % 64U;
  for (uint32_t i = 0U; i < nb; i++)
  {
    uint8_t *uu____1 = out + i * 64U;
    uint8_t *uu____2 = inp + i * 64U;
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
    uint32_t klen9 = 1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen9;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + 10U * klen9;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    KRML_MAYBE_FOR9(i0,
      0U,
      9U,
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
    Lib_IntVector_Intrinsics_vec128 v00 = Lib_IntVector_Intrinsics_vec128_load128_le(uu____2);
    Lib_IntVector_Intrinsics_vec128 v1 = Lib_IntVector_Intrinsics_vec128_load128_le(uu____2 + 16U);
    Lib_IntVector_Intrinsics_vec128 v2 = Lib_IntVector_Intrinsics_vec128_load128_le(uu____2 + 32U);
    Lib_IntVector_Intrinsics_vec128 v3 = Lib_IntVector_Intrinsics_vec128_load128_le(uu____2 + 48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v00, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(uu____1, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(uu____1 + 16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(uu____1 + 32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(uu____1 + 48U, v31);
  }
  if (rem1 > 0U)
  {
    uint8_t *uu____3 = out + nb * 64U;
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
    uint32_t klen9 = 1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen9;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + 10U * klen9;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    KRML_MAYBE_FOR9(i,
      0U,
      9U,
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
    memcpy(uu____3, last, rem * sizeof (uint8_t));
  }
}

