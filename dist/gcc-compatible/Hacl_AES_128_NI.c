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


#include "Hacl_AES_128_NI.h"

void
Hacl_AES_128_NI_aes128_init(Lib_IntVector_Intrinsics_vec128 *ctx, uint8_t *key, uint8_t *nonce)
{
  Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *n = ctx;
  uint32_t klen = (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *uu____0 = kex;
  uu____0[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(key);
  Lib_IntVector_Intrinsics_vec128 *prev = kex;
  Lib_IntVector_Intrinsics_vec128 *next = kex + klen;
  Lib_IntVector_Intrinsics_vec128
  v0 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev[0U], (uint8_t)0x01U);
  next[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v0,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key1 = prev[0U];
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
  next[0U] = Lib_IntVector_Intrinsics_vec128_xor(next[0U], key4);
  Lib_IntVector_Intrinsics_vec128 *prev1 = kex + klen;
  Lib_IntVector_Intrinsics_vec128 *next1 = kex + (uint32_t)2U * klen;
  Lib_IntVector_Intrinsics_vec128
  v1 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev1[0U], (uint8_t)0x02U);
  next1[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v1,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
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
  next1[0U] = Lib_IntVector_Intrinsics_vec128_xor(next1[0U], key40);
  Lib_IntVector_Intrinsics_vec128 *prev2 = kex + klen * (uint32_t)2U;
  Lib_IntVector_Intrinsics_vec128 *next2 = kex + klen * (uint32_t)3U;
  Lib_IntVector_Intrinsics_vec128
  v2 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev2[0U], (uint8_t)0x04U);
  next2[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v2,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key11 = prev2[0U];
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
  next2[0U] = Lib_IntVector_Intrinsics_vec128_xor(next2[0U], key41);
  Lib_IntVector_Intrinsics_vec128 *prev3 = kex + klen * (uint32_t)3U;
  Lib_IntVector_Intrinsics_vec128 *next3 = kex + klen * (uint32_t)4U;
  Lib_IntVector_Intrinsics_vec128
  v3 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev3[0U], (uint8_t)0x08U);
  next3[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v3,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key12 = prev3[0U];
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
  next3[0U] = Lib_IntVector_Intrinsics_vec128_xor(next3[0U], key42);
  Lib_IntVector_Intrinsics_vec128 *prev4 = kex + klen * (uint32_t)4U;
  Lib_IntVector_Intrinsics_vec128 *next4 = kex + klen * (uint32_t)5U;
  Lib_IntVector_Intrinsics_vec128
  v4 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev4[0U], (uint8_t)0x10U);
  next4[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v4,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key13 = prev4[0U];
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
  next4[0U] = Lib_IntVector_Intrinsics_vec128_xor(next4[0U], key43);
  Lib_IntVector_Intrinsics_vec128 *prev5 = kex + klen * (uint32_t)5U;
  Lib_IntVector_Intrinsics_vec128 *next5 = kex + klen * (uint32_t)6U;
  Lib_IntVector_Intrinsics_vec128
  v5 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev5[0U], (uint8_t)0x20U);
  next5[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v5,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key14 = prev5[0U];
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
  next5[0U] = Lib_IntVector_Intrinsics_vec128_xor(next5[0U], key44);
  Lib_IntVector_Intrinsics_vec128 *prev6 = kex + klen * (uint32_t)6U;
  Lib_IntVector_Intrinsics_vec128 *next6 = kex + klen * (uint32_t)7U;
  Lib_IntVector_Intrinsics_vec128
  v6 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev6[0U], (uint8_t)0x40U);
  next6[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v6,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key15 = prev6[0U];
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
  next6[0U] = Lib_IntVector_Intrinsics_vec128_xor(next6[0U], key45);
  Lib_IntVector_Intrinsics_vec128 *prev7 = kex + klen * (uint32_t)7U;
  Lib_IntVector_Intrinsics_vec128 *next7 = kex + klen * (uint32_t)8U;
  Lib_IntVector_Intrinsics_vec128
  v7 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev7[0U], (uint8_t)0x80U);
  next7[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v7,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key16 = prev7[0U];
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
  next7[0U] = Lib_IntVector_Intrinsics_vec128_xor(next7[0U], key46);
  Lib_IntVector_Intrinsics_vec128 *prev8 = kex + klen * (uint32_t)8U;
  Lib_IntVector_Intrinsics_vec128 *next8 = kex + klen * (uint32_t)9U;
  Lib_IntVector_Intrinsics_vec128
  v8 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev8[0U], (uint8_t)0x1bU);
  next8[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v8,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key17 = prev8[0U];
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
  next8[0U] = Lib_IntVector_Intrinsics_vec128_xor(next8[0U], key47);
  Lib_IntVector_Intrinsics_vec128 *prev9 = kex + klen * (uint32_t)9U;
  Lib_IntVector_Intrinsics_vec128 *next9 = kex + klen * (uint32_t)10U;
  Lib_IntVector_Intrinsics_vec128
  v = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev9[0U], (uint8_t)0x36U);
  next9[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key18 = prev9[0U];
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
  next9[0U] = Lib_IntVector_Intrinsics_vec128_xor(next9[0U], key48);
  uint8_t nb[16U] = { 0U };
  memcpy(nb, nonce, (uint32_t)12U * sizeof (uint8_t));
  n[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb);
}

void Hacl_AES_128_NI_aes128_set_nonce(Lib_IntVector_Intrinsics_vec128 *ctx, uint8_t *nonce)
{
  Lib_IntVector_Intrinsics_vec128 *n = ctx;
  uint8_t nb[16U] = { 0U };
  memcpy(nb, nonce, (uint32_t)12U * sizeof (uint8_t));
  n[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb);
}

void
Hacl_AES_128_NI_aes128_key_block(
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
  Lib_IntVector_Intrinsics_vec128_store128_le(kb, st[0U]);
}

inline void
Hacl_AES_128_NI_aes128_ctr_encrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint8_t *k,
  uint8_t *n,
  uint32_t c
)
{
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 ctx[12U] KRML_POST_ALIGN(16) = { 0U };
  Lib_IntVector_Intrinsics_vec128 *kex0 = ctx + (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *n10 = ctx;
  uint32_t klen = (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *uu____0 = kex0;
  uu____0[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(k);
  Lib_IntVector_Intrinsics_vec128 *prev = kex0;
  Lib_IntVector_Intrinsics_vec128 *next = kex0 + klen;
  Lib_IntVector_Intrinsics_vec128
  v0 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev[0U], (uint8_t)0x01U);
  next[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v0,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key = prev[0U];
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
  next[0U] = Lib_IntVector_Intrinsics_vec128_xor(next[0U], key3);
  Lib_IntVector_Intrinsics_vec128 *prev1 = kex0 + klen;
  Lib_IntVector_Intrinsics_vec128 *next1 = kex0 + (uint32_t)2U * klen;
  Lib_IntVector_Intrinsics_vec128
  v4 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev1[0U], (uint8_t)0x02U);
  next1[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v4,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
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
  next1[0U] = Lib_IntVector_Intrinsics_vec128_xor(next1[0U], key30);
  Lib_IntVector_Intrinsics_vec128 *prev2 = kex0 + klen * (uint32_t)2U;
  Lib_IntVector_Intrinsics_vec128 *next2 = kex0 + klen * (uint32_t)3U;
  Lib_IntVector_Intrinsics_vec128
  v5 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev2[0U], (uint8_t)0x04U);
  next2[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v5,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key4 = prev2[0U];
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
  next2[0U] = Lib_IntVector_Intrinsics_vec128_xor(next2[0U], key31);
  Lib_IntVector_Intrinsics_vec128 *prev3 = kex0 + klen * (uint32_t)3U;
  Lib_IntVector_Intrinsics_vec128 *next3 = kex0 + klen * (uint32_t)4U;
  Lib_IntVector_Intrinsics_vec128
  v6 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev3[0U], (uint8_t)0x08U);
  next3[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v6,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key5 = prev3[0U];
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
  next3[0U] = Lib_IntVector_Intrinsics_vec128_xor(next3[0U], key32);
  Lib_IntVector_Intrinsics_vec128 *prev4 = kex0 + klen * (uint32_t)4U;
  Lib_IntVector_Intrinsics_vec128 *next4 = kex0 + klen * (uint32_t)5U;
  Lib_IntVector_Intrinsics_vec128
  v7 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev4[0U], (uint8_t)0x10U);
  next4[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v7,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key6 = prev4[0U];
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
  next4[0U] = Lib_IntVector_Intrinsics_vec128_xor(next4[0U], key33);
  Lib_IntVector_Intrinsics_vec128 *prev5 = kex0 + klen * (uint32_t)5U;
  Lib_IntVector_Intrinsics_vec128 *next5 = kex0 + klen * (uint32_t)6U;
  Lib_IntVector_Intrinsics_vec128
  v8 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev5[0U], (uint8_t)0x20U);
  next5[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v8,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key7 = prev5[0U];
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
  next5[0U] = Lib_IntVector_Intrinsics_vec128_xor(next5[0U], key34);
  Lib_IntVector_Intrinsics_vec128 *prev6 = kex0 + klen * (uint32_t)6U;
  Lib_IntVector_Intrinsics_vec128 *next6 = kex0 + klen * (uint32_t)7U;
  Lib_IntVector_Intrinsics_vec128
  v9 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev6[0U], (uint8_t)0x40U);
  next6[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v9,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key8 = prev6[0U];
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
  next6[0U] = Lib_IntVector_Intrinsics_vec128_xor(next6[0U], key35);
  Lib_IntVector_Intrinsics_vec128 *prev7 = kex0 + klen * (uint32_t)7U;
  Lib_IntVector_Intrinsics_vec128 *next7 = kex0 + klen * (uint32_t)8U;
  Lib_IntVector_Intrinsics_vec128
  v10 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev7[0U], (uint8_t)0x80U);
  next7[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v10,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key9 = prev7[0U];
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
  next7[0U] = Lib_IntVector_Intrinsics_vec128_xor(next7[0U], key36);
  Lib_IntVector_Intrinsics_vec128 *prev8 = kex0 + klen * (uint32_t)8U;
  Lib_IntVector_Intrinsics_vec128 *next8 = kex0 + klen * (uint32_t)9U;
  Lib_IntVector_Intrinsics_vec128
  v12 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev8[0U], (uint8_t)0x1bU);
  next8[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v12,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key17 = prev8[0U];
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
  next8[0U] = Lib_IntVector_Intrinsics_vec128_xor(next8[0U], key37);
  Lib_IntVector_Intrinsics_vec128 *prev9 = kex0 + klen * (uint32_t)9U;
  Lib_IntVector_Intrinsics_vec128 *next9 = kex0 + klen * (uint32_t)10U;
  Lib_IntVector_Intrinsics_vec128
  v = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev9[0U], (uint8_t)0x36U);
  next9[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key19 = prev9[0U];
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
  next9[0U] = Lib_IntVector_Intrinsics_vec128_xor(next9[0U], key38);
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
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)10U * klen0;
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
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)10U * klen0;
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

inline void
Hacl_AES_128_NI_aes128_ctr_decrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint8_t *k,
  uint8_t *n,
  uint32_t c
)
{
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 ctx[12U] KRML_POST_ALIGN(16) = { 0U };
  Lib_IntVector_Intrinsics_vec128 *kex0 = ctx + (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *n10 = ctx;
  uint32_t klen = (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *uu____0 = kex0;
  uu____0[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(k);
  Lib_IntVector_Intrinsics_vec128 *prev = kex0;
  Lib_IntVector_Intrinsics_vec128 *next = kex0 + klen;
  Lib_IntVector_Intrinsics_vec128
  v0 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev[0U], (uint8_t)0x01U);
  next[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v0,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key = prev[0U];
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
  next[0U] = Lib_IntVector_Intrinsics_vec128_xor(next[0U], key3);
  Lib_IntVector_Intrinsics_vec128 *prev1 = kex0 + klen;
  Lib_IntVector_Intrinsics_vec128 *next1 = kex0 + (uint32_t)2U * klen;
  Lib_IntVector_Intrinsics_vec128
  v4 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev1[0U], (uint8_t)0x02U);
  next1[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v4,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
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
  next1[0U] = Lib_IntVector_Intrinsics_vec128_xor(next1[0U], key30);
  Lib_IntVector_Intrinsics_vec128 *prev2 = kex0 + klen * (uint32_t)2U;
  Lib_IntVector_Intrinsics_vec128 *next2 = kex0 + klen * (uint32_t)3U;
  Lib_IntVector_Intrinsics_vec128
  v5 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev2[0U], (uint8_t)0x04U);
  next2[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v5,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key4 = prev2[0U];
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
  next2[0U] = Lib_IntVector_Intrinsics_vec128_xor(next2[0U], key31);
  Lib_IntVector_Intrinsics_vec128 *prev3 = kex0 + klen * (uint32_t)3U;
  Lib_IntVector_Intrinsics_vec128 *next3 = kex0 + klen * (uint32_t)4U;
  Lib_IntVector_Intrinsics_vec128
  v6 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev3[0U], (uint8_t)0x08U);
  next3[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v6,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key5 = prev3[0U];
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
  next3[0U] = Lib_IntVector_Intrinsics_vec128_xor(next3[0U], key32);
  Lib_IntVector_Intrinsics_vec128 *prev4 = kex0 + klen * (uint32_t)4U;
  Lib_IntVector_Intrinsics_vec128 *next4 = kex0 + klen * (uint32_t)5U;
  Lib_IntVector_Intrinsics_vec128
  v7 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev4[0U], (uint8_t)0x10U);
  next4[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v7,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key6 = prev4[0U];
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
  next4[0U] = Lib_IntVector_Intrinsics_vec128_xor(next4[0U], key33);
  Lib_IntVector_Intrinsics_vec128 *prev5 = kex0 + klen * (uint32_t)5U;
  Lib_IntVector_Intrinsics_vec128 *next5 = kex0 + klen * (uint32_t)6U;
  Lib_IntVector_Intrinsics_vec128
  v8 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev5[0U], (uint8_t)0x20U);
  next5[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v8,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key7 = prev5[0U];
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
  next5[0U] = Lib_IntVector_Intrinsics_vec128_xor(next5[0U], key34);
  Lib_IntVector_Intrinsics_vec128 *prev6 = kex0 + klen * (uint32_t)6U;
  Lib_IntVector_Intrinsics_vec128 *next6 = kex0 + klen * (uint32_t)7U;
  Lib_IntVector_Intrinsics_vec128
  v9 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev6[0U], (uint8_t)0x40U);
  next6[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v9,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key8 = prev6[0U];
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
  next6[0U] = Lib_IntVector_Intrinsics_vec128_xor(next6[0U], key35);
  Lib_IntVector_Intrinsics_vec128 *prev7 = kex0 + klen * (uint32_t)7U;
  Lib_IntVector_Intrinsics_vec128 *next7 = kex0 + klen * (uint32_t)8U;
  Lib_IntVector_Intrinsics_vec128
  v10 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev7[0U], (uint8_t)0x80U);
  next7[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v10,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key9 = prev7[0U];
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
  next7[0U] = Lib_IntVector_Intrinsics_vec128_xor(next7[0U], key36);
  Lib_IntVector_Intrinsics_vec128 *prev8 = kex0 + klen * (uint32_t)8U;
  Lib_IntVector_Intrinsics_vec128 *next8 = kex0 + klen * (uint32_t)9U;
  Lib_IntVector_Intrinsics_vec128
  v12 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev8[0U], (uint8_t)0x1bU);
  next8[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v12,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key17 = prev8[0U];
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
  next8[0U] = Lib_IntVector_Intrinsics_vec128_xor(next8[0U], key37);
  Lib_IntVector_Intrinsics_vec128 *prev9 = kex0 + klen * (uint32_t)9U;
  Lib_IntVector_Intrinsics_vec128 *next9 = kex0 + klen * (uint32_t)10U;
  Lib_IntVector_Intrinsics_vec128
  v = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev9[0U], (uint8_t)0x36U);
  next9[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key19 = prev9[0U];
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
  next9[0U] = Lib_IntVector_Intrinsics_vec128_xor(next9[0U], key38);
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
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)10U * klen0;
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
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)10U * klen0;
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

