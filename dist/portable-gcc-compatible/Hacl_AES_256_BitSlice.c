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


#include "Hacl_AES_256_BitSlice.h"

#include "internal/Hacl_AES_128_BitSlice.h"

/* SNIPPET_START: Hacl_AES_256_BitSlice_aes256_init */

void Hacl_AES_256_BitSlice_aes256_init(uint64_t *ctx, uint8_t *key, uint8_t *nonce)
{
  uint64_t *kex = ctx + (uint32_t)8U;
  uint64_t *n = ctx;
  uint32_t klen = (uint32_t)8U;
  uint64_t *next0 = kex;
  uint64_t *next1 = kex + klen;
  Hacl_Impl_AES_CoreBitSlice_load_key1(next0, key);
  Hacl_Impl_AES_CoreBitSlice_load_key1(next1, key + (uint32_t)16U);
  uint64_t *prev0 = next0;
  uint64_t *prev1 = next1;
  uint64_t *next01 = kex + klen * (uint32_t)2U;
  uint64_t *next11 = kex + klen * (uint32_t)3U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next01, prev1, (uint8_t)0x01U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next01[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next01[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next01, prev0);
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next11, next01, (uint8_t)0U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next11[i];
    uint64_t n2 = n1 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n3 = n2 ^ n2 << (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next11[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next11, prev1);
  uint64_t *prev01 = next01;
  uint64_t *prev11 = next11;
  uint64_t *next02 = kex + klen * (uint32_t)4U;
  uint64_t *next12 = kex + klen * (uint32_t)5U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next02, prev11, (uint8_t)0x02U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next02[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next02[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next02, prev01);
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next12, next02, (uint8_t)0U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next12[i];
    uint64_t n2 = n1 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n3 = n2 ^ n2 << (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next12[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next12, prev11);
  uint64_t *prev02 = next02;
  uint64_t *prev12 = next12;
  uint64_t *next03 = kex + klen * (uint32_t)6U;
  uint64_t *next13 = kex + klen * (uint32_t)7U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next03, prev12, (uint8_t)0x04U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next03[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next03[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next03, prev02);
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next13, next03, (uint8_t)0U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next13[i];
    uint64_t n2 = n1 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n3 = n2 ^ n2 << (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next13[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next13, prev12);
  uint64_t *prev03 = next03;
  uint64_t *prev13 = next13;
  uint64_t *next04 = kex + klen * (uint32_t)8U;
  uint64_t *next14 = kex + klen * (uint32_t)9U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next04, prev13, (uint8_t)0x08U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next04[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next04[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next04, prev03);
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next14, next04, (uint8_t)0U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next14[i];
    uint64_t n2 = n1 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n3 = n2 ^ n2 << (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next14[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next14, prev13);
  uint64_t *prev04 = next04;
  uint64_t *prev14 = next14;
  uint64_t *next05 = kex + klen * (uint32_t)10U;
  uint64_t *next15 = kex + klen * (uint32_t)11U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next05, prev14, (uint8_t)0x10U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next05[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next05[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next05, prev04);
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next15, next05, (uint8_t)0U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next15[i];
    uint64_t n2 = n1 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n3 = n2 ^ n2 << (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next15[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next15, prev14);
  uint64_t *prev05 = next05;
  uint64_t *prev15 = next15;
  uint64_t *next06 = kex + klen * (uint32_t)12U;
  uint64_t *next16 = kex + klen * (uint32_t)13U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next06, prev15, (uint8_t)0x20U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next06[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next06[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next06, prev05);
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next16, next06, (uint8_t)0U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next16[i];
    uint64_t n2 = n1 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n3 = n2 ^ n2 << (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next16[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next16, prev15);
  uint64_t *prev06 = next06;
  uint64_t *prev16 = next16;
  uint64_t *next07 = kex + klen * (uint32_t)14U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next07, prev16, (uint8_t)0x40U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next07[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next07[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next07, prev06);
  Hacl_Impl_AES_CoreBitSlice_load_nonce(n, nonce);
}

/* SNIPPET_END: Hacl_AES_256_BitSlice_aes256_init */

/* SNIPPET_START: Hacl_AES_256_BitSlice_aes256_set_nonce */

void Hacl_AES_256_BitSlice_aes256_set_nonce(uint64_t *ctx, uint8_t *nonce)
{
  uint64_t *n = ctx;
  Hacl_Impl_AES_CoreBitSlice_load_nonce(n, nonce);
}

/* SNIPPET_END: Hacl_AES_256_BitSlice_aes256_set_nonce */

/* SNIPPET_START: Hacl_AES_256_BitSlice_aes256_key_block */

void Hacl_AES_256_BitSlice_aes256_key_block(uint8_t *kb, uint64_t *ctx, uint32_t counter)
{
  uint64_t *kex = ctx + (uint32_t)8U;
  uint64_t *n = ctx;
  uint64_t st[8U] = { 0U };
  Hacl_Impl_AES_CoreBitSlice_load_state(st, n, counter);
  uint32_t klen = (uint32_t)8U;
  uint64_t *k0 = kex;
  uint64_t *kr = kex + klen;
  uint64_t *kn = kex + (uint32_t)14U * klen;
  Hacl_Impl_AES_CoreBitSlice_xor_state_key1(st, k0);
  KRML_MAYBE_FOR13(i,
    (uint32_t)0U,
    (uint32_t)13U,
    (uint32_t)1U,
    uint64_t *sub_key = kr + i * (uint32_t)8U;
    Hacl_Impl_AES_CoreBitSlice_aes_enc(st, sub_key););
  Hacl_Impl_AES_CoreBitSlice_aes_enc_last(st, kn);
  Hacl_Impl_AES_CoreBitSlice_store_block0(kb, st);
}

/* SNIPPET_END: Hacl_AES_256_BitSlice_aes256_key_block */

/* SNIPPET_START: Hacl_AES_256_BitSlice_aes256_ctr */

void
Hacl_AES_256_BitSlice_aes256_ctr(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint64_t *ctx,
  uint32_t c
)
{
  Hacl_Impl_AES_Generic_aes256_ctr_bitslice(len, out, inp, ctx, c);
}

/* SNIPPET_END: Hacl_AES_256_BitSlice_aes256_ctr */

/* SNIPPET_START: Hacl_AES_256_BitSlice_aes256_ctr_encrypt */

inline void
Hacl_AES_256_BitSlice_aes256_ctr_encrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint8_t *k,
  uint8_t *n,
  uint32_t c
)
{
  uint64_t ctx[128U] = { 0U };
  uint64_t *kex = ctx + (uint32_t)8U;
  uint64_t *n1 = ctx;
  uint32_t klen = (uint32_t)8U;
  uint64_t *next0 = kex;
  uint64_t *next1 = kex + klen;
  Hacl_Impl_AES_CoreBitSlice_load_key1(next0, k);
  Hacl_Impl_AES_CoreBitSlice_load_key1(next1, k + (uint32_t)16U);
  uint64_t *prev0 = next0;
  uint64_t *prev1 = next1;
  uint64_t *next01 = kex + klen * (uint32_t)2U;
  uint64_t *next11 = kex + klen * (uint32_t)3U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next01, prev1, (uint8_t)0x01U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next01[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next01[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next01, prev0);
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next11, next01, (uint8_t)0U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next11[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next11[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next11, prev1);
  uint64_t *prev01 = next01;
  uint64_t *prev11 = next11;
  uint64_t *next02 = kex + klen * (uint32_t)4U;
  uint64_t *next12 = kex + klen * (uint32_t)5U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next02, prev11, (uint8_t)0x02U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next02[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next02[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next02, prev01);
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next12, next02, (uint8_t)0U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next12[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next12[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next12, prev11);
  uint64_t *prev02 = next02;
  uint64_t *prev12 = next12;
  uint64_t *next03 = kex + klen * (uint32_t)6U;
  uint64_t *next13 = kex + klen * (uint32_t)7U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next03, prev12, (uint8_t)0x04U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next03[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next03[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next03, prev02);
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next13, next03, (uint8_t)0U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next13[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next13[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next13, prev12);
  uint64_t *prev03 = next03;
  uint64_t *prev13 = next13;
  uint64_t *next04 = kex + klen * (uint32_t)8U;
  uint64_t *next14 = kex + klen * (uint32_t)9U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next04, prev13, (uint8_t)0x08U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next04[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next04[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next04, prev03);
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next14, next04, (uint8_t)0U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next14[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next14[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next14, prev13);
  uint64_t *prev04 = next04;
  uint64_t *prev14 = next14;
  uint64_t *next05 = kex + klen * (uint32_t)10U;
  uint64_t *next15 = kex + klen * (uint32_t)11U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next05, prev14, (uint8_t)0x10U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next05[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next05[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next05, prev04);
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next15, next05, (uint8_t)0U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next15[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next15[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next15, prev14);
  uint64_t *prev05 = next05;
  uint64_t *prev15 = next15;
  uint64_t *next06 = kex + klen * (uint32_t)12U;
  uint64_t *next16 = kex + klen * (uint32_t)13U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next06, prev15, (uint8_t)0x20U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next06[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next06[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next06, prev05);
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next16, next06, (uint8_t)0U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next16[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next16[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next16, prev15);
  uint64_t *prev06 = next06;
  uint64_t *prev16 = next16;
  uint64_t *next07 = kex + klen * (uint32_t)14U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next07, prev16, (uint8_t)0x40U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next07[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next07[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next07, prev06);
  Hacl_Impl_AES_CoreBitSlice_load_nonce(n1, n);
  Hacl_Impl_AES_Generic_aes256_ctr_bitslice(len, out, inp, ctx, c);
}

/* SNIPPET_END: Hacl_AES_256_BitSlice_aes256_ctr_encrypt */

/* SNIPPET_START: Hacl_AES_256_BitSlice_aes256_ctr_decrypt */

inline void
Hacl_AES_256_BitSlice_aes256_ctr_decrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint8_t *k,
  uint8_t *n,
  uint32_t c
)
{
  uint64_t ctx[128U] = { 0U };
  uint64_t *kex = ctx + (uint32_t)8U;
  uint64_t *n1 = ctx;
  uint32_t klen = (uint32_t)8U;
  uint64_t *next0 = kex;
  uint64_t *next1 = kex + klen;
  Hacl_Impl_AES_CoreBitSlice_load_key1(next0, k);
  Hacl_Impl_AES_CoreBitSlice_load_key1(next1, k + (uint32_t)16U);
  uint64_t *prev0 = next0;
  uint64_t *prev1 = next1;
  uint64_t *next01 = kex + klen * (uint32_t)2U;
  uint64_t *next11 = kex + klen * (uint32_t)3U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next01, prev1, (uint8_t)0x01U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next01[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next01[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next01, prev0);
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next11, next01, (uint8_t)0U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next11[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next11[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next11, prev1);
  uint64_t *prev01 = next01;
  uint64_t *prev11 = next11;
  uint64_t *next02 = kex + klen * (uint32_t)4U;
  uint64_t *next12 = kex + klen * (uint32_t)5U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next02, prev11, (uint8_t)0x02U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next02[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next02[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next02, prev01);
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next12, next02, (uint8_t)0U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next12[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next12[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next12, prev11);
  uint64_t *prev02 = next02;
  uint64_t *prev12 = next12;
  uint64_t *next03 = kex + klen * (uint32_t)6U;
  uint64_t *next13 = kex + klen * (uint32_t)7U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next03, prev12, (uint8_t)0x04U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next03[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next03[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next03, prev02);
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next13, next03, (uint8_t)0U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next13[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next13[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next13, prev12);
  uint64_t *prev03 = next03;
  uint64_t *prev13 = next13;
  uint64_t *next04 = kex + klen * (uint32_t)8U;
  uint64_t *next14 = kex + klen * (uint32_t)9U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next04, prev13, (uint8_t)0x08U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next04[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next04[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next04, prev03);
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next14, next04, (uint8_t)0U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next14[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next14[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next14, prev13);
  uint64_t *prev04 = next04;
  uint64_t *prev14 = next14;
  uint64_t *next05 = kex + klen * (uint32_t)10U;
  uint64_t *next15 = kex + klen * (uint32_t)11U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next05, prev14, (uint8_t)0x10U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next05[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next05[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next05, prev04);
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next15, next05, (uint8_t)0U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next15[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next15[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next15, prev14);
  uint64_t *prev05 = next05;
  uint64_t *prev15 = next15;
  uint64_t *next06 = kex + klen * (uint32_t)12U;
  uint64_t *next16 = kex + klen * (uint32_t)13U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next06, prev15, (uint8_t)0x20U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next06[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next06[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next06, prev05);
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next16, next06, (uint8_t)0U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next16[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next16[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next16, prev15);
  uint64_t *prev06 = next06;
  uint64_t *prev16 = next16;
  uint64_t *next07 = kex + klen * (uint32_t)14U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next07, prev16, (uint8_t)0x40U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next07[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next07[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next07, prev06);
  Hacl_Impl_AES_CoreBitSlice_load_nonce(n1, n);
  Hacl_Impl_AES_Generic_aes256_ctr_bitslice(len, out, inp, ctx, c);
}

/* SNIPPET_END: Hacl_AES_256_BitSlice_aes256_ctr_decrypt */

