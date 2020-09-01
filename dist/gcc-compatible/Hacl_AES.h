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


#ifndef __Hacl_AES_H
#define __Hacl_AES_H
#include "kremlib.h"




typedef uint8_t *Crypto_Symmetric_AES_bytes;

typedef uint8_t *Crypto_Symmetric_AES_block;

typedef uint8_t *Crypto_Symmetric_AES_skey;

typedef uint8_t *Crypto_Symmetric_AES_xkey;

typedef uint32_t Crypto_Symmetric_AES_rnd;

typedef uint32_t Crypto_Symmetric_AES_idx_16;

typedef uint8_t *Crypto_Symmetric_AES_sbox;

void Crypto_Symmetric_AES_mk_sbox(uint8_t *sbox1);

void Crypto_Symmetric_AES_mk_inv_sbox(uint8_t *sbox1);

void Crypto_Symmetric_AES_cipher(uint8_t *out, uint8_t *input, uint8_t *w, uint8_t *sbox1);

void Crypto_Symmetric_AES_keyExpansion(uint8_t *key, uint8_t *w, uint8_t *sbox1);

void Crypto_Symmetric_AES_inv_cipher(uint8_t *out, uint8_t *input, uint8_t *w, uint8_t *sbox1);

typedef uint8_t *Crypto_Symmetric_AES128_bytes;

typedef uint8_t *Crypto_Symmetric_AES128_block;

typedef uint8_t *Crypto_Symmetric_AES128_skey;

typedef uint8_t *Crypto_Symmetric_AES128_xkey;

typedef uint32_t Crypto_Symmetric_AES128_rnd;

typedef uint32_t Crypto_Symmetric_AES128_idx_16;

typedef uint8_t *Crypto_Symmetric_AES128_sbox;

void Crypto_Symmetric_AES128_mk_sbox(uint8_t *sbox1);

void Crypto_Symmetric_AES128_mk_inv_sbox(uint8_t *sbox1);

void Crypto_Symmetric_AES128_cipher(uint8_t *out, uint8_t *input, uint8_t *w, uint8_t *sbox1);

void Crypto_Symmetric_AES128_keyExpansion(uint8_t *key, uint8_t *w, uint8_t *sbox1);

void
Crypto_Symmetric_AES128_inv_cipher(uint8_t *out, uint8_t *input, uint8_t *w, uint8_t *sbox1);


#define __Hacl_AES_H_DEFINED
#endif
