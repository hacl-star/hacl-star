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


#ifndef __EverCrypt_Hacl_H
#define __EverCrypt_Hacl_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"




#define EverCrypt_Hacl_aes128_mk_sbox Crypto_Symmetric_AES128_mk_sbox

extern void EverCrypt_Hacl_aes128_mk_sbox(uint8_t *sb);

#define EverCrypt_Hacl_aes128_keyExpansion Crypto_Symmetric_AES128_keyExpansion

extern void EverCrypt_Hacl_aes128_keyExpansion(uint8_t *key, uint8_t *w, uint8_t *sb);

#define EverCrypt_Hacl_aes128_cipher Crypto_Symmetric_AES128_cipher

extern void
EverCrypt_Hacl_aes128_cipher(uint8_t *cipher, uint8_t *plain, uint8_t *w, uint8_t *sb);

#define EverCrypt_Hacl_aes256_mk_sbox Crypto_Symmetric_AES_mk_sbox

extern void EverCrypt_Hacl_aes256_mk_sbox(uint8_t *sb);

#define EverCrypt_Hacl_aes256_keyExpansion Crypto_Symmetric_AES_keyExpansion

extern void EverCrypt_Hacl_aes256_keyExpansion(uint8_t *key, uint8_t *w, uint8_t *sb);

#define EverCrypt_Hacl_aes256_cipher Crypto_Symmetric_AES_cipher

extern void
EverCrypt_Hacl_aes256_cipher(uint8_t *cipher, uint8_t *plain, uint8_t *w, uint8_t *sb);

#if defined(__cplusplus)
}
#endif

#define __EverCrypt_Hacl_H_DEFINED
#endif
