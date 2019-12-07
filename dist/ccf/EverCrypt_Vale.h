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

#include "evercrypt_targetconfig.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"

#ifndef __EverCrypt_Vale_H
#define __EverCrypt_Vale_H




extern void aes128_key_expansion_sbox(uint8_t *key, uint8_t *w, uint8_t *sbox);

extern void
aes128_encrypt_one_block(uint8_t *cipher, uint8_t *plain, uint8_t *w, uint8_t *sbox);

typedef struct gcm_args_s
{
  uint8_t *plain;
  uint64_t plain_len;
  uint8_t *aad;
  uint64_t aad_len;
  uint8_t *iv;
  uint8_t *expanded_key;
  uint8_t *cipher;
  uint8_t *tag;
}
gcm_args;

uint8_t *__proj__Mkgcm_args__item__plain(gcm_args projectee);

uint64_t __proj__Mkgcm_args__item__plain_len(gcm_args projectee);

uint8_t *__proj__Mkgcm_args__item__aad(gcm_args projectee);

uint64_t __proj__Mkgcm_args__item__aad_len(gcm_args projectee);

uint8_t *__proj__Mkgcm_args__item__iv(gcm_args projectee);

uint8_t *__proj__Mkgcm_args__item__expanded_key(gcm_args projectee);

uint8_t *__proj__Mkgcm_args__item__cipher(gcm_args projectee);

uint8_t *__proj__Mkgcm_args__item__tag(gcm_args projectee);

extern void __stdcall old_aes128_key_expansion(uint8_t *key_ptr, uint8_t *expanded_key_ptr);

extern void __stdcall old_gcm128_encrypt(gcm_args *uu____343);

extern uint32_t __stdcall old_gcm128_decrypt(gcm_args *uu____357);

extern void __stdcall old_aes256_key_expansion(uint8_t *key_ptr, uint8_t *expanded_key_ptr);

extern void __stdcall old_gcm256_encrypt(gcm_args *uu____389);

extern uint32_t __stdcall old_gcm256_decrypt(gcm_args *uu____403);

#define __EverCrypt_Vale_H_DEFINED
#endif
