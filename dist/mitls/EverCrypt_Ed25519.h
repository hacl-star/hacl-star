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


#ifndef __EverCrypt_Ed25519_H
#define __EverCrypt_Ed25519_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_Ed25519.h"

void EverCrypt_Ed25519_sign(uint8_t *signature, uint8_t *secret, uint32_t len, uint8_t *msg);

bool EverCrypt_Ed25519_verify(uint8_t *pubkey, uint32_t len, uint8_t *msg, uint8_t *signature);

void EverCrypt_Ed25519_secret_to_public(uint8_t *output, uint8_t *secret);

void EverCrypt_Ed25519_expand_keys(uint8_t *ks, uint8_t *secret);

void
EverCrypt_Ed25519_sign_expanded(uint8_t *signature, uint8_t *ks, uint32_t len, uint8_t *msg);

#if defined(__cplusplus)
}
#endif

#define __EverCrypt_Ed25519_H_DEFINED
#endif
