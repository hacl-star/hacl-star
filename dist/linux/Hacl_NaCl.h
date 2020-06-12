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

#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"

#ifndef __Hacl_NaCl_H
#define __Hacl_NaCl_H

#include "Hacl_Kremlib.h"
#include "Hacl_Salsa20.h"
#include "Hacl_Poly1305_32.h"
#include "Hacl_Curve25519_51.h"


u32 Hacl_NaCl_crypto_secretbox_detached(u8 *c, u8 *tag, u8 *m, u32 mlen, u8 *n1, u8 *k);

u32 Hacl_NaCl_crypto_secretbox_open_detached(u8 *m, u8 *c, u8 *tag, u32 mlen, u8 *n1, u8 *k);

u32 Hacl_NaCl_crypto_secretbox_easy(u8 *c, u8 *m, u32 mlen, u8 *n1, u8 *k);

u32 Hacl_NaCl_crypto_secretbox_open_easy(u8 *m, u8 *c, u32 clen, u8 *n1, u8 *k);

u32 Hacl_NaCl_crypto_box_beforenm(u8 *k, u8 *pk, u8 *sk);

u32 Hacl_NaCl_crypto_box_detached_afternm(u8 *c, u8 *tag, u8 *m, u32 mlen, u8 *n1, u8 *k);

u32 Hacl_NaCl_crypto_box_detached(u8 *c, u8 *tag, u8 *m, u32 mlen, u8 *n1, u8 *pk, u8 *sk);

u32 Hacl_NaCl_crypto_box_open_detached_afternm(u8 *m, u8 *c, u8 *tag, u32 mlen, u8 *n1, u8 *k);

u32
Hacl_NaCl_crypto_box_open_detached(u8 *m, u8 *c, u8 *tag, u32 mlen, u8 *n1, u8 *pk, u8 *sk);

u32 Hacl_NaCl_crypto_box_easy_afternm(u8 *c, u8 *m, u32 mlen, u8 *n1, u8 *k);

u32 Hacl_NaCl_crypto_box_easy(u8 *c, u8 *m, u32 mlen, u8 *n1, u8 *pk, u8 *sk);

u32 Hacl_NaCl_crypto_box_open_easy_afternm(u8 *m, u8 *c, u32 clen, u8 *n1, u8 *k);

u32 Hacl_NaCl_crypto_box_open_easy(u8 *m, u8 *c, u32 clen, u8 *n1, u8 *pk, u8 *sk);

#define __Hacl_NaCl_H_DEFINED
#endif
