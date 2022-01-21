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


#ifndef __Hacl_NaCl_H
#define __Hacl_NaCl_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_Salsa20.h"
#include "Hacl_Poly1305_32.h"
#include "Hacl_Curve25519_51.h"

uint32_t
Hacl_NaCl_crypto_secretbox_detached(
  uint8_t *c,
  uint8_t *tag,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *k
);

uint32_t
Hacl_NaCl_crypto_secretbox_open_detached(
  uint8_t *m,
  uint8_t *c,
  uint8_t *tag,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *k
);

uint32_t
Hacl_NaCl_crypto_secretbox_easy(uint8_t *c, uint8_t *m, uint32_t mlen, uint8_t *n, uint8_t *k);

uint32_t
Hacl_NaCl_crypto_secretbox_open_easy(
  uint8_t *m,
  uint8_t *c,
  uint32_t clen,
  uint8_t *n,
  uint8_t *k
);

uint32_t Hacl_NaCl_crypto_box_beforenm(uint8_t *k, uint8_t *pk, uint8_t *sk);

uint32_t
Hacl_NaCl_crypto_box_detached_afternm(
  uint8_t *c,
  uint8_t *tag,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *k
);

uint32_t
Hacl_NaCl_crypto_box_detached(
  uint8_t *c,
  uint8_t *tag,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
);

uint32_t
Hacl_NaCl_crypto_box_open_detached_afternm(
  uint8_t *m,
  uint8_t *c,
  uint8_t *tag,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *k
);

uint32_t
Hacl_NaCl_crypto_box_open_detached(
  uint8_t *m,
  uint8_t *c,
  uint8_t *tag,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
);

uint32_t
Hacl_NaCl_crypto_box_easy_afternm(
  uint8_t *c,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *k
);

uint32_t
Hacl_NaCl_crypto_box_easy(
  uint8_t *c,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
);

uint32_t
Hacl_NaCl_crypto_box_open_easy_afternm(
  uint8_t *m,
  uint8_t *c,
  uint32_t clen,
  uint8_t *n,
  uint8_t *k
);

uint32_t
Hacl_NaCl_crypto_box_open_easy(
  uint8_t *m,
  uint8_t *c,
  uint32_t clen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
);

#if defined(__cplusplus)
}
#endif

#define __Hacl_NaCl_H_DEFINED
#endif
