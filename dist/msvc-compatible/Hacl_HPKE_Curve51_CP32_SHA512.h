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


#ifndef __Hacl_HPKE_Curve51_CP32_SHA512_H
#define __Hacl_HPKE_Curve51_CP32_SHA512_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_Hash_SHA2.h"
#include "Hacl_HKDF.h"
#include "Hacl_Curve25519_51.h"
#include "Hacl_Chacha20Poly1305_32.h"

uint32_t
Hacl_HPKE_Curve51_CP32_SHA512_setupBaseI(
  uint8_t *o_pkE,
  uint8_t *o_k,
  uint8_t *o_n,
  uint8_t *skE,
  uint8_t *pkR,
  uint32_t infolen,
  uint8_t *info
);

uint32_t
Hacl_HPKE_Curve51_CP32_SHA512_setupBaseR(
  uint8_t *o_key_aead,
  uint8_t *o_nonce_aead,
  uint8_t *pkE,
  uint8_t *skR,
  uint32_t infolen,
  uint8_t *info
);

uint32_t
Hacl_HPKE_Curve51_CP32_SHA512_sealBase(
  uint8_t *skE,
  uint8_t *pkR,
  uint32_t mlen,
  uint8_t *m,
  uint32_t infolen,
  uint8_t *info,
  uint8_t *output
);

uint32_t
Hacl_HPKE_Curve51_CP32_SHA512_openBase(
  uint8_t *pkE,
  uint8_t *skR,
  uint32_t mlen,
  uint8_t *m,
  uint32_t infolen,
  uint8_t *info,
  uint8_t *output
);

#if defined(__cplusplus)
}
#endif

#define __Hacl_HPKE_Curve51_CP32_SHA512_H_DEFINED
#endif
