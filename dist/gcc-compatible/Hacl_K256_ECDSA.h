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


#ifndef __Hacl_K256_ECDSA_H
#define __Hacl_K256_ECDSA_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "lib_intrinsics.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_Kremlib.h"
#include "Hacl_Hash_SHA2.h"
#include "Hacl_Bignum_Base.h"

bool
Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(
  uint8_t *r,
  uint8_t *s,
  uint8_t *m,
  uint8_t *private_key,
  uint8_t *k
);

bool
Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(
  uint8_t *m,
  uint8_t *public_key_x,
  uint8_t *public_key_y,
  uint8_t *r,
  uint8_t *s
);

bool
Hacl_K256_ECDSA_ecdsa_sign_sha256(
  uint8_t *r,
  uint8_t *s,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *k
);

bool
Hacl_K256_ECDSA_ecdsa_verify_sha256(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key_x,
  uint8_t *public_key_y,
  uint8_t *r,
  uint8_t *s
);

#if defined(__cplusplus)
}
#endif

#define __Hacl_K256_ECDSA_H_DEFINED
#endif
