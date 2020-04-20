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
#include "lib_intrinsics.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"

#ifndef __Hacl_ECDSA_H
#define __Hacl_ECDSA_H

#include "Hacl_Kremlib.h"
#include "Hacl_Hash.h"


/* SNIPPET_START: Hacl_Impl_P256_DH_ecp256dh_i */

uint64_t Hacl_Impl_P256_DH_ecp256dh_i(uint8_t *result, uint8_t *scalar);

/* SNIPPET_END: Hacl_Impl_P256_DH_ecp256dh_i */

/* SNIPPET_START: Hacl_Impl_P256_DH_ecp256dh_r */

uint64_t Hacl_Impl_P256_DH_ecp256dh_r(uint8_t *result, uint8_t *pubKey, uint8_t *scalar);

/* SNIPPET_END: Hacl_Impl_P256_DH_ecp256dh_r */

/* SNIPPET_START: Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign */

uint64_t
Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
);

/* SNIPPET_END: Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign */

/* SNIPPET_START: Hacl_Impl_ECDSA_ecdsa_p256_sha2_verify */

bool
Hacl_Impl_ECDSA_ecdsa_p256_sha2_verify(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
);

/* SNIPPET_END: Hacl_Impl_ECDSA_ecdsa_p256_sha2_verify */

#define __Hacl_ECDSA_H_DEFINED
#endif
