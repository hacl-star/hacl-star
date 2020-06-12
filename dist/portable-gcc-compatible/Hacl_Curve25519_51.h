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
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"

#ifndef __Hacl_Curve25519_51_H
#define __Hacl_Curve25519_51_H

#include "Hacl_Kremlib.h"


/* SNIPPET_START: Hacl_Impl_Curve25519_Field51_fadd */

void Hacl_Impl_Curve25519_Field51_fadd(uint64_t *out, uint64_t *f1, uint64_t *f2);

/* SNIPPET_END: Hacl_Impl_Curve25519_Field51_fadd */

/* SNIPPET_START: Hacl_Impl_Curve25519_Field51_fsub */

void Hacl_Impl_Curve25519_Field51_fsub(uint64_t *out, uint64_t *f1, uint64_t *f2);

/* SNIPPET_END: Hacl_Impl_Curve25519_Field51_fsub */

/* SNIPPET_START: Hacl_Impl_Curve25519_Field51_fmul */

void
Hacl_Impl_Curve25519_Field51_fmul(
  uint64_t *out,
  uint64_t *f1,
  uint64_t *f2,
  FStar_UInt128_uint128 *uu____3153
);

/* SNIPPET_END: Hacl_Impl_Curve25519_Field51_fmul */

/* SNIPPET_START: Hacl_Impl_Curve25519_Field51_fmul1 */

void Hacl_Impl_Curve25519_Field51_fmul1(uint64_t *out, uint64_t *f1, uint64_t f2);

/* SNIPPET_END: Hacl_Impl_Curve25519_Field51_fmul1 */

/* SNIPPET_START: Hacl_Impl_Curve25519_Field51_fsqr */

void
Hacl_Impl_Curve25519_Field51_fsqr(
  uint64_t *out,
  uint64_t *f,
  FStar_UInt128_uint128 *uu____7683
);

/* SNIPPET_END: Hacl_Impl_Curve25519_Field51_fsqr */

/* SNIPPET_START: Hacl_Curve25519_51_fsquare_times */

void
Hacl_Curve25519_51_fsquare_times(
  uint64_t *o,
  uint64_t *inp,
  FStar_UInt128_uint128 *tmp,
  uint32_t n
);

/* SNIPPET_END: Hacl_Curve25519_51_fsquare_times */

/* SNIPPET_START: Hacl_Curve25519_51_finv */

void Hacl_Curve25519_51_finv(uint64_t *o, uint64_t *i, FStar_UInt128_uint128 *tmp);

/* SNIPPET_END: Hacl_Curve25519_51_finv */

/* SNIPPET_START: Hacl_Curve25519_51_scalarmult */

void Hacl_Curve25519_51_scalarmult(uint8_t *out, uint8_t *priv, uint8_t *pub);

/* SNIPPET_END: Hacl_Curve25519_51_scalarmult */

/* SNIPPET_START: Hacl_Curve25519_51_secret_to_public */

void Hacl_Curve25519_51_secret_to_public(uint8_t *pub, uint8_t *priv);

/* SNIPPET_END: Hacl_Curve25519_51_secret_to_public */

/* SNIPPET_START: Hacl_Curve25519_51_ecdh */

bool Hacl_Curve25519_51_ecdh(uint8_t *out, uint8_t *priv, uint8_t *pub);

/* SNIPPET_END: Hacl_Curve25519_51_ecdh */

#define __Hacl_Curve25519_51_H_DEFINED
#endif
