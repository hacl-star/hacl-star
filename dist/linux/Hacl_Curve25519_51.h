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

#ifndef __Hacl_Curve25519_51_H
#define __Hacl_Curve25519_51_H

#include "Hacl_Kremlib.h"


void Hacl_Impl_Curve25519_Field51_fadd(u64 *out, u64 *f1, u64 *f2);

void Hacl_Impl_Curve25519_Field51_fsub(u64 *out, u64 *f1, u64 *f2);

void Hacl_Impl_Curve25519_Field51_fmul(u64 *out, u64 *f1, u64 *f2, uint128_t *uu____2959);

void Hacl_Impl_Curve25519_Field51_fmul1(u64 *out, u64 *f1, u64 f2);

void Hacl_Impl_Curve25519_Field51_fsqr(u64 *out, u64 *f, uint128_t *uu____6941);

void Hacl_Curve25519_51_fsquare_times(u64 *o, u64 *inp, uint128_t *tmp, u32 n1);

void Hacl_Curve25519_51_finv(u64 *o, u64 *i, uint128_t *tmp);

void Hacl_Curve25519_51_scalarmult(u8 *out, u8 *priv, u8 *pub);

void Hacl_Curve25519_51_secret_to_public(u8 *pub, u8 *priv);

bool Hacl_Curve25519_51_ecdh(u8 *out, u8 *priv, u8 *pub);

#define __Hacl_Curve25519_51_H_DEFINED
#endif
