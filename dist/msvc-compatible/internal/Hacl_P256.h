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


#ifndef __internal_Hacl_P256_H
#define __internal_Hacl_P256_H

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


#include "internal/Hacl_Spec.h"
#include "internal/Hacl_Kremlib.h"
#include "../Hacl_P256.h"

void Hacl_Impl_P256_LowLevel_toUint8(uint64_t *i, uint8_t *o);

void Hacl_Impl_P256_LowLevel_changeEndian(uint64_t *i);

void Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(uint8_t *i, uint64_t *o);

uint64_t Hacl_Impl_P256_Core_isPointAtInfinityPrivate(uint64_t *p);

void
Hacl_Impl_P256_Core_secretToPublic(uint64_t *result, uint8_t *scalar, uint64_t *tempBuffer);

/*
  The pub(lic)_key input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over this variable.
*/
uint64_t Hacl_Impl_P256_DH__ecp256dh_r(uint64_t *result, uint64_t *pubKey, uint8_t *scalar);

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_P256_H_DEFINED
#endif
