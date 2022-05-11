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

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "internal/Hacl_Spec.h"
#include "../Hacl_P256.h"
#include "lib_intrinsics.h"
#include "libintvector.h"
void Hacl_Impl_P256_LowLevel_toUint8(u64 *i, u8 *o);

void Hacl_Impl_P256_LowLevel_changeEndian(u64 *i);

void Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(u8 *i, u64 *o);

u64 Hacl_Impl_P256_Core_isPointAtInfinityPrivate(u64 *p);

void Hacl_Impl_P256_Core_secretToPublic(u64 *result, u8 *scalar, u64 *tempBuffer);

/*
  The pub(lic)_key input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over this variable.
*/
u64 Hacl_Impl_P256_DH__ecp256dh_r(u64 *result, u64 *pubKey, u8 *scalar);

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_P256_H_DEFINED
#endif
