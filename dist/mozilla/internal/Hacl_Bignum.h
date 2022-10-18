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


#ifndef __internal_Hacl_Bignum_H
#define __internal_Hacl_Bignum_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include <stdbool.h>


#include "Hacl_Krmllib.h"
#include "lib_intrinsics.h"
void Hacl_Bignum_Convert_bn_from_bytes_be_uint64(uint32_t len, uint8_t *b, uint64_t *res);

void Hacl_Bignum_Convert_bn_to_bytes_be_uint64(uint32_t len, uint64_t *b, uint8_t *res);

uint64_t Hacl_Bignum_ModInvLimb_mod_inv_uint64(uint64_t n0);

void
Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64(
  uint32_t len,
  uint32_t nBits,
  uint64_t *n,
  uint64_t *res
);

void
Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t mu,
  uint64_t *r2,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
);

void
Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t mu,
  uint64_t *r2,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
);

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_Bignum_H_DEFINED
#endif
