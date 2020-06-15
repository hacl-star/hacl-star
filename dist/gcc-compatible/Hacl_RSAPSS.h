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

#ifndef __Hacl_RSAPSS_H
#define __Hacl_RSAPSS_H

#include "Hacl_Kremlib.h"
#include "Hacl_Hash.h"


uint64_t
Hacl_Bignum_Multiplication_mul_carry_add_u64_st(
  uint64_t c_in,
  uint64_t a,
  uint64_t b,
  uint64_t *out
);

bool Hacl_Bignum_bn_is_bit_set(uint32_t len, uint64_t *input, uint32_t ind);

uint64_t Hacl_Bignum_Montgomery_mod_inv_u64(uint64_t n0);

void
Hacl_RSAPSS_rsapss_sign(
  uint32_t modBits,
  uint32_t eBits,
  uint32_t dBits,
  uint64_t *skey,
  uint32_t sLen,
  uint8_t *salt,
  uint32_t msgLen,
  uint8_t *msg,
  uint8_t *sgnt
);

bool
Hacl_RSAPSS_rsapss_verify(
  uint32_t modBits,
  uint32_t eBits,
  uint64_t *pkey,
  uint32_t sLen,
  uint8_t *sgnt,
  uint32_t msgLen,
  uint8_t *msg
);

void Hacl_Bignum_Convert_bn_from_bytes_be(uint32_t len, uint8_t *b, uint64_t *res);

void Hacl_Bignum_Convert_bn_from_bytes_le(uint32_t len, uint8_t *b, uint64_t *res);

void Hacl_Bignum_Convert_bn_to_bytes_be(uint32_t len, uint64_t *b, uint8_t *res);

void Hacl_Bignum_Convert_bn_to_bytes_le(uint32_t len, uint64_t *b, uint8_t *res);

#define __Hacl_RSAPSS_H_DEFINED
#endif
