/* MIT License
 *
 * Copyright (c) 2016-2018 INRIA and Microsoft Corporation
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



#ifndef __Hacl_Poly1305_64_H
#define __Hacl_Poly1305_64_H


#include "kremlib.h"

typedef unsigned __int128 uint128_t, FStar_UInt128_uint128;

#define FStar_Int_Cast_Full_uint64_to_uint128(x0) ((uint128_t)(x0))
#define FStar_UInt64_eq_mask(x0, x1) ((x0) == (x1)?(uint64_t)0xffffffffffffffff:(uint64_t) 0)
#define FStar_UInt64_gte_mask(x0, x1) ((x0) >= (x1)?(uint64_t)0xffffffffffffffff:(uint64_t) 0)
#define FStar_UInt128_add(x0, x1) ((x0) + (x1))
#define FStar_UInt128_add_mod(x0, x1) ((x0) + (x1))
#define FStar_UInt128_logand(x0, x1) ((x0) & (x1))
#define FStar_UInt128_logor(x0, x1) ((x0) | (x1))
#define FStar_UInt128_shift_left(x0, x1) ((x0) << (x1))
#define FStar_UInt128_shift_right(x0, x1) ((x0) >> (x1))
#define FStar_UInt128_uint64_to_uint128(x0) ((uint128_t)(x0))
#define FStar_UInt128_uint128_to_uint64(x0) ((uint64_t)(x0))
#define FStar_UInt128_mul_wide(x0, x1) ((uint128_t)x0 * x1)

static uint128_t load128_le(uint8_t* in){
  uint64_t lo = load64_le(in);
  uint64_t hi = load64_le(in+8);
  return ((uint128_t)hi << 64 | lo);
}
static uint128_t store128_le(uint8_t* in, uint128_t u) {
  store64_le(in,(uint64_t)u);
  store64_le(in+8,(uint64_t)(u >> 64));
}
typedef uint8_t *Hacl_Poly1305_64_uint8_p;

typedef uint64_t Hacl_Poly1305_64_uint64_t;

void
Hacl_Poly1305_64_poly1305_mac(
  uint8_t *output,
  uint8_t *input,
  uint64_t len1,
  uint8_t *k1
);

#define __Hacl_Poly1305_64_H_DEFINED
#endif
