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


#ifndef __Hacl_Kremlib_H
#define __Hacl_Kremlib_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"




static inline uint8_t FStar_UInt8_eq_mask(uint8_t a, uint8_t b);

static inline uint64_t FStar_UInt64_eq_mask(uint64_t a, uint64_t b);

static inline uint64_t FStar_UInt64_gte_mask(uint64_t a, uint64_t b);

static inline uint128_t FStar_UInt128_add(uint128_t a, uint128_t b);

static inline uint128_t FStar_UInt128_add_mod(uint128_t a, uint128_t b);

static inline uint128_t FStar_UInt128_logor(uint128_t a, uint128_t b);

static inline uint128_t FStar_UInt128_shift_left(uint128_t a, uint32_t s);

static inline uint128_t FStar_UInt128_shift_right(uint128_t a, uint32_t s);

static inline uint128_t FStar_UInt128_uint64_to_uint128(uint64_t a);

static inline uint64_t FStar_UInt128_uint128_to_uint64(uint128_t a);

static inline uint128_t FStar_UInt128_mul_wide(uint64_t x, uint64_t y);

static inline void store128_le(uint8_t *x0, uint128_t x1);

static inline void store128_be(uint8_t *x0, uint128_t x1);

static inline uint128_t load128_be(uint8_t *x0);

uint32_t LowStar_Vector_new_capacity(uint32_t cap);

#if defined(__cplusplus)
}
#endif

#define __Hacl_Kremlib_H_DEFINED
#endif
