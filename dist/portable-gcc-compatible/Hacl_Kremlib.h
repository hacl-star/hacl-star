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




/* SNIPPET_START: FStar_UInt8_eq_mask */

static inline uint8_t FStar_UInt8_eq_mask(uint8_t a, uint8_t b);

/* SNIPPET_END: FStar_UInt8_eq_mask */

/* SNIPPET_START: FStar_UInt64_eq_mask */

static inline uint64_t FStar_UInt64_eq_mask(uint64_t a, uint64_t b);

/* SNIPPET_END: FStar_UInt64_eq_mask */

/* SNIPPET_START: FStar_UInt64_gte_mask */

static inline uint64_t FStar_UInt64_gte_mask(uint64_t a, uint64_t b);

/* SNIPPET_END: FStar_UInt64_gte_mask */

/* SNIPPET_START: FStar_UInt128_add */

static inline FStar_UInt128_uint128
FStar_UInt128_add(FStar_UInt128_uint128 a, FStar_UInt128_uint128 b);

/* SNIPPET_END: FStar_UInt128_add */

/* SNIPPET_START: FStar_UInt128_add_mod */

static inline FStar_UInt128_uint128
FStar_UInt128_add_mod(FStar_UInt128_uint128 a, FStar_UInt128_uint128 b);

/* SNIPPET_END: FStar_UInt128_add_mod */

/* SNIPPET_START: FStar_UInt128_logor */

static inline FStar_UInt128_uint128
FStar_UInt128_logor(FStar_UInt128_uint128 a, FStar_UInt128_uint128 b);

/* SNIPPET_END: FStar_UInt128_logor */

/* SNIPPET_START: FStar_UInt128_shift_left */

static inline FStar_UInt128_uint128
FStar_UInt128_shift_left(FStar_UInt128_uint128 a, uint32_t s);

/* SNIPPET_END: FStar_UInt128_shift_left */

/* SNIPPET_START: FStar_UInt128_shift_right */

static inline FStar_UInt128_uint128
FStar_UInt128_shift_right(FStar_UInt128_uint128 a, uint32_t s);

/* SNIPPET_END: FStar_UInt128_shift_right */

/* SNIPPET_START: FStar_UInt128_uint64_to_uint128 */

static inline FStar_UInt128_uint128 FStar_UInt128_uint64_to_uint128(uint64_t a);

/* SNIPPET_END: FStar_UInt128_uint64_to_uint128 */

/* SNIPPET_START: FStar_UInt128_uint128_to_uint64 */

static inline uint64_t FStar_UInt128_uint128_to_uint64(FStar_UInt128_uint128 a);

/* SNIPPET_END: FStar_UInt128_uint128_to_uint64 */

/* SNIPPET_START: FStar_UInt128_mul_wide */

static inline FStar_UInt128_uint128 FStar_UInt128_mul_wide(uint64_t x, uint64_t y);

/* SNIPPET_END: FStar_UInt128_mul_wide */

/* SNIPPET_START: store128_le */

static inline void store128_le(uint8_t *x0, FStar_UInt128_uint128 x1);

/* SNIPPET_END: store128_le */

/* SNIPPET_START: store128_be */

static inline void store128_be(uint8_t *x0, FStar_UInt128_uint128 x1);

/* SNIPPET_END: store128_be */

/* SNIPPET_START: load128_be */

static inline FStar_UInt128_uint128 load128_be(uint8_t *x0);

/* SNIPPET_END: load128_be */

/* SNIPPET_START: LowStar_Vector_new_capacity */

uint32_t LowStar_Vector_new_capacity(uint32_t cap);

/* SNIPPET_END: LowStar_Vector_new_capacity */

#if defined(__cplusplus)
}
#endif

#define __Hacl_Kremlib_H_DEFINED
#endif
