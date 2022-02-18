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


#ifndef __Hacl_IntTypes_Intrinsics_128_H
#define __Hacl_IntTypes_Intrinsics_128_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_Kremlib.h"

static inline u64 Hacl_IntTypes_Intrinsics_128_add_carry_u64(u64 cin, u64 x, u64 y, u64 *r)
{
  uint128_t res = (uint128_t)x + (uint128_t)cin + (uint128_t)y;
  u64 c = (uint64_t)(res >> (u32)64U);
  r[0U] = (uint64_t)res;
  return c;
}

static inline u64 Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(u64 cin, u64 x, u64 y, u64 *r)
{
  uint128_t res = (uint128_t)x - (uint128_t)y - (uint128_t)cin;
  u64 c = (uint64_t)(res >> (u32)64U) & (u64)1U;
  r[0U] = (uint64_t)res;
  return c;
}

#if defined(__cplusplus)
}
#endif

#define __Hacl_IntTypes_Intrinsics_128_H_DEFINED
#endif
