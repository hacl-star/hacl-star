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


#ifndef __Hacl_IntTypes_Intrinsics_H
#define __Hacl_IntTypes_Intrinsics_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"



#include "libintvector.h"
static inline u32 Hacl_IntTypes_Intrinsics_add_carry_u32(u32 cin, u32 x, u32 y, u32 *r)
{
  u64 res = (u64)x + (u64)cin + (u64)y;
  u32 c = (u32)(res >> (u32)32U);
  r[0U] = (u32)res;
  return c;
}

static inline u32 Hacl_IntTypes_Intrinsics_sub_borrow_u32(u32 cin, u32 x, u32 y, u32 *r)
{
  u64 res = (u64)x - (u64)y - (u64)cin;
  u32 c = (u32)(res >> (u32)32U) & (u32)1U;
  r[0U] = (u32)res;
  return c;
}

static inline u64 Hacl_IntTypes_Intrinsics_add_carry_u64(u64 cin, u64 x, u64 y, u64 *r)
{
  u64 res = x + cin + y;
  u64 c = (~FStar_UInt64_gte_mask(res, x) | (FStar_UInt64_eq_mask(res, x) & cin)) & (u64)1U;
  r[0U] = res;
  return c;
}

static inline u64 Hacl_IntTypes_Intrinsics_sub_borrow_u64(u64 cin, u64 x, u64 y, u64 *r)
{
  u64 res = x - y - cin;
  u64
  c =
    ((FStar_UInt64_gte_mask(res, x) & ~FStar_UInt64_eq_mask(res, x))
    | (FStar_UInt64_eq_mask(res, x) & cin))
    & (u64)1U;
  r[0U] = res;
  return c;
}

#if defined(__cplusplus)
}
#endif

#define __Hacl_IntTypes_Intrinsics_H_DEFINED
#endif
