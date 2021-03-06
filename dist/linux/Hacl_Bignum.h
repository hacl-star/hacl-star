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


#ifndef __Hacl_Bignum_H
#define __Hacl_Bignum_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "lib_intrinsics.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_Kremlib.h"

static inline u64 Hacl_Bignum_Base_mul_wide_add_u64(u64 a, u64 b, u64 c_in, u64 *out)
{
  uint128_t res = (uint128_t)a * b + (uint128_t)c_in;
  out[0U] = (uint64_t)res;
  return (uint64_t)(res >> (u32)64U);
}

static inline u64 Hacl_Bignum_Base_mul_wide_add2_u64(u64 a, u64 b, u64 c_in, u64 *out)
{
  u64 out0 = out[0U];
  uint128_t res = (uint128_t)a * b + (uint128_t)c_in + (uint128_t)out0;
  out[0U] = (uint64_t)res;
  return (uint64_t)(res >> (u32)64U);
}

static inline u64 Hacl_Bignum_Addition_bn_add_eq_len_u64(u32 aLen, u64 *a, u64 *b, u64 *res)
{
  u64 c = (u64)0U;
  {
    u32 i;
    for (i = (u32)0U; i < aLen / (u32)4U * (u32)4U / (u32)4U; i++)
    {
      u64 t1 = a[(u32)4U * i];
      u64 t20 = b[(u32)4U * i];
      u64 *res_i0 = res + (u32)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t20, res_i0);
      {
        u64 t10 = a[(u32)4U * i + (u32)1U];
        u64 t21 = b[(u32)4U * i + (u32)1U];
        u64 *res_i1 = res + (u32)4U * i + (u32)1U;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, t21, res_i1);
        {
          u64 t11 = a[(u32)4U * i + (u32)2U];
          u64 t22 = b[(u32)4U * i + (u32)2U];
          u64 *res_i2 = res + (u32)4U * i + (u32)2U;
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t22, res_i2);
          {
            u64 t12 = a[(u32)4U * i + (u32)3U];
            u64 t2 = b[(u32)4U * i + (u32)3U];
            u64 *res_i = res + (u32)4U * i + (u32)3U;
            c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t2, res_i);
          }
        }
      }
    }
  }
  {
    u32 i;
    for (i = aLen / (u32)4U * (u32)4U; i < aLen; i++)
    {
      u64 t1 = a[i];
      u64 t2 = b[i];
      u64 *res_i = res + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t2, res_i);
    }
  }
  return c;
}

#if defined(__cplusplus)
}
#endif

#define __Hacl_Bignum_H_DEFINED
#endif
