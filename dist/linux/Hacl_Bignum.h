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

#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_Kremlib.h"

static inline u64
Hacl_Bignum_Multiplication_mul_carry_add_u64_st(u64 c_in, u64 a, u64 b, u64 *out)
{
  uint128_t uu____0 = (uint128_t)out[0U];
  uint128_t res = (uint128_t)a * b + (uint128_t)c_in + uu____0;
  out[0U] = (uint64_t)res;
  return (uint64_t)(res >> (u32)64U);
}

static inline bool Hacl_Bignum_bn_is_bit_set(u32 len, u64 *input, u32 ind)
{
  u32 i = ind / (u32)64U;
  u32 j = ind % (u32)64U;
  u64 tmp = input[i];
  u64 tmp1 = tmp >> j & (u64)1U;
  return tmp1 == (u64)1U;
}

static inline void Hacl_Bignum_bn_bit_set(u32 len, u64 *input, u32 ind)
{
  u32 i = ind / (u32)64U;
  u32 j = ind % (u32)64U;
  input[i] = input[i] | (u64)1U << j;
}

static inline bool Hacl_Bignum_bn_is_less(u32 len, u64 *a, u64 *b)
{
  u64 acc = (u64)0U;
  u64 mask;
  {
    u32 i;
    for (i = (u32)0U; i < len; i++)
    {
      u64 beq = FStar_UInt64_eq_mask(a[i], b[i]);
      u64 blt = ~FStar_UInt64_gte_mask(a[i], b[i]);
      acc = (beq & acc) | (~beq & ((blt & (u64)0xFFFFFFFFFFFFFFFFU) | (~blt & (u64)0U)));
    }
  }
  mask = acc;
  return mask == (u64)0xFFFFFFFFFFFFFFFFU;
}

static inline u64 Hacl_Bignum_ModInv64_mod_inv_u64(u64 n0)
{
  u64 alpha = (u64)9223372036854775808U;
  u64 beta = n0;
  u64 ub = (u64)0U;
  u64 vb = (u64)0U;
  ub = (u64)1U;
  vb = (u64)0U;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)64U; i++)
    {
      u64 us = ub;
      u64 vs = vb;
      u64 u_is_odd = (u64)0U - (us & (u64)1U);
      u64 beta_if_u_is_odd = beta & u_is_odd;
      ub = ((us ^ beta_if_u_is_odd) >> (u32)1U) + (us & beta_if_u_is_odd);
      {
        u64 alpha_if_u_is_odd = alpha & u_is_odd;
        vb = (vs >> (u32)1U) + alpha_if_u_is_odd;
      }
    }
  }
  return vb;
}

#if defined(__cplusplus)
}
#endif

#define __Hacl_Bignum_H_DEFINED
#endif
