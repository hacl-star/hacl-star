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

#include "evercrypt_targetconfig.h"
#include "lib_intrinsics.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_Kremlib.h"

void
Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(
  uint32_t aLen,
  uint64_t *a,
  uint64_t *b,
  uint64_t *tmp,
  uint64_t *res
);

void
Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(
  uint32_t aLen,
  uint64_t *a,
  uint64_t *tmp,
  uint64_t *res
);

static inline void
Hacl_Bignum_bn_add_mod_n_u64(
  uint32_t len1,
  uint64_t *n,
  uint64_t *a,
  uint64_t *b,
  uint64_t *res
)
{
  uint64_t c2 = (uint64_t)0U;
  uint32_t k0 = len1 / (uint32_t)4U * (uint32_t)4U;
  uint64_t c0;
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
    {
      uint64_t t1 = a[(uint32_t)4U * i];
      uint64_t t20 = b[(uint32_t)4U * i];
      c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t1, t20, res + (uint32_t)4U * i);
      {
        uint64_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
        c2 =
          Lib_IntTypes_Intrinsics_add_carry_u64(c2,
            t10,
            t21,
            res + (uint32_t)4U * i + (uint32_t)1U);
        {
          uint64_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
          c2 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c2,
              t11,
              t22,
              res + (uint32_t)4U * i + (uint32_t)2U);
          {
            uint64_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
            uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
            c2 =
              Lib_IntTypes_Intrinsics_add_carry_u64(c2,
                t12,
                t2,
                res + (uint32_t)4U * i + (uint32_t)3U);
          }
        }
      }
    }
  }
  {
    uint32_t i;
    for (i = k0; i < len1; i++)
    {
      uint64_t t1 = a[i];
      uint64_t t2 = b[i];
      c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t1, t2, res + i);
    }
  }
  c0 = c2;
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  {
    uint64_t tmp[len1];
    memset(tmp, 0U, len1 * sizeof (uint64_t));
    {
      uint64_t c3 = (uint64_t)0U;
      uint32_t k = len1 / (uint32_t)4U * (uint32_t)4U;
      uint64_t c1;
      uint64_t c;
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = res[(uint32_t)4U * i];
          uint64_t t20 = n[(uint32_t)4U * i];
          c3 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c3, t1, t20, tmp + (uint32_t)4U * i);
          {
            uint64_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
            uint64_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
            c3 =
              Lib_IntTypes_Intrinsics_sub_borrow_u64(c3,
                t10,
                t21,
                tmp + (uint32_t)4U * i + (uint32_t)1U);
            {
              uint64_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
              uint64_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
              c3 =
                Lib_IntTypes_Intrinsics_sub_borrow_u64(c3,
                  t11,
                  t22,
                  tmp + (uint32_t)4U * i + (uint32_t)2U);
              {
                uint64_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
                uint64_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
                c3 =
                  Lib_IntTypes_Intrinsics_sub_borrow_u64(c3,
                    t12,
                    t2,
                    tmp + (uint32_t)4U * i + (uint32_t)3U);
              }
            }
          }
        }
      }
      {
        uint32_t i;
        for (i = k; i < len1; i++)
        {
          uint64_t t1 = res[i];
          uint64_t t2 = n[i];
          c3 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c3, t1, t2, tmp + i);
        }
      }
      c1 = c3;
      c = c0 - c1;
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < len1; i++)
        {
          uint64_t *os = res;
          uint64_t x = (c & res[i]) | (~c & tmp[i]);
          os[i] = x;
        }
      }
    }
  }
}

static inline uint64_t Hacl_Bignum_ModInvLimb_mod_inv_uint64(uint64_t n0)
{
  uint64_t alpha = (uint64_t)9223372036854775808U;
  uint64_t beta = n0;
  uint64_t ub = (uint64_t)0U;
  uint64_t vb = (uint64_t)0U;
  ub = (uint64_t)1U;
  vb = (uint64_t)0U;
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < (uint32_t)64U; i++)
    {
      uint64_t us = ub;
      uint64_t vs = vb;
      uint64_t u_is_odd = (uint64_t)0U - (us & (uint64_t)1U);
      uint64_t beta_if_u_is_odd = beta & u_is_odd;
      ub = ((us ^ beta_if_u_is_odd) >> (uint32_t)1U) + (us & beta_if_u_is_odd);
      {
        uint64_t alpha_if_u_is_odd = alpha & u_is_odd;
        vb = (vs >> (uint32_t)1U) + alpha_if_u_is_odd;
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
