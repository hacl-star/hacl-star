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


#include "Hacl_Impl_P384_Exponent.h"

inline void
Hacl_Impl_P384_Exponent_exponent_p384(uint64_t *t, uint64_t *result, uint64_t *tempBuffer)
{
  uint64_t *t0 = tempBuffer;
  uint64_t *t1 = tempBuffer + (uint32_t)6U;
  uint64_t *t2 = tempBuffer + (uint32_t)12U;
  uint64_t *t3 = tempBuffer + (uint32_t)18U;
  uint64_t *t4 = tempBuffer + (uint32_t)24U;
  uint64_t *t5 = tempBuffer + (uint32_t)30U;
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_square_buffer_dh_p384(t, t0);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_multiplication_buffer_dh_p384(t, t0, t0);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_square_buffer_dh_p384(t0, t0);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_multiplication_buffer_dh_p384(t, t0, t0);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_square_buffer_dh_p384(t0, t1);
  Hacl_Impl_EC_MontgomeryMultiplication_fsquarePowN_dh_p384((uint32_t)2U, t1);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_multiplication_buffer_dh_p384(t0, t1, t1);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_square_buffer_dh_p384(t1, t2);
  Hacl_Impl_EC_MontgomeryMultiplication_fsquarePowN_dh_p384((uint32_t)5U, t2);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_multiplication_buffer_dh_p384(t2, t1, t2);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_square_buffer_dh_p384(t2, t3);
  Hacl_Impl_EC_MontgomeryMultiplication_fsquarePowN_dh_p384((uint32_t)11U, t3);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_multiplication_buffer_dh_p384(t2, t3, t2);
  Hacl_Impl_EC_MontgomeryMultiplication_fsquarePowN_dh_p384((uint32_t)6U, t2);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_multiplication_buffer_dh_p384(t2, t1, t1);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_square_buffer_dh_p384(t1, t2);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_multiplication_buffer_dh_p384(t2, t, t2);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_square_buffer_dh_p384(t2, t3);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_multiplication_buffer_dh_p384(t, t3, t3);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_square_buffer_dh_p384(t3, t4);
  Hacl_Impl_EC_MontgomeryMultiplication_fsquarePowN_dh_p384((uint32_t)30U, t4);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_multiplication_buffer_dh_p384(t4, t2, t4);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_square_buffer_dh_p384(t4, t5);
  Hacl_Impl_EC_MontgomeryMultiplication_fsquarePowN_dh_p384((uint32_t)62U, t5);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_multiplication_buffer_dh_p384(t4, t5, t4);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_square_buffer_dh_p384(t4, t5);
  Hacl_Impl_EC_MontgomeryMultiplication_fsquarePowN_dh_p384((uint32_t)125U, t5);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_multiplication_buffer_dh_p384(t4, t5, t4);
  Hacl_Impl_EC_MontgomeryMultiplication_fsquarePowN_dh_p384((uint32_t)3U, t4);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_multiplication_buffer_dh_p384(t4, t0, t4);
  Hacl_Impl_EC_MontgomeryMultiplication_fsquarePowN_dh_p384((uint32_t)33U, t4);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_multiplication_buffer_dh_p384(t4, t3, t4);
  Hacl_Impl_EC_MontgomeryMultiplication_fsquarePowN_dh_p384((uint32_t)94U, t4);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_multiplication_buffer_dh_p384(t4, t1, t4);
  Hacl_Impl_EC_MontgomeryMultiplication_fsquarePowN_dh_p384((uint32_t)2U, t4);
  Hacl_Impl_EC_MontgomeryMultiplication_montgomery_multiplication_buffer_dh_p384(t4, t, result);
}

