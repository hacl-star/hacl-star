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


#include "Hacl_Impl_LowLevel_RawCmp.h"

/* SNIPPET_START: Hacl_Impl_LowLevel_RawCmp_eq_u8_nCT */

bool Hacl_Impl_LowLevel_RawCmp_eq_u8_nCT(uint8_t a, uint8_t b)
{
  return a == b;
}

/* SNIPPET_END: Hacl_Impl_LowLevel_RawCmp_eq_u8_nCT */

/* SNIPPET_START: Hacl_Impl_LowLevel_RawCmp_eq_u64_nCT */

bool Hacl_Impl_LowLevel_RawCmp_eq_u64_nCT(uint64_t a, uint64_t b)
{
  return a == b;
}

/* SNIPPET_END: Hacl_Impl_LowLevel_RawCmp_eq_u64_nCT */

/* SNIPPET_START: Hacl_Impl_LowLevel_RawCmp_eq_0_u64 */

bool Hacl_Impl_LowLevel_RawCmp_eq_0_u64(uint64_t a)
{
  return Hacl_Impl_LowLevel_RawCmp_eq_u64_nCT(a, (uint64_t)0U);
}

/* SNIPPET_END: Hacl_Impl_LowLevel_RawCmp_eq_0_u64 */

