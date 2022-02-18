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


#ifndef __TestLib_H
#define __TestLib_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"




extern void TestLib_touch(s32 uu___);

extern void TestLib_check(bool uu___);

extern void TestLib_check8(s8 uu___, s8 uu___1);

extern void TestLib_check16(s16 uu___, s16 uu___1);

extern void TestLib_check32(s32 uu___, s32 uu___1);

extern void TestLib_check64(s64 uu___, s64 uu___1);

extern void TestLib_checku8(u8 uu___, u8 uu___1);

extern void TestLib_checku16(u16 uu___, u16 uu___1);

extern void TestLib_checku32(u32 uu___, u32 uu___1);

extern void TestLib_checku64(u64 uu___, u64 uu___1);

extern void TestLib_compare_and_print(C_String_t uu___, u8 *b1, u8 *b2, u32 l);

extern u8 *TestLib_unsafe_malloc(u32 l);

extern void TestLib_perr(u32 uu___);

extern void TestLib_print_clock_diff(clock_t uu___, clock_t uu___1);

KRML_DEPRECATED("p_null from TestLib; use LowStar.Buffer.null instead")

extern u8 *TestLib_uint8_p_null;

KRML_DEPRECATED("p_null from TestLib; use LowStar.Buffer.null instead")

extern u32 *TestLib_uint32_p_null;

KRML_DEPRECATED("p_null from TestLib; use LowStar.Buffer.null instead")

extern u64 *TestLib_uint64_p_null;

extern TestLib_cycles TestLib_cpucycles();

extern void
TestLib_print_cycles_per_round(TestLib_cycles uu___, TestLib_cycles uu___1, u32 uu___2);

#if defined(__cplusplus)
}
#endif

#define __TestLib_H_DEFINED
#endif
