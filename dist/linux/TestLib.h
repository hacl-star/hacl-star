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

#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"

#ifndef __TestLib_H
#define __TestLib_H




extern void TestLib_touch(s32 uu____7);

extern void TestLib_check(bool uu____15);

extern void TestLib_check8(s8 uu____30, s8 uu____31);

extern void TestLib_check16(s16 uu____46, s16 uu____47);

extern void TestLib_check32(s32 uu____62, s32 uu____63);

extern void TestLib_check64(s64 uu____78, s64 uu____79);

extern void TestLib_checku8(u8 uu____94, u8 uu____95);

extern void TestLib_checku16(u16 uu____110, u16 uu____111);

extern void TestLib_checku32(u32 uu____126, u32 uu____127);

extern void TestLib_checku64(u64 uu____142, u64 uu____143);

extern void TestLib_compare_and_print(C_String_t uu____176, u8 *b1, u8 *b2, u32 l);

extern u8 *TestLib_unsafe_malloc(u32 l);

extern void TestLib_perr(u32 uu____203);

extern void TestLib_print_clock_diff(clock_t uu____218, clock_t uu____219);

KRML_DEPRECATED("p_null from TestLib; use LowStar.Buffer.null instead")

extern u8 *TestLib_uint8_p_null;

KRML_DEPRECATED("p_null from TestLib; use LowStar.Buffer.null instead")

extern u32 *TestLib_uint32_p_null;

KRML_DEPRECATED("p_null from TestLib; use LowStar.Buffer.null instead")

extern u64 *TestLib_uint64_p_null;

extern TestLib_cycles TestLib_cpucycles();

extern void
TestLib_print_cycles_per_round(
  TestLib_cycles uu____276,
  TestLib_cycles uu____277,
  u32 uu____278
);

#define __TestLib_H_DEFINED
#endif
