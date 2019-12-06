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

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"

#ifndef __TestLib_H
#define __TestLib_H




/* SNIPPET_START: TestLib_touch */

extern void TestLib_touch(int32_t uu____11);

/* SNIPPET_END: TestLib_touch */

/* SNIPPET_START: TestLib_check */

extern void TestLib_check(bool uu____26);

/* SNIPPET_END: TestLib_check */

/* SNIPPET_START: TestLib_check8 */

extern void TestLib_check8(int8_t uu____48, int8_t uu____49);

/* SNIPPET_END: TestLib_check8 */

/* SNIPPET_START: TestLib_check16 */

extern void TestLib_check16(int16_t uu____70, int16_t uu____71);

/* SNIPPET_END: TestLib_check16 */

/* SNIPPET_START: TestLib_check32 */

extern void TestLib_check32(int32_t uu____92, int32_t uu____93);

/* SNIPPET_END: TestLib_check32 */

/* SNIPPET_START: TestLib_check64 */

extern void TestLib_check64(int64_t uu____114, int64_t uu____115);

/* SNIPPET_END: TestLib_check64 */

/* SNIPPET_START: TestLib_checku8 */

extern void TestLib_checku8(uint8_t uu____136, uint8_t uu____137);

/* SNIPPET_END: TestLib_checku8 */

/* SNIPPET_START: TestLib_checku16 */

extern void TestLib_checku16(uint16_t uu____158, uint16_t uu____159);

/* SNIPPET_END: TestLib_checku16 */

/* SNIPPET_START: TestLib_checku32 */

extern void TestLib_checku32(uint32_t uu____180, uint32_t uu____181);

/* SNIPPET_END: TestLib_checku32 */

/* SNIPPET_START: TestLib_checku64 */

extern void TestLib_checku64(uint64_t uu____202, uint64_t uu____203);

/* SNIPPET_END: TestLib_checku64 */

/* SNIPPET_START: TestLib_compare_and_print */

extern void
TestLib_compare_and_print(C_String_t uu____242, uint8_t *b1, uint8_t *b2, uint32_t l);

/* SNIPPET_END: TestLib_compare_and_print */

/* SNIPPET_START: TestLib_unsafe_malloc */

extern uint8_t *TestLib_unsafe_malloc(uint32_t l);

/* SNIPPET_END: TestLib_unsafe_malloc */

/* SNIPPET_START: TestLib_perr */

extern void TestLib_perr(uint32_t uu____281);

/* SNIPPET_END: TestLib_perr */

/* SNIPPET_START: TestLib_print_clock_diff */

extern void TestLib_print_clock_diff(clock_t uu____302, clock_t uu____303);

/* SNIPPET_END: TestLib_print_clock_diff */

/* SNIPPET_START: TestLib_uint8_p_null */

KRML_DEPRECATED("p_null from TestLib; use LowStar.Buffer.null instead")

extern uint8_t *TestLib_uint8_p_null;

/* SNIPPET_END: TestLib_uint8_p_null */

/* SNIPPET_START: TestLib_uint32_p_null */

KRML_DEPRECATED("p_null from TestLib; use LowStar.Buffer.null instead")

extern uint32_t *TestLib_uint32_p_null;

/* SNIPPET_END: TestLib_uint32_p_null */

/* SNIPPET_START: TestLib_uint64_p_null */

KRML_DEPRECATED("p_null from TestLib; use LowStar.Buffer.null instead")

extern uint64_t *TestLib_uint64_p_null;

/* SNIPPET_END: TestLib_uint64_p_null */

/* SNIPPET_START: TestLib_cpucycles */

extern TestLib_cycles TestLib_cpucycles();

/* SNIPPET_END: TestLib_cpucycles */

/* SNIPPET_START: TestLib_print_cycles_per_round */

extern void
TestLib_print_cycles_per_round(
  TestLib_cycles uu____378,
  TestLib_cycles uu____379,
  uint32_t uu____380
);

/* SNIPPET_END: TestLib_print_cycles_per_round */

#define __TestLib_H_DEFINED
#endif
