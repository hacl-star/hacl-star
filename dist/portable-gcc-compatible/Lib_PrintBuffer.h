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

#ifndef __Lib_PrintBuffer_H
#define __Lib_PrintBuffer_H




/* SNIPPET_START: Lib_PrintBuffer_print_bytes */

extern void Lib_PrintBuffer_print_bytes(uint32_t len, uint8_t *buf1);

/* SNIPPET_END: Lib_PrintBuffer_print_bytes */

/* SNIPPET_START: Lib_PrintBuffer_print_compare */

extern void Lib_PrintBuffer_print_compare(uint32_t len, uint8_t *buf0, uint8_t *buf1);

/* SNIPPET_END: Lib_PrintBuffer_print_compare */

/* SNIPPET_START: Lib_PrintBuffer_print_compare_display */

extern void Lib_PrintBuffer_print_compare_display(uint32_t len, uint8_t *buf0, uint8_t *buf1);

/* SNIPPET_END: Lib_PrintBuffer_print_compare_display */

/* SNIPPET_START: Lib_PrintBuffer_result_compare_display */

extern bool Lib_PrintBuffer_result_compare_display(uint32_t len, uint8_t *buf0, uint8_t *buf1);

/* SNIPPET_END: Lib_PrintBuffer_result_compare_display */

#define __Lib_PrintBuffer_H_DEFINED
#endif
