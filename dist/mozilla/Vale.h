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


#ifndef __Vale_H
#define __Vale_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include <stdbool.h>




extern uint64_t add_scalar_e(uint64_t *x0, uint64_t *x1, uint64_t x2);

extern uint64_t fadd_e(uint64_t *x0, uint64_t *x1, uint64_t *x2);

extern uint64_t cswap2_e(uint64_t x0, uint64_t *x1, uint64_t *x2);

extern uint64_t fsqr_e(uint64_t *x0, uint64_t *x1, uint64_t *x2);

extern uint64_t fsqr2_e(uint64_t *x0, uint64_t *x1, uint64_t *x2);

extern uint64_t fmul_e(uint64_t *x0, uint64_t *x1, uint64_t *x2, uint64_t *x3);

extern uint64_t fmul2_e(uint64_t *x0, uint64_t *x1, uint64_t *x2, uint64_t *x3);

extern uint64_t fmul_scalar_e(uint64_t *x0, uint64_t *x1, uint64_t x2);

extern uint64_t fsub_e(uint64_t *x0, uint64_t *x1, uint64_t *x2);

#if defined(__cplusplus)
}
#endif

#define __Vale_H_DEFINED
#endif
