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


#ifndef __Vale_Inline_H
#define __Vale_Inline_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"




static inline void cswap2(uint64_t bit, uint64_t *p0, uint64_t *p1);

static inline void fsqr(uint64_t *out, uint64_t *f1, uint64_t *tmp);

static inline void fsqr2(uint64_t *out, uint64_t *f1, uint64_t *tmp);

static inline void fmul(uint64_t *out, uint64_t *f1, uint64_t *f2, uint64_t *tmp);

static inline void fmul2(uint64_t *out, uint64_t *f1, uint64_t *f2, uint64_t *tmp);

static inline void fmul_scalar(uint64_t *out, uint64_t *f1, uint64_t f2);

static inline uint64_t add_scalar(uint64_t *out, uint64_t *f1, uint64_t f2);

static inline void fadd(uint64_t *out, uint64_t *f1, uint64_t *f2);

static inline void fsub(uint64_t *out, uint64_t *f1, uint64_t *f2);

#if defined(__cplusplus)
}
#endif

#define __Vale_Inline_H_DEFINED
#endif
