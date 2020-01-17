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

#ifndef __Vale_Inline_H
#define __Vale_Inline_H




/* SNIPPET_START: cswap2 */

<<<<<<< HEAD
static inline void cswap2(uint64_t bit, uint64_t *p0, uint64_t *p1);
=======
inline static void cswap2_inline(uint64_t bit, uint64_t *p0, uint64_t *p1);
>>>>>>> master

/* SNIPPET_END: cswap2 */

/* SNIPPET_START: fsqr */

<<<<<<< HEAD
static inline void fsqr(uint64_t *out1, uint64_t *f1, uint64_t *tmp);
=======
inline static void fsqr_inline(uint64_t *tmp, uint64_t *f1, uint64_t *out1);
>>>>>>> master

/* SNIPPET_END: fsqr */

/* SNIPPET_START: fsqr2 */

<<<<<<< HEAD
static inline void fsqr2(uint64_t *out1, uint64_t *f1, uint64_t *tmp);
=======
inline static void fsqr2_inline(uint64_t *tmp, uint64_t *f1, uint64_t *out1);
>>>>>>> master

/* SNIPPET_END: fsqr2 */

/* SNIPPET_START: fmul */

<<<<<<< HEAD
static inline void fmul(uint64_t *out1, uint64_t *f1, uint64_t *f2, uint64_t *tmp);
=======
inline static void fmul_inline(uint64_t *tmp, uint64_t *f1, uint64_t *out1, uint64_t *f2);
>>>>>>> master

/* SNIPPET_END: fmul */

/* SNIPPET_START: fmul2 */

<<<<<<< HEAD
static inline void fmul2(uint64_t *out1, uint64_t *f1, uint64_t *f2, uint64_t *tmp);
=======
inline static void fmul2_inline(uint64_t *tmp, uint64_t *f1, uint64_t *out1, uint64_t *f2);
>>>>>>> master

/* SNIPPET_END: fmul2 */

/* SNIPPET_START: fmul_scalar */

<<<<<<< HEAD
static inline void fmul_scalar(uint64_t *out1, uint64_t *f1, uint64_t f2);
=======
inline static void fmul1_inline(uint64_t *out1, uint64_t *f1, uint64_t f2);
>>>>>>> master

/* SNIPPET_END: fmul_scalar */

/* SNIPPET_START: add_scalar */

<<<<<<< HEAD
static inline uint64_t add_scalar(uint64_t *out1, uint64_t *f1, uint64_t f2);
=======
inline static uint64_t add1_inline(uint64_t *out1, uint64_t *f1, uint64_t f2);
>>>>>>> master

/* SNIPPET_END: add_scalar */

/* SNIPPET_START: fadd */

<<<<<<< HEAD
static inline void fadd(uint64_t *out1, uint64_t *f1, uint64_t *f2);
=======
inline static void fadd_inline(uint64_t *out1, uint64_t *f1, uint64_t *f2);
>>>>>>> master

/* SNIPPET_END: fadd */

/* SNIPPET_START: fsub */

<<<<<<< HEAD
static inline void fsub(uint64_t *out1, uint64_t *f1, uint64_t *f2);
=======
inline static void fsub_inline(uint64_t *out1, uint64_t *f1, uint64_t *f2);
>>>>>>> master

/* SNIPPET_END: fsub */

#define __Vale_Inline_H_DEFINED
#endif
