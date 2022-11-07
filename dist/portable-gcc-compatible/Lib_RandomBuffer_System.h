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


#ifndef __Lib_RandomBuffer_System_H
#define __Lib_RandomBuffer_System_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"




/* SNIPPET_START: Lib_RandomBuffer_System_randombytes */

KRML_DEPRECATED("random_crypto")

extern bool Lib_RandomBuffer_System_randombytes(uint8_t *buf, uint32_t len);

/* SNIPPET_END: Lib_RandomBuffer_System_randombytes */

/* SNIPPET_START: Lib_RandomBuffer_System_entropy_p */

extern void *Lib_RandomBuffer_System_entropy_p;

/* SNIPPET_END: Lib_RandomBuffer_System_entropy_p */

/* SNIPPET_START: Lib_RandomBuffer_System_crypto_random */

extern void Lib_RandomBuffer_System_crypto_random(uint8_t *buf, uint32_t len);

/* SNIPPET_END: Lib_RandomBuffer_System_crypto_random */

#if defined(__cplusplus)
}
#endif

#define __Lib_RandomBuffer_System_H_DEFINED
#endif
