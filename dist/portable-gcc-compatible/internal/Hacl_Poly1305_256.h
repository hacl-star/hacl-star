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


#ifndef __internal_Hacl_Poly1305_256_H
#define __internal_Hacl_Poly1305_256_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "../Hacl_Poly1305_256.h"
#include "libintvector.h"
/* SNIPPET_START: Hacl_Impl_Poly1305_Field32xN_256_load_acc4 */

void
Hacl_Impl_Poly1305_Field32xN_256_load_acc4(Lib_IntVector_Intrinsics_vec256 *acc, uint8_t *b);

/* SNIPPET_END: Hacl_Impl_Poly1305_Field32xN_256_load_acc4 */

/* SNIPPET_START: Hacl_Impl_Poly1305_Field32xN_256_fmul_r4_normalize */

void
Hacl_Impl_Poly1305_Field32xN_256_fmul_r4_normalize(
  Lib_IntVector_Intrinsics_vec256 *out,
  Lib_IntVector_Intrinsics_vec256 *p
);

/* SNIPPET_END: Hacl_Impl_Poly1305_Field32xN_256_fmul_r4_normalize */

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_Poly1305_256_H_DEFINED
#endif
