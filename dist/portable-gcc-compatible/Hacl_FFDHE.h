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


#ifndef __Hacl_FFDHE_H
#define __Hacl_FFDHE_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "Hacl_Spec.h"
#include "Hacl_Impl_FFDHE_Constants.h"
#include "Hacl_Bignum_Base.h"

/* SNIPPET_START: Hacl_FFDHE_ffdhe_len */

uint32_t Hacl_FFDHE_ffdhe_len(Spec_FFDHE_ffdhe_alg a);

/* SNIPPET_END: Hacl_FFDHE_ffdhe_len */

/* SNIPPET_START: Hacl_FFDHE_new_ffdhe_precomp_p */

uint64_t *Hacl_FFDHE_new_ffdhe_precomp_p(Spec_FFDHE_ffdhe_alg a);

/* SNIPPET_END: Hacl_FFDHE_new_ffdhe_precomp_p */

/* SNIPPET_START: Hacl_FFDHE_ffdhe_secret_to_public_precomp */

void
Hacl_FFDHE_ffdhe_secret_to_public_precomp(
  Spec_FFDHE_ffdhe_alg a,
  uint64_t *p_r2_n,
  uint8_t *sk,
  uint8_t *pk
);

/* SNIPPET_END: Hacl_FFDHE_ffdhe_secret_to_public_precomp */

/* SNIPPET_START: Hacl_FFDHE_ffdhe_secret_to_public */

void Hacl_FFDHE_ffdhe_secret_to_public(Spec_FFDHE_ffdhe_alg a, uint8_t *sk, uint8_t *pk);

/* SNIPPET_END: Hacl_FFDHE_ffdhe_secret_to_public */

/* SNIPPET_START: Hacl_FFDHE_ffdhe_shared_secret_precomp */

uint64_t
Hacl_FFDHE_ffdhe_shared_secret_precomp(
  Spec_FFDHE_ffdhe_alg a,
  uint64_t *p_r2_n,
  uint8_t *sk,
  uint8_t *pk,
  uint8_t *ss
);

/* SNIPPET_END: Hacl_FFDHE_ffdhe_shared_secret_precomp */

/* SNIPPET_START: Hacl_FFDHE_ffdhe_shared_secret */

uint64_t
Hacl_FFDHE_ffdhe_shared_secret(Spec_FFDHE_ffdhe_alg a, uint8_t *sk, uint8_t *pk, uint8_t *ss);

/* SNIPPET_END: Hacl_FFDHE_ffdhe_shared_secret */

#if defined(__cplusplus)
}
#endif

#define __Hacl_FFDHE_H_DEFINED
#endif
