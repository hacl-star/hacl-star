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
#include "kremlin/fstar_int.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"

#ifndef __Hacl_Impl_QTesla_H
#define __Hacl_Impl_QTesla_H

#include "Hacl_Kremlib.h"
#include "Lib_RandomBuffer_System.h"
#include "Hacl_SHA3.h"


/* SNIPPET_START: Hacl_Impl_QTesla_abs_ */

int32_t Hacl_Impl_QTesla_abs_(int32_t value);

/* SNIPPET_END: Hacl_Impl_QTesla_abs_ */

/* SNIPPET_START: Hacl_Impl_QTesla_check_ES */

bool Hacl_Impl_QTesla_check_ES(int32_t *p, uint32_t bound);

/* SNIPPET_END: Hacl_Impl_QTesla_check_ES */

/* SNIPPET_START: Hacl_Impl_QTesla_poly_uniform */

void Hacl_Impl_QTesla_poly_uniform(int32_t *a, uint8_t *seed);

/* SNIPPET_END: Hacl_Impl_QTesla_poly_uniform */

/* SNIPPET_START: Hacl_Impl_QTesla_qtesla_keygen */

int32_t Hacl_Impl_QTesla_qtesla_keygen(uint8_t *pk, uint8_t *sk);

/* SNIPPET_END: Hacl_Impl_QTesla_qtesla_keygen */

/* SNIPPET_START: Hacl_Impl_QTesla_sample_y */

void Hacl_Impl_QTesla_sample_y(int32_t *y, uint8_t *seed, uint32_t nonce);

/* SNIPPET_END: Hacl_Impl_QTesla_sample_y */

/* SNIPPET_START: Hacl_Impl_QTesla_hash_H */

void Hacl_Impl_QTesla_hash_H(uint8_t *c_bin, int32_t *v_, uint8_t *hm);

/* SNIPPET_END: Hacl_Impl_QTesla_hash_H */

/* SNIPPET_START: Hacl_Impl_QTesla_encode_c */

void Hacl_Impl_QTesla_encode_c(uint32_t *pos_list, int16_t *sign_list, uint8_t *c_bin);

/* SNIPPET_END: Hacl_Impl_QTesla_encode_c */

/* SNIPPET_START: Hacl_Impl_QTesla_sparse_mul */

void
Hacl_Impl_QTesla_sparse_mul(int32_t *prod, int16_t *s, uint32_t *pos_list, int16_t *sign_list);

/* SNIPPET_END: Hacl_Impl_QTesla_sparse_mul */

/* SNIPPET_START: Hacl_Impl_QTesla_sparse_mul32 */

void
Hacl_Impl_QTesla_sparse_mul32(
  int32_t *prod,
  int32_t *pk,
  uint32_t *pos_list,
  int16_t *sign_list
);

/* SNIPPET_END: Hacl_Impl_QTesla_sparse_mul32 */

/* SNIPPET_START: Hacl_Impl_QTesla_test_rejection */

bool Hacl_Impl_QTesla_test_rejection(int32_t *z);

/* SNIPPET_END: Hacl_Impl_QTesla_test_rejection */

/* SNIPPET_START: Hacl_Impl_QTesla_test_correctness */

int32_t Hacl_Impl_QTesla_test_correctness(int32_t *v_);

/* SNIPPET_END: Hacl_Impl_QTesla_test_correctness */

/* SNIPPET_START: Hacl_Impl_QTesla_qtesla_sign */

void
Hacl_Impl_QTesla_qtesla_sign(
  uint32_t *smlen,
  uint32_t mlen,
  uint8_t *m,
  uint8_t *sm,
  uint8_t *sk
);

/* SNIPPET_END: Hacl_Impl_QTesla_qtesla_sign */

/* SNIPPET_START: Hacl_Impl_QTesla_test_z */

int32_t Hacl_Impl_QTesla_test_z(int32_t *z);

/* SNIPPET_END: Hacl_Impl_QTesla_test_z */

/* SNIPPET_START: Hacl_Impl_QTesla_qtesla_verify */

int32_t
Hacl_Impl_QTesla_qtesla_verify(
  uint32_t *mlen,
  uint32_t smlen,
  uint8_t *m,
  uint8_t *sm,
  uint8_t *pk
);

/* SNIPPET_END: Hacl_Impl_QTesla_qtesla_verify */

/* SNIPPET_START: Hacl_Impl_QTesla_crypto_sign_keypair */

int32_t Hacl_Impl_QTesla_crypto_sign_keypair(uint8_t *pk, uint8_t *sk);

/* SNIPPET_END: Hacl_Impl_QTesla_crypto_sign_keypair */

/* SNIPPET_START: Hacl_Impl_QTesla_crypto_sign */

int32_t
Hacl_Impl_QTesla_crypto_sign(
  uint8_t *sm,
  uint64_t *smlen,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *sk
);

/* SNIPPET_END: Hacl_Impl_QTesla_crypto_sign */

/* SNIPPET_START: Hacl_Impl_QTesla_crypto_sign_open */

int32_t
Hacl_Impl_QTesla_crypto_sign_open(
  uint8_t *m,
  uint64_t *mlen,
  uint8_t *sm,
  uint64_t smlen,
  uint8_t *pk
);

/* SNIPPET_END: Hacl_Impl_QTesla_crypto_sign_open */

#define __Hacl_Impl_QTesla_H_DEFINED
#endif
