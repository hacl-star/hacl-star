/**
 * Copyright (c) 2017, Armando Faz <armfazh@ic.unicamp.br>. All rights reserved.
 * Institute of Computing.
 * University of Campinas, Brazil.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 *  * Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *  * Redistributions in binary form must reproduce the above
 *    copyright notice, this list of conditions and the following
 *    disclaimer in the documentation and/or other materials provided
 *    with the distribution.
 *  * Neither the name of University of Campinas nor the names of its
 *    contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#ifndef FP25519_X64_H
#define FP25519_X64_H

#include <stdint.h>

#ifndef ALIGN_BYTES
#define ALIGN_BYTES 32
#endif

#ifndef ALIGN
#ifdef __INTEL_COMPILER
#define ALIGN __declspec(align(ALIGN_BYTES))
#else
#define ALIGN __attribute__((aligned(ALIGN_BYTES)))
#endif
#endif

#define SIZE_BYTES_FP25519 32
#define NUM_WORDS_ELTFP25519_X64 4
typedef ALIGN uint64_t EltFp25519_1w_x64[NUM_WORDS_ELTFP25519_X64];
typedef ALIGN uint64_t EltFp25519_1w_Buffer_x64[2 * NUM_WORDS_ELTFP25519_X64];
typedef ALIGN uint64_t EltFp25519_2w_x64[2 * NUM_WORDS_ELTFP25519_X64];
typedef ALIGN uint64_t EltFp25519_2w_Buffer_x64[4 * NUM_WORDS_ELTFP25519_X64];

#ifdef __cplusplus
extern "C" {
#endif

/* Integer Arithmetic */
void mul2_256x256_integer_x64(uint64_t *const c, uint64_t *const a,
                              uint64_t *const b);

void sqr2_256x256_integer_x64(uint64_t *const c, uint64_t *const a);

void red_EltFp25519_2w_x64(uint64_t *const c, uint64_t *const a);

void mul_256x256_integer_x64(uint64_t *const c, uint64_t *const a,
                             uint64_t *const b);

void sqr_256x256_integer_x64(uint64_t *const c, uint64_t *const a);

void red_EltFp25519_1w_x64(uint64_t *const c, uint64_t *const a);

/* Prime Field Arithmetic */
void add_EltFp25519_1w_x64(uint64_t *const c, uint64_t *const a,
                           uint64_t *const b);

void sub_EltFp25519_1w_x64(uint64_t *const c, uint64_t *const a,
                           uint64_t *const b);

void mul_a24_EltFp25519_1w_x64(uint64_t *const c, uint64_t *const a);

void inv_EltFp25519_1w_x64(uint64_t *const c, uint64_t *const a);

void fred_EltFp25519_1w_x64(uint64_t *const c);

#ifdef __cplusplus
}
#endif

#define mul_EltFp25519_1w_x64(c, a, b)      \
  mul_256x256_integer_x64(buffer_1w, a, b); \
  red_EltFp25519_1w_x64(c, buffer_1w);

#define sqr_EltFp25519_1w_x64(a)         \
  sqr_256x256_integer_x64(buffer_1w, a); \
  red_EltFp25519_1w_x64(a, buffer_1w);

#define mul_EltFp25519_2w_x64(c, a, b)       \
  mul2_256x256_integer_x64(buffer_2w, a, b); \
  red_EltFp25519_2w_x64(c, buffer_2w);

#define sqr_EltFp25519_2w_x64(a)          \
  sqr2_256x256_integer_x64(buffer_2w, a); \
  red_EltFp25519_2w_x64(a, buffer_2w);

#define copy_EltFp25519_1w_x64(C, A) \
  (C)[0] = (A)[0];                   \
  (C)[1] = (A)[1];                   \
  (C)[2] = (A)[2];                   \
  (C)[3] = (A)[3];

#define setzero_EltFp25519_1w_x64(C) \
  (C)[0] = 0;                        \
  (C)[1] = 0;                        \
  (C)[2] = 0;                        \
  (C)[3] = 0;

#endif /* FP25519_X64_H */
