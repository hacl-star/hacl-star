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


#ifndef __internal_Vale_H
#define __internal_Vale_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"




/* SNIPPET_START: add_scalar_e */

extern uint64_t add_scalar_e(uint64_t *x0, uint64_t *x1, uint64_t x2);

/* SNIPPET_END: add_scalar_e */

/* SNIPPET_START: fadd_e */

extern uint64_t fadd_e(uint64_t *x0, uint64_t *x1, uint64_t *x2);

/* SNIPPET_END: fadd_e */

/* SNIPPET_START: sha256_update */

extern uint64_t sha256_update(uint32_t *x0, uint8_t *x1, uint64_t x2, uint32_t *x3);

/* SNIPPET_END: sha256_update */

/* SNIPPET_START: x64_poly1305 */

extern uint64_t x64_poly1305(uint8_t *x0, uint8_t *x1, uint64_t x2, uint64_t x3);

/* SNIPPET_END: x64_poly1305 */

/* SNIPPET_START: check_aesni */

extern uint64_t check_aesni();

/* SNIPPET_END: check_aesni */

/* SNIPPET_START: check_sha */

extern uint64_t check_sha();

/* SNIPPET_END: check_sha */

/* SNIPPET_START: check_adx_bmi2 */

extern uint64_t check_adx_bmi2();

/* SNIPPET_END: check_adx_bmi2 */

/* SNIPPET_START: check_avx */

extern uint64_t check_avx();

/* SNIPPET_END: check_avx */

/* SNIPPET_START: check_avx2 */

extern uint64_t check_avx2();

/* SNIPPET_END: check_avx2 */

/* SNIPPET_START: check_movbe */

extern uint64_t check_movbe();

/* SNIPPET_END: check_movbe */

/* SNIPPET_START: check_sse */

extern uint64_t check_sse();

/* SNIPPET_END: check_sse */

/* SNIPPET_START: check_rdrand */

extern uint64_t check_rdrand();

/* SNIPPET_END: check_rdrand */

/* SNIPPET_START: check_avx512 */

extern uint64_t check_avx512();

/* SNIPPET_END: check_avx512 */

/* SNIPPET_START: check_osxsave */

extern uint64_t check_osxsave();

/* SNIPPET_END: check_osxsave */

/* SNIPPET_START: check_avx_xcr0 */

extern uint64_t check_avx_xcr0();

/* SNIPPET_END: check_avx_xcr0 */

/* SNIPPET_START: check_avx512_xcr0 */

extern uint64_t check_avx512_xcr0();

/* SNIPPET_END: check_avx512_xcr0 */

/* SNIPPET_START: gcm128_decrypt_opt */

extern uint64_t
gcm128_decrypt_opt(
  uint8_t *x0,
  uint64_t x1,
  uint64_t x2,
  uint8_t *x3,
  uint8_t *x4,
  uint8_t *x5,
  uint8_t *x6,
  uint8_t *x7,
  uint8_t *x8,
  uint64_t x9,
  uint8_t *x10,
  uint8_t *x11,
  uint64_t x12,
  uint8_t *x13,
  uint64_t x14,
  uint8_t *x15,
  uint8_t *x16
);

/* SNIPPET_END: gcm128_decrypt_opt */

/* SNIPPET_START: gcm256_decrypt_opt */

extern uint64_t
gcm256_decrypt_opt(
  uint8_t *x0,
  uint64_t x1,
  uint64_t x2,
  uint8_t *x3,
  uint8_t *x4,
  uint8_t *x5,
  uint8_t *x6,
  uint8_t *x7,
  uint8_t *x8,
  uint64_t x9,
  uint8_t *x10,
  uint8_t *x11,
  uint64_t x12,
  uint8_t *x13,
  uint64_t x14,
  uint8_t *x15,
  uint8_t *x16
);

/* SNIPPET_END: gcm256_decrypt_opt */

/* SNIPPET_START: aes128_key_expansion */

extern uint64_t aes128_key_expansion(uint8_t *x0, uint8_t *x1);

/* SNIPPET_END: aes128_key_expansion */

/* SNIPPET_START: aes256_key_expansion */

extern uint64_t aes256_key_expansion(uint8_t *x0, uint8_t *x1);

/* SNIPPET_END: aes256_key_expansion */

/* SNIPPET_START: compute_iv_stdcall */

extern uint64_t
compute_iv_stdcall(
  uint8_t *x0,
  uint64_t x1,
  uint64_t x2,
  uint8_t *x3,
  uint8_t *x4,
  uint8_t *x5
);

/* SNIPPET_END: compute_iv_stdcall */

/* SNIPPET_START: gcm128_encrypt_opt */

extern uint64_t
gcm128_encrypt_opt(
  uint8_t *x0,
  uint64_t x1,
  uint64_t x2,
  uint8_t *x3,
  uint8_t *x4,
  uint8_t *x5,
  uint8_t *x6,
  uint8_t *x7,
  uint8_t *x8,
  uint64_t x9,
  uint8_t *x10,
  uint8_t *x11,
  uint64_t x12,
  uint8_t *x13,
  uint64_t x14,
  uint8_t *x15,
  uint8_t *x16
);

/* SNIPPET_END: gcm128_encrypt_opt */

/* SNIPPET_START: gcm256_encrypt_opt */

extern uint64_t
gcm256_encrypt_opt(
  uint8_t *x0,
  uint64_t x1,
  uint64_t x2,
  uint8_t *x3,
  uint8_t *x4,
  uint8_t *x5,
  uint8_t *x6,
  uint8_t *x7,
  uint8_t *x8,
  uint64_t x9,
  uint8_t *x10,
  uint8_t *x11,
  uint64_t x12,
  uint8_t *x13,
  uint64_t x14,
  uint8_t *x15,
  uint8_t *x16
);

/* SNIPPET_END: gcm256_encrypt_opt */

/* SNIPPET_START: aes128_keyhash_init */

extern uint64_t aes128_keyhash_init(uint8_t *x0, uint8_t *x1);

/* SNIPPET_END: aes128_keyhash_init */

/* SNIPPET_START: aes256_keyhash_init */

extern uint64_t aes256_keyhash_init(uint8_t *x0, uint8_t *x1);

/* SNIPPET_END: aes256_keyhash_init */

/* SNIPPET_START: cswap2_e */

extern uint64_t cswap2_e(uint64_t x0, uint64_t *x1, uint64_t *x2);

/* SNIPPET_END: cswap2_e */

/* SNIPPET_START: fsqr_e */

extern uint64_t fsqr_e(uint64_t *x0, uint64_t *x1, uint64_t *x2);

/* SNIPPET_END: fsqr_e */

/* SNIPPET_START: fsqr2_e */

extern uint64_t fsqr2_e(uint64_t *x0, uint64_t *x1, uint64_t *x2);

/* SNIPPET_END: fsqr2_e */

/* SNIPPET_START: fmul_e */

extern uint64_t fmul_e(uint64_t *x0, uint64_t *x1, uint64_t *x2, uint64_t *x3);

/* SNIPPET_END: fmul_e */

/* SNIPPET_START: fmul2_e */

extern uint64_t fmul2_e(uint64_t *x0, uint64_t *x1, uint64_t *x2, uint64_t *x3);

/* SNIPPET_END: fmul2_e */

/* SNIPPET_START: fmul_scalar_e */

extern uint64_t fmul_scalar_e(uint64_t *x0, uint64_t *x1, uint64_t x2);

/* SNIPPET_END: fmul_scalar_e */

/* SNIPPET_START: fsub_e */

extern uint64_t fsub_e(uint64_t *x0, uint64_t *x1, uint64_t *x2);

/* SNIPPET_END: fsub_e */

#if defined(__cplusplus)
}
#endif

#define __internal_Vale_H_DEFINED
#endif
