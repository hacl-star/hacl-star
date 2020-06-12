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

#ifndef __Vale_H
#define __Vale_H




extern uint64_t add_scalar_e(uint64_t *x0, uint64_t *x1, uint64_t x2);

extern uint64_t fadd_e(uint64_t *x0, uint64_t *x1, uint64_t *x2);

extern uint64_t sha256_update(uint32_t *x0, uint8_t *x1, uint64_t x2, uint32_t *x3);

extern uint64_t x64_poly1305(uint8_t *x0, uint8_t *x1, uint64_t x2, uint64_t x3);

extern uint64_t check_aesni();

extern uint64_t check_sha();

extern uint64_t check_adx_bmi2();

extern uint64_t check_avx();

extern uint64_t check_avx2();

extern uint64_t check_movbe();

extern uint64_t check_sse();

extern uint64_t check_rdrand();

extern uint64_t cswap2_e(uint64_t x0, uint64_t *x1, uint64_t *x2);

extern uint64_t fsqr_e(uint64_t *x0, uint64_t *x1, uint64_t *x2);

extern uint64_t fsqr2_e(uint64_t *x0, uint64_t *x1, uint64_t *x2);

extern uint64_t fmul_e(uint64_t *x0, uint64_t *x1, uint64_t *x2, uint64_t *x3);

extern uint64_t fmul2_e(uint64_t *x0, uint64_t *x1, uint64_t *x2, uint64_t *x3);

extern uint64_t fmul_scalar_e(uint64_t *x0, uint64_t *x1, uint64_t x2);

extern uint64_t fsub_e(uint64_t *x0, uint64_t *x1, uint64_t *x2);

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

extern uint64_t aes128_key_expansion(uint8_t *x0, uint8_t *x1);

extern uint64_t aes256_key_expansion(uint8_t *x0, uint8_t *x1);

extern uint64_t
compute_iv_stdcall(
  uint8_t *x0,
  uint64_t x1,
  uint64_t x2,
  uint8_t *x3,
  uint8_t *x4,
  uint8_t *x5
);

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

extern uint64_t aes128_keyhash_init(uint8_t *x0, uint8_t *x1);

extern uint64_t aes256_keyhash_init(uint8_t *x0, uint8_t *x1);

extern uint64_t
gctr128_bytes(
  uint8_t *x0,
  uint64_t x1,
  uint8_t *x2,
  uint8_t *x3,
  uint8_t *x4,
  uint8_t *x5,
  uint64_t x6
);

extern uint64_t
gctr256_bytes(
  uint8_t *x0,
  uint64_t x1,
  uint8_t *x2,
  uint8_t *x3,
  uint8_t *x4,
  uint8_t *x5,
  uint64_t x6
);

#define __Vale_H_DEFINED
#endif
