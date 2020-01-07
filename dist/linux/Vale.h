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

#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"

#ifndef __Vale_H
#define __Vale_H




extern u64 add1(u64 *x0, u64 *x1, u64 x2);

extern u64 fadd_(u64 *x0, u64 *x1, u64 *x2);

extern u64 sha256_update(u32 *x0, u8 *x1, u64 x2, u32 *x3);

extern u64 x64_poly1305(u8 *x0, u8 *x1, u64 x2, u64 x3);

extern u64 check_aesni();

extern u64 check_sha();

extern u64 check_adx_bmi2();

extern u64 check_avx();

extern u64 check_avx2();

extern u64 check_movbe();

extern u64 check_sse();

extern u64 check_rdrand();

extern u64 cswap2(u64 x0, u64 *x1, u64 *x2);

extern u64 fsqr(u64 *x0, u64 *x1, u64 *x2);

extern u64 fsqr2(u64 *x0, u64 *x1, u64 *x2);

extern u64 fmul_(u64 *x0, u64 *x1, u64 *x2, u64 *x3);

extern u64 fmul2(u64 *x0, u64 *x1, u64 *x2, u64 *x3);

extern u64 fmul1(u64 *x0, u64 *x1, u64 x2);

extern u64 fsub_(u64 *x0, u64 *x1, u64 *x2);

extern u64
gcm128_decrypt_opt(
  u8 *x0,
  u64 x1,
  u64 x2,
  u8 *x3,
  u8 *x4,
  u8 *x5,
  u8 *x6,
  u8 *x7,
  u8 *x8,
  u64 x9,
  u8 *x10,
  u8 *x11,
  u64 x12,
  u8 *x13,
  u64 x14,
  u8 *x15,
  u8 *x16
);

extern u64
gcm256_decrypt_opt(
  u8 *x0,
  u64 x1,
  u64 x2,
  u8 *x3,
  u8 *x4,
  u8 *x5,
  u8 *x6,
  u8 *x7,
  u8 *x8,
  u64 x9,
  u8 *x10,
  u8 *x11,
  u64 x12,
  u8 *x13,
  u64 x14,
  u8 *x15,
  u8 *x16
);

extern u64 aes128_key_expansion(u8 *x0, u8 *x1);

extern u64 aes256_key_expansion(u8 *x0, u8 *x1);

extern u64 compute_iv_stdcall(u8 *x0, u64 x1, u64 x2, u8 *x3, u8 *x4, u8 *x5);

extern u64
gcm128_encrypt_opt(
  u8 *x0,
  u64 x1,
  u64 x2,
  u8 *x3,
  u8 *x4,
  u8 *x5,
  u8 *x6,
  u8 *x7,
  u8 *x8,
  u64 x9,
  u8 *x10,
  u8 *x11,
  u64 x12,
  u8 *x13,
  u64 x14,
  u8 *x15,
  u8 *x16
);

extern u64
gcm256_encrypt_opt(
  u8 *x0,
  u64 x1,
  u64 x2,
  u8 *x3,
  u8 *x4,
  u8 *x5,
  u8 *x6,
  u8 *x7,
  u8 *x8,
  u64 x9,
  u8 *x10,
  u8 *x11,
  u64 x12,
  u8 *x13,
  u64 x14,
  u8 *x15,
  u8 *x16
);

extern u64 aes128_keyhash_init(u8 *x0, u8 *x1);

extern u64 aes256_keyhash_init(u8 *x0, u8 *x1);

extern u64 gctr128_bytes(u8 *x0, u64 x1, u8 *x2, u8 *x3, u8 *x4, u8 *x5, u64 x6);

extern u64 gctr256_bytes(u8 *x0, u64 x1, u8 *x2, u8 *x3, u8 *x4, u8 *x5, u64 x6);

#define __Vale_H_DEFINED
#endif
