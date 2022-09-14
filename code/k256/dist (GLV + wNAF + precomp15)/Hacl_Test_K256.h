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


#ifndef __Hacl_Test_K256_H
#define __Hacl_Test_K256_H
#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"


#include "Lib_PrintBuffer.h"
#include "Hacl_Krmllib.h"
#include "Hacl_K256_ECDSA.h"
#include "lib_intrinsics.h"
extern const uint8_t pk1[64U];

extern const uint8_t msg1[6U];

extern const uint8_t sgnt1[64U];

extern const uint8_t sk2[32U];

extern const uint8_t pk2[64U];

extern const uint8_t nonce2[32U];

extern const uint8_t msgHash2[32U];

extern const uint8_t sgnt2[64U];

void test_verify();

void test_sign_and_verify();

void test_public_key_compressed();

void test_public_key_uncompressed();

exit_code main();


#define __Hacl_Test_K256_H_DEFINED
#endif
