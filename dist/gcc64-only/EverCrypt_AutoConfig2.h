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


#ifndef __EverCrypt_AutoConfig2_H
#define __EverCrypt_AutoConfig2_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"




bool EverCrypt_AutoConfig2_has_shaext();

bool EverCrypt_AutoConfig2_has_aesni();

bool EverCrypt_AutoConfig2_has_pclmulqdq();

bool EverCrypt_AutoConfig2_has_avx2();

bool EverCrypt_AutoConfig2_has_avx();

bool EverCrypt_AutoConfig2_has_bmi2();

bool EverCrypt_AutoConfig2_has_adx();

bool EverCrypt_AutoConfig2_has_sse();

bool EverCrypt_AutoConfig2_has_movbe();

bool EverCrypt_AutoConfig2_has_rdrand();

bool EverCrypt_AutoConfig2_has_avx512();

void EverCrypt_AutoConfig2_recall();

void EverCrypt_AutoConfig2_init();

typedef void (*EverCrypt_AutoConfig2_disabler)();

void EverCrypt_AutoConfig2_disable_avx2();

void EverCrypt_AutoConfig2_disable_avx();

void EverCrypt_AutoConfig2_disable_bmi2();

void EverCrypt_AutoConfig2_disable_adx();

void EverCrypt_AutoConfig2_disable_shaext();

void EverCrypt_AutoConfig2_disable_aesni();

void EverCrypt_AutoConfig2_disable_pclmulqdq();

void EverCrypt_AutoConfig2_disable_sse();

void EverCrypt_AutoConfig2_disable_movbe();

void EverCrypt_AutoConfig2_disable_rdrand();

void EverCrypt_AutoConfig2_disable_avx512();

bool EverCrypt_AutoConfig2_has_vec128();

bool EverCrypt_AutoConfig2_has_vec256();

#if defined(__cplusplus)
}
#endif

#define __EverCrypt_AutoConfig2_H_DEFINED
#endif
