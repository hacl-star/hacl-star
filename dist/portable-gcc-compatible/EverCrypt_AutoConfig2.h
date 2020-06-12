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

#ifndef __EverCrypt_AutoConfig2_H
#define __EverCrypt_AutoConfig2_H

#include "Vale.h"


/* SNIPPET_START: EverCrypt_AutoConfig2_has_shaext */

bool EverCrypt_AutoConfig2_has_shaext();

/* SNIPPET_END: EverCrypt_AutoConfig2_has_shaext */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_aesni */

bool EverCrypt_AutoConfig2_has_aesni();

/* SNIPPET_END: EverCrypt_AutoConfig2_has_aesni */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_pclmulqdq */

bool EverCrypt_AutoConfig2_has_pclmulqdq();

/* SNIPPET_END: EverCrypt_AutoConfig2_has_pclmulqdq */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_avx2 */

bool EverCrypt_AutoConfig2_has_avx2();

/* SNIPPET_END: EverCrypt_AutoConfig2_has_avx2 */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_avx */

bool EverCrypt_AutoConfig2_has_avx();

/* SNIPPET_END: EverCrypt_AutoConfig2_has_avx */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_bmi2 */

bool EverCrypt_AutoConfig2_has_bmi2();

/* SNIPPET_END: EverCrypt_AutoConfig2_has_bmi2 */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_adx */

bool EverCrypt_AutoConfig2_has_adx();

/* SNIPPET_END: EverCrypt_AutoConfig2_has_adx */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_sse */

bool EverCrypt_AutoConfig2_has_sse();

/* SNIPPET_END: EverCrypt_AutoConfig2_has_sse */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_movbe */

bool EverCrypt_AutoConfig2_has_movbe();

/* SNIPPET_END: EverCrypt_AutoConfig2_has_movbe */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_rdrand */

bool EverCrypt_AutoConfig2_has_rdrand();

/* SNIPPET_END: EverCrypt_AutoConfig2_has_rdrand */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_avx512 */

bool EverCrypt_AutoConfig2_has_avx512();

/* SNIPPET_END: EverCrypt_AutoConfig2_has_avx512 */

/* SNIPPET_START: EverCrypt_AutoConfig2_wants_vale */

bool EverCrypt_AutoConfig2_wants_vale();

/* SNIPPET_END: EverCrypt_AutoConfig2_wants_vale */

/* SNIPPET_START: EverCrypt_AutoConfig2_wants_hacl */

bool EverCrypt_AutoConfig2_wants_hacl();

/* SNIPPET_END: EverCrypt_AutoConfig2_wants_hacl */

/* SNIPPET_START: EverCrypt_AutoConfig2_wants_openssl */

bool EverCrypt_AutoConfig2_wants_openssl();

/* SNIPPET_END: EverCrypt_AutoConfig2_wants_openssl */

/* SNIPPET_START: EverCrypt_AutoConfig2_wants_bcrypt */

bool EverCrypt_AutoConfig2_wants_bcrypt();

/* SNIPPET_END: EverCrypt_AutoConfig2_wants_bcrypt */

/* SNIPPET_START: EverCrypt_AutoConfig2_recall */

void EverCrypt_AutoConfig2_recall();

/* SNIPPET_END: EverCrypt_AutoConfig2_recall */

/* SNIPPET_START: EverCrypt_AutoConfig2_init */

void EverCrypt_AutoConfig2_init();

/* SNIPPET_END: EverCrypt_AutoConfig2_init */

/* SNIPPET_START: EverCrypt_AutoConfig2_disabler */

typedef void (*EverCrypt_AutoConfig2_disabler)();

/* SNIPPET_END: EverCrypt_AutoConfig2_disabler */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_avx2 */

void EverCrypt_AutoConfig2_disable_avx2();

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_avx2 */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_avx */

void EverCrypt_AutoConfig2_disable_avx();

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_avx */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_bmi2 */

void EverCrypt_AutoConfig2_disable_bmi2();

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_bmi2 */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_adx */

void EverCrypt_AutoConfig2_disable_adx();

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_adx */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_shaext */

void EverCrypt_AutoConfig2_disable_shaext();

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_shaext */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_aesni */

void EverCrypt_AutoConfig2_disable_aesni();

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_aesni */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_pclmulqdq */

void EverCrypt_AutoConfig2_disable_pclmulqdq();

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_pclmulqdq */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_sse */

void EverCrypt_AutoConfig2_disable_sse();

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_sse */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_movbe */

void EverCrypt_AutoConfig2_disable_movbe();

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_movbe */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_rdrand */

void EverCrypt_AutoConfig2_disable_rdrand();

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_rdrand */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_avx512 */

void EverCrypt_AutoConfig2_disable_avx512();

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_avx512 */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_vale */

void EverCrypt_AutoConfig2_disable_vale();

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_vale */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_hacl */

void EverCrypt_AutoConfig2_disable_hacl();

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_hacl */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_openssl */

void EverCrypt_AutoConfig2_disable_openssl();

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_openssl */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_bcrypt */

void EverCrypt_AutoConfig2_disable_bcrypt();

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_bcrypt */

#define __EverCrypt_AutoConfig2_H_DEFINED
#endif
