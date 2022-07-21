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


#ifndef __Hacl_Frodo64_H
#define __Hacl_Frodo64_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "Lib_Memzero0.h"
#include "Hacl_Spec.h"
#include "Hacl_SHA3.h"
#include "Hacl_Frodo_KEM.h"
#include "libintvector.h"
/*
 this variant is used only for testing purposes!
 */


extern u32 Hacl_Frodo64_crypto_bytes;

extern u32 Hacl_Frodo64_crypto_publickeybytes;

extern u32 Hacl_Frodo64_crypto_secretkeybytes;

extern u32 Hacl_Frodo64_crypto_ciphertextbytes;

u32 Hacl_Frodo64_crypto_kem_keypair(u8 *pk, u8 *sk);

u32 Hacl_Frodo64_crypto_kem_enc(u8 *ct, u8 *ss, u8 *pk);

u32 Hacl_Frodo64_crypto_kem_dec(u8 *ss, u8 *ct, u8 *sk);

#if defined(__cplusplus)
}
#endif

#define __Hacl_Frodo64_H_DEFINED
#endif
