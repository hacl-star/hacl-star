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


#ifndef __Hacl_Spec_H
#define __Hacl_Spec_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"




/* SNIPPET_START: Spec_Blake2_alg */

#define Spec_Blake2_Blake2S 0
#define Spec_Blake2_Blake2B 1

/* SNIPPET_END: Spec_Blake2_alg */

typedef uint8_t Spec_Blake2_alg;

/* SNIPPET_START: Spec_Hash_Definitions_hash_alg */

#define Spec_Hash_Definitions_SHA2_224 0
#define Spec_Hash_Definitions_SHA2_256 1
#define Spec_Hash_Definitions_SHA2_384 2
#define Spec_Hash_Definitions_SHA2_512 3
#define Spec_Hash_Definitions_SHA1 4
#define Spec_Hash_Definitions_MD5 5
#define Spec_Hash_Definitions_Blake2S 6
#define Spec_Hash_Definitions_Blake2B 7
#define Spec_Hash_Definitions_SHA3_256 8

/* SNIPPET_END: Spec_Hash_Definitions_hash_alg */

typedef uint8_t Spec_Hash_Definitions_hash_alg;

/* SNIPPET_START: Spec_FFDHE_ffdhe_alg */

#define Spec_FFDHE_FFDHE2048 0
#define Spec_FFDHE_FFDHE3072 1
#define Spec_FFDHE_FFDHE4096 2
#define Spec_FFDHE_FFDHE6144 3
#define Spec_FFDHE_FFDHE8192 4

/* SNIPPET_END: Spec_FFDHE_ffdhe_alg */

typedef uint8_t Spec_FFDHE_ffdhe_alg;

/* SNIPPET_START: Spec_Agile_AEAD_alg */

#define Spec_Agile_AEAD_AES128_GCM 0
#define Spec_Agile_AEAD_AES256_GCM 1
#define Spec_Agile_AEAD_CHACHA20_POLY1305 2
#define Spec_Agile_AEAD_AES128_CCM 3
#define Spec_Agile_AEAD_AES256_CCM 4
#define Spec_Agile_AEAD_AES128_CCM8 5
#define Spec_Agile_AEAD_AES256_CCM8 6

/* SNIPPET_END: Spec_Agile_AEAD_alg */

typedef uint8_t Spec_Agile_AEAD_alg;

/* SNIPPET_START: Spec_Frodo_Params_frodo_gen_a */

#define Spec_Frodo_Params_SHAKE128 0
#define Spec_Frodo_Params_AES128 1

/* SNIPPET_END: Spec_Frodo_Params_frodo_gen_a */

typedef uint8_t Spec_Frodo_Params_frodo_gen_a;

#if defined(__cplusplus)
}
#endif

#define __Hacl_Spec_H_DEFINED
#endif
