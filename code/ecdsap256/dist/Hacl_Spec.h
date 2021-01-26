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
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "wnaf.h"
#include "lib_intrinsics.h"




#define Spec_Hash_Definitions_SHA2_224 0
#define Spec_Hash_Definitions_SHA2_256 1
#define Spec_Hash_Definitions_SHA2_384 2
#define Spec_Hash_Definitions_SHA2_512 3
#define Spec_Hash_Definitions_SHA1 4
#define Spec_Hash_Definitions_MD5 5
#define Spec_Hash_Definitions_Blake2S 6
#define Spec_Hash_Definitions_Blake2B 7

typedef uint8_t Spec_Hash_Definitions_hash_alg;

#define Spec_P256_Ladder 0
#define Spec_P256_Radix4 1
#define Spec_P256_Comb 2

typedef uint8_t Spec_P256_montgomery_ladder_mode;

#define Spec_ECDSA_NoHash 0
#define Spec_ECDSA_Hash 1

typedef uint8_t Spec_ECDSA_hash_alg_ecdsa_tags;

typedef struct Spec_ECDSA_hash_alg_ecdsa_s
{
  Spec_ECDSA_hash_alg_ecdsa_tags tag;
  Spec_Hash_Definitions_hash_alg _0;
}
Spec_ECDSA_hash_alg_ecdsa;


#define __Hacl_Spec_H_DEFINED
#endif
