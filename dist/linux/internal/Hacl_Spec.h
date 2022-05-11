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


#ifndef __internal_Hacl_Spec_H
#define __internal_Hacl_Spec_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "../Hacl_Spec.h"
#include "libintvector.h"
#define Spec_ECDSA_NoHash 0
#define Spec_ECDSA_Hash 1

typedef u8 Spec_ECDSA_hash_alg_ecdsa_tags;

typedef struct Spec_ECDSA_hash_alg_ecdsa_s
{
  Spec_ECDSA_hash_alg_ecdsa_tags tag;
  Spec_Hash_Definitions_hash_alg _0;
}
Spec_ECDSA_hash_alg_ecdsa;

Spec_Agile_DH_algorithm Spec_Agile_HPKE_kem_dh_of_cs(Spec_Agile_HPKE_ciphersuite cs);

Spec_Hash_Definitions_hash_alg Spec_Agile_HPKE_kem_hash_of_cs(Spec_Agile_HPKE_ciphersuite cs);

Spec_Agile_HPKE_aead Spec_Agile_HPKE_aead_of_cs(Spec_Agile_HPKE_ciphersuite cs);

Spec_Hash_Definitions_hash_alg Spec_Agile_HPKE_hash_of_cs(Spec_Agile_HPKE_ciphersuite cs);

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_Spec_H_DEFINED
#endif
