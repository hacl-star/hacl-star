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
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"

#ifndef __MerkleTree_Low_Datastructures_H
#define __MerkleTree_Low_Datastructures_H

#include "Hacl_Kremlib.h"


typedef uint32_t MerkleTree_Low_Datastructures_hash_size_t;

uint8_t *MerkleTree_Low_Datastructures_hash_dummy(uint32_t uu____22);

uint8_t *MerkleTree_Low_Datastructures_hash_r_alloc(uint32_t s);

void MerkleTree_Low_Datastructures_hash_r_free(uint32_t uu____220, uint8_t *v1);

void MerkleTree_Low_Datastructures_hash_copy(uint32_t s, uint8_t *src, uint8_t *dst);

void
(*MerkleTree_Low_Datastructures_hcpy(uint32_t hsz))(uint32_t x0, uint8_t *x1, uint8_t *x2);

typedef struct LowStar_Vector_vector_str___uint8_t__s
{
  uint32_t sz;
  uint32_t cap;
  uint8_t **vs;
}
LowStar_Vector_vector_str___uint8_t_;

typedef struct LowStar_Regional_regional__uint32_t__uint8_t__s
{
  uint32_t state;
  uint8_t *(*dummy)(uint32_t x0);
  uint8_t *(*r_alloc)(uint32_t x0);
  void (*r_free)(uint32_t x0, uint8_t *x1);
}
LowStar_Regional_regional__uint32_t__uint8_t_;

LowStar_Vector_vector_str___uint8_t_
MerkleTree_Low_Datastructures_hash_vec_dummy(
  LowStar_Regional_regional__uint32_t__uint8_t_ uu____479
);

uint8_t
*LowStar_Regional_rg_dummy___uint8_t__uint32_t(
  LowStar_Regional_regional__uint32_t__uint8_t_ rg
);

LowStar_Vector_vector_str___uint8_t_
MerkleTree_Low_Datastructures_hash_vec_r_alloc(LowStar_Regional_regional__uint32_t__uint8_t_ s);

void LowStar_Vector_free___uint8_t_(LowStar_Vector_vector_str___uint8_t_ vec);

void
MerkleTree_Low_Datastructures_hash_vec_r_free(
  LowStar_Regional_regional__uint32_t__uint8_t_ uu____717,
  LowStar_Vector_vector_str___uint8_t_ v1
);

#define __MerkleTree_Low_Datastructures_H_DEFINED
#endif
