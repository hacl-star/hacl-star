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


#include "MerkleTree_Low_Datastructures.h"

uint8_t *MerkleTree_Low_Datastructures_hash_dummy(uint32_t uu____22)
{
  return NULL;
}

uint8_t *MerkleTree_Low_Datastructures_hash_r_alloc(uint32_t s)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), s);
  uint8_t *buf = KRML_HOST_CALLOC(s, sizeof (uint8_t));
  return buf;
}

void MerkleTree_Low_Datastructures_hash_r_free(uint8_t *v1)
{
  KRML_HOST_FREE(v1);
}

void MerkleTree_Low_Datastructures_hash_copy(uint32_t s, uint8_t *src, uint8_t *dst)
{
  memcpy(dst, src, s * sizeof (src[0U]));
}

#define Cpy 0

typedef uint8_t copyable__uint32_t__uint8_t__tags;

typedef void (*copyable__uint32_t__uint8_t_)(uint32_t x0, uint8_t *x1, uint8_t *x2);

void (*MerkleTree_Low_Datastructures_hcpy(uint32_t hsz))(uint32_t x0, uint8_t *x1, uint8_t *x2)
{
  return MerkleTree_Low_Datastructures_hash_copy;
}

LowStar_Vector_vector_str___uint8_t_ MerkleTree_Low_Datastructures_hash_vec_dummy()
{
  return
    ((LowStar_Vector_vector_str___uint8_t_){ .sz = (uint32_t)0U, .cap = (uint32_t)0U, .vs = NULL });
}

static LowStar_Vector_vector_str___uint8_t_ alloc_reserve___uint8_t_(uint32_t len, uint8_t *ia)
{
  KRML_CHECK_SIZE(sizeof (uint8_t *), len);
  uint8_t **buf = KRML_HOST_MALLOC(sizeof (uint8_t *) * len);
  for (uint32_t _i = 0U; _i < len; ++_i)
    buf[_i] = ia;
  return ((LowStar_Vector_vector_str___uint8_t_){ .sz = (uint32_t)0U, .cap = len, .vs = buf });
}

LowStar_Vector_vector_str___uint8_t_
MerkleTree_Low_Datastructures_hash_vec_r_alloc(uint32_t hsz)
{
  return alloc_reserve___uint8_t_((uint32_t)1U, MerkleTree_Low_Datastructures_hash_dummy(hsz));
}

void LowStar_Vector_free___uint8_t_(LowStar_Vector_vector_str___uint8_t_ vec)
{
  KRML_HOST_FREE(vec.vs);
}

void MerkleTree_Low_Datastructures_hash_vec_r_free(LowStar_Vector_vector_str___uint8_t_ v1)
{
  LowStar_Vector_free___uint8_t_(v1);
}

