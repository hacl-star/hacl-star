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

#ifndef __MerkleTree_New_Low_Serialization_H
#define __MerkleTree_New_Low_Serialization_H

#include "Hacl_Kremlib.h"
#include "MerkleTree_New_Low.h"
#include "MerkleTree_New_Low_Datastructures.h"
#include "MerkleTree_New_Low_Hashfunctions.h"


typedef uint8_t uint8_t;

typedef uint16_t uint16_t;

typedef uint32_t uint32_t;

typedef uint64_t uint64_t;

typedef uint8_t *uint8_p;

typedef const uint8_t *const_uint8_p;

uint64_t mt_serialize_size(const merkle_tree *mt);

uint64_t mt_serialize(const merkle_tree *mt, uint8_t *output, uint64_t sz);

merkle_tree
*mt_deserialize(
  uint32_t hash_size,
  const uint8_t *input,
  uint64_t sz,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
);

uint64_t
mt_serialize_path(
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  const merkle_tree *mt,
  uint8_t *output,
  uint64_t sz
);

LowStar_Vector_vector_str___uint8_t_
*mt_deserialize_path(uint32_t hsz, const uint8_t *input, uint64_t sz);

#define __MerkleTree_New_Low_Serialization_H_DEFINED
#endif
