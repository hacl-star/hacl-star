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

#ifndef __MerkleTree_H
#define __MerkleTree_H

#include "Hacl_Kremlib.h"
#include "EverCrypt_Hash.h"


extern uint32_t hash_size;

typedef uint8_t *hash;

void hash_r_free(uint8_t *v1);

void hash_copy(uint8_t *src, uint8_t *dst);

typedef struct LowStar_Vector_vector_str___uint8_t__s
{
  uint32_t sz;
  uint32_t cap;
  uint8_t **vs;
}
LowStar_Vector_vector_str___uint8_t_;

typedef LowStar_Vector_vector_str___uint8_t_ hash_vec;

void hash_vec_r_free(LowStar_Vector_vector_str___uint8_t_ v1);

typedef struct LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t__s
{
  uint32_t sz;
  uint32_t cap;
  LowStar_Vector_vector_str___uint8_t_ *vs;
}
LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_;

typedef LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hash_vv;

extern uint8_t *(*init_hash)();

extern void (*free_hash)(uint8_t *x0);

typedef void (*hash_fun_t)(uint8_t *x0, uint8_t *x1, uint8_t *x2);

void hash_2(uint8_t *src1, uint8_t *src2, uint8_t *dst);

typedef uint32_t index_t;

extern uint32_t uint32_32_max;

extern uint64_t uint32_max;

extern uint64_t uint64_max;

extern uint64_t offset_range_limit;

typedef uint64_t offset_t;

extern uint32_t merkle_tree_size_lg;

typedef struct merkle_tree_s
{
  uint64_t offset;
  uint32_t i;
  uint32_t j;
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs;
  bool rhs_ok;
  LowStar_Vector_vector_str___uint8_t_ rhs;
  uint8_t *mroot;
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2);
}
merkle_tree;

bool uu___is_MT(merkle_tree projectee);

uint64_t __proj__MT__item__offset(merkle_tree projectee);

uint32_t __proj__MT__item__i(merkle_tree projectee);

uint32_t __proj__MT__item__j(merkle_tree projectee);

LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
__proj__MT__item__hs(merkle_tree projectee);

bool __proj__MT__item__rhs_ok(merkle_tree projectee);

LowStar_Vector_vector_str___uint8_t_ __proj__MT__item__rhs(merkle_tree projectee);

uint8_t *__proj__MT__item__mroot(merkle_tree projectee);

void
(*__proj__MT__item__hash_fun(merkle_tree projectee))(uint8_t *x0, uint8_t *x1, uint8_t *x2);

typedef merkle_tree *mt_p;

typedef const merkle_tree *const_mt_p;

bool
merkle_tree_conditions(
  uint64_t offset1,
  uint32_t i1,
  uint32_t j1,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs,
  bool rhs_ok,
  LowStar_Vector_vector_str___uint8_t_ rhs,
  uint8_t *mroot
);

uint32_t offset_of(uint32_t i1);

void mt_free(merkle_tree *mt);

bool mt_insert_pre(const merkle_tree *mt, uint8_t *v1);

void mt_insert(merkle_tree *mt, uint8_t *v1);

merkle_tree
*mt_create_custom(uint8_t *init1, void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2));

merkle_tree *mt_create(uint8_t *init1);

typedef LowStar_Vector_vector_str___uint8_t_ path;

typedef LowStar_Vector_vector_str___uint8_t_ *path_p;

typedef const LowStar_Vector_vector_str___uint8_t_ *const_path_p;

LowStar_Vector_vector_str___uint8_t_ *init_path();

void clear_path(LowStar_Vector_vector_str___uint8_t_ *p1);

void free_path(LowStar_Vector_vector_str___uint8_t_ *p1);

bool mt_get_root_pre(const merkle_tree *mt, uint8_t *rt);

void mt_get_root(const merkle_tree *mt, uint8_t *rt);

void path_insert(LowStar_Vector_vector_str___uint8_t_ *p1, uint8_t *hp);

bool
mt_get_path_pre(
  const merkle_tree *mt,
  uint64_t idx,
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *root
);

uint32_t
mt_get_path(
  const merkle_tree *mt,
  uint64_t idx,
  LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *root
);

bool mt_flush_to_pre(const merkle_tree *mt, uint64_t idx);

void mt_flush_to(merkle_tree *mt, uint64_t idx);

bool mt_flush_pre(const merkle_tree *mt);

void mt_flush(merkle_tree *mt);

bool mt_retract_to_pre(const merkle_tree *mt, uint64_t r);

void mt_retract_to(merkle_tree *mt, uint64_t r);

bool
mt_verify_pre(
  const merkle_tree *mt,
  uint64_t k1,
  uint64_t j1,
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *rt
);

bool
mt_verify(
  const merkle_tree *mt,
  uint64_t k1,
  uint64_t j1,
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *rt
);

typedef uint8_t uint8_t;

typedef uint16_t uint16_t;

typedef uint32_t uint32_t;

typedef uint64_t uint64_t;

typedef uint8_t *uint8_p;

typedef const uint8_t *const_uint8_p;

uint64_t mt_serialize_size(const merkle_tree *mt);

uint64_t mt_serialize(const merkle_tree *mt, uint8_t *output, uint64_t sz);

merkle_tree *mt_deserialize(const uint8_t *input, uint64_t sz);

uint64_t
mt_serialize_path(
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  const merkle_tree *mt,
  uint8_t *output,
  uint64_t sz
);

LowStar_Vector_vector_str___uint8_t_ *mt_deserialize_path(const uint8_t *input, uint64_t sz);

#define __MerkleTree_H_DEFINED
#endif
