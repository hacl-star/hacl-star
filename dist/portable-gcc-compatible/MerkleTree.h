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

#ifndef __MerkleTree_H
#define __MerkleTree_H

#include "Hacl_Kremlib.h"
#include "EverCrypt_Hash.h"


/* SNIPPET_START: hash_size */

extern uint32_t hash_size;

/* SNIPPET_END: hash_size */

/* SNIPPET_START: hash */

typedef uint8_t *hash;

/* SNIPPET_END: hash */

/* SNIPPET_START: hash_r_free */

void hash_r_free(uint8_t *v1);

/* SNIPPET_END: hash_r_free */

/* SNIPPET_START: hash_copy */

void hash_copy(uint8_t *src, uint8_t *dst);

/* SNIPPET_END: hash_copy */

/* SNIPPET_START: LowStar_Vector_vector_str___uint8_t_ */

typedef struct LowStar_Vector_vector_str___uint8_t__s
{
  uint32_t sz;
  uint32_t cap;
  uint8_t **vs;
}
LowStar_Vector_vector_str___uint8_t_;

/* SNIPPET_END: LowStar_Vector_vector_str___uint8_t_ */

/* SNIPPET_START: hash_vec */

typedef LowStar_Vector_vector_str___uint8_t_ hash_vec;

/* SNIPPET_END: hash_vec */

/* SNIPPET_START: hash_vec_r_free */

void hash_vec_r_free(LowStar_Vector_vector_str___uint8_t_ v1);

/* SNIPPET_END: hash_vec_r_free */

/* SNIPPET_START: LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ */

typedef struct LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t__s
{
  uint32_t sz;
  uint32_t cap;
  LowStar_Vector_vector_str___uint8_t_ *vs;
}
LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_;

/* SNIPPET_END: LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ */

/* SNIPPET_START: hash_vv */

typedef LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hash_vv;

/* SNIPPET_END: hash_vv */

/* SNIPPET_START: init_hash */

extern uint8_t *(*init_hash)();

/* SNIPPET_END: init_hash */

/* SNIPPET_START: free_hash */

extern void (*free_hash)(uint8_t *x0);

/* SNIPPET_END: free_hash */

/* SNIPPET_START: hash_fun_t */

typedef void (*hash_fun_t)(uint8_t *x0, uint8_t *x1, uint8_t *x2);

/* SNIPPET_END: hash_fun_t */

/* SNIPPET_START: hash_2 */

void hash_2(uint8_t *src1, uint8_t *src2, uint8_t *dst);

/* SNIPPET_END: hash_2 */

/* SNIPPET_START: index_t */

typedef uint32_t index_t;

/* SNIPPET_END: index_t */

/* SNIPPET_START: uint32_32_max */

extern uint32_t uint32_32_max;

/* SNIPPET_END: uint32_32_max */

/* SNIPPET_START: uint32_max */

extern uint64_t uint32_max;

/* SNIPPET_END: uint32_max */

/* SNIPPET_START: uint64_max */

extern uint64_t uint64_max;

/* SNIPPET_END: uint64_max */

/* SNIPPET_START: offset_range_limit */

extern uint64_t offset_range_limit;

/* SNIPPET_END: offset_range_limit */

/* SNIPPET_START: offset_t */

typedef uint64_t offset_t;

/* SNIPPET_END: offset_t */

/* SNIPPET_START: merkle_tree_size_lg */

extern uint32_t merkle_tree_size_lg;

/* SNIPPET_END: merkle_tree_size_lg */

/* SNIPPET_START: merkle_tree */

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

/* SNIPPET_END: merkle_tree */

/* SNIPPET_START: uu___is_MT */

bool uu___is_MT(merkle_tree projectee);

/* SNIPPET_END: uu___is_MT */

/* SNIPPET_START: __proj__MT__item__offset */

uint64_t __proj__MT__item__offset(merkle_tree projectee);

/* SNIPPET_END: __proj__MT__item__offset */

/* SNIPPET_START: __proj__MT__item__i */

uint32_t __proj__MT__item__i(merkle_tree projectee);

/* SNIPPET_END: __proj__MT__item__i */

/* SNIPPET_START: __proj__MT__item__j */

uint32_t __proj__MT__item__j(merkle_tree projectee);

/* SNIPPET_END: __proj__MT__item__j */

/* SNIPPET_START: __proj__MT__item__hs */

LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
__proj__MT__item__hs(merkle_tree projectee);

/* SNIPPET_END: __proj__MT__item__hs */

/* SNIPPET_START: __proj__MT__item__rhs_ok */

bool __proj__MT__item__rhs_ok(merkle_tree projectee);

/* SNIPPET_END: __proj__MT__item__rhs_ok */

/* SNIPPET_START: __proj__MT__item__rhs */

LowStar_Vector_vector_str___uint8_t_ __proj__MT__item__rhs(merkle_tree projectee);

/* SNIPPET_END: __proj__MT__item__rhs */

/* SNIPPET_START: __proj__MT__item__mroot */

uint8_t *__proj__MT__item__mroot(merkle_tree projectee);

/* SNIPPET_END: __proj__MT__item__mroot */

/* SNIPPET_START: __proj__MT__item__hash_fun */

void
(*__proj__MT__item__hash_fun(merkle_tree projectee))(uint8_t *x0, uint8_t *x1, uint8_t *x2);

/* SNIPPET_END: __proj__MT__item__hash_fun */

/* SNIPPET_START: mt_p */

typedef merkle_tree *mt_p;

/* SNIPPET_END: mt_p */

/* SNIPPET_START: const_mt_p */

typedef const merkle_tree *const_mt_p;

/* SNIPPET_END: const_mt_p */

/* SNIPPET_START: merkle_tree_conditions */

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

/* SNIPPET_END: merkle_tree_conditions */

/* SNIPPET_START: offset_of */

uint32_t offset_of(uint32_t i1);

/* SNIPPET_END: offset_of */

/* SNIPPET_START: mt_free */

void mt_free(merkle_tree *mt);

/* SNIPPET_END: mt_free */

/* SNIPPET_START: mt_insert_pre */

bool mt_insert_pre(const merkle_tree *mt, uint8_t *v1);

/* SNIPPET_END: mt_insert_pre */

/* SNIPPET_START: mt_insert */

void mt_insert(merkle_tree *mt, uint8_t *v1);

/* SNIPPET_END: mt_insert */

/* SNIPPET_START: mt_create_custom */

merkle_tree
*mt_create_custom(uint8_t *init1, void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2));

/* SNIPPET_END: mt_create_custom */

/* SNIPPET_START: mt_create */

merkle_tree *mt_create(uint8_t *init1);

/* SNIPPET_END: mt_create */

/* SNIPPET_START: path */

typedef LowStar_Vector_vector_str___uint8_t_ path;

/* SNIPPET_END: path */

/* SNIPPET_START: path_p */

typedef LowStar_Vector_vector_str___uint8_t_ *path_p;

/* SNIPPET_END: path_p */

/* SNIPPET_START: const_path_p */

typedef const LowStar_Vector_vector_str___uint8_t_ *const_path_p;

/* SNIPPET_END: const_path_p */

/* SNIPPET_START: init_path */

LowStar_Vector_vector_str___uint8_t_ *init_path();

/* SNIPPET_END: init_path */

/* SNIPPET_START: clear_path */

void clear_path(LowStar_Vector_vector_str___uint8_t_ *p1);

/* SNIPPET_END: clear_path */

/* SNIPPET_START: free_path */

void free_path(LowStar_Vector_vector_str___uint8_t_ *p1);

/* SNIPPET_END: free_path */

/* SNIPPET_START: mt_get_root_pre */

bool mt_get_root_pre(const merkle_tree *mt, uint8_t *rt);

/* SNIPPET_END: mt_get_root_pre */

/* SNIPPET_START: mt_get_root */

void mt_get_root(const merkle_tree *mt, uint8_t *rt);

/* SNIPPET_END: mt_get_root */

/* SNIPPET_START: path_insert */

void path_insert(LowStar_Vector_vector_str___uint8_t_ *p1, uint8_t *hp);

/* SNIPPET_END: path_insert */

/* SNIPPET_START: mt_get_path_pre */

bool
mt_get_path_pre(
  const merkle_tree *mt,
  uint64_t idx,
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *root
);

/* SNIPPET_END: mt_get_path_pre */

/* SNIPPET_START: mt_get_path */

uint32_t
mt_get_path(
  const merkle_tree *mt,
  uint64_t idx,
  LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *root
);

/* SNIPPET_END: mt_get_path */

/* SNIPPET_START: mt_flush_to_pre */

bool mt_flush_to_pre(const merkle_tree *mt, uint64_t idx);

/* SNIPPET_END: mt_flush_to_pre */

/* SNIPPET_START: mt_flush_to */

void mt_flush_to(merkle_tree *mt, uint64_t idx);

/* SNIPPET_END: mt_flush_to */

/* SNIPPET_START: mt_flush_pre */

bool mt_flush_pre(const merkle_tree *mt);

/* SNIPPET_END: mt_flush_pre */

/* SNIPPET_START: mt_flush */

void mt_flush(merkle_tree *mt);

/* SNIPPET_END: mt_flush */

/* SNIPPET_START: mt_retract_to_pre */

bool mt_retract_to_pre(const merkle_tree *mt, uint64_t r);

/* SNIPPET_END: mt_retract_to_pre */

/* SNIPPET_START: mt_retract_to */

void mt_retract_to(merkle_tree *mt, uint64_t r);

/* SNIPPET_END: mt_retract_to */

/* SNIPPET_START: mt_verify_pre */

bool
mt_verify_pre(
  const merkle_tree *mt,
  uint64_t k1,
  uint64_t j1,
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *rt
);

/* SNIPPET_END: mt_verify_pre */

/* SNIPPET_START: mt_verify */

bool
mt_verify(
  const merkle_tree *mt,
  uint64_t k1,
  uint64_t j1,
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *rt
);

/* SNIPPET_END: mt_verify */

/* SNIPPET_START: uint8_t */

typedef uint8_t uint8_t;

/* SNIPPET_END: uint8_t */

/* SNIPPET_START: uint16_t */

typedef uint16_t uint16_t;

/* SNIPPET_END: uint16_t */

/* SNIPPET_START: uint32_t */

typedef uint32_t uint32_t;

/* SNIPPET_END: uint32_t */

/* SNIPPET_START: uint64_t */

typedef uint64_t uint64_t;

/* SNIPPET_END: uint64_t */

/* SNIPPET_START: uint8_p */

typedef uint8_t *uint8_p;

/* SNIPPET_END: uint8_p */

/* SNIPPET_START: const_uint8_p */

typedef const uint8_t *const_uint8_p;

/* SNIPPET_END: const_uint8_p */

/* SNIPPET_START: mt_serialize_size */

uint64_t mt_serialize_size(const merkle_tree *mt);

/* SNIPPET_END: mt_serialize_size */

/* SNIPPET_START: mt_serialize */

uint64_t mt_serialize(const merkle_tree *mt, uint8_t *output, uint64_t sz);

/* SNIPPET_END: mt_serialize */

/* SNIPPET_START: mt_deserialize */

merkle_tree *mt_deserialize(const uint8_t *input, uint64_t sz);

/* SNIPPET_END: mt_deserialize */

/* SNIPPET_START: mt_serialize_path */

uint64_t
mt_serialize_path(
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  const merkle_tree *mt,
  uint8_t *output,
  uint64_t sz
);

/* SNIPPET_END: mt_serialize_path */

/* SNIPPET_START: mt_deserialize_path */

LowStar_Vector_vector_str___uint8_t_ *mt_deserialize_path(const uint8_t *input, uint64_t sz);

/* SNIPPET_END: mt_deserialize_path */

#define __MerkleTree_H_DEFINED
#endif
