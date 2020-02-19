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

#ifndef __MerkleTree_New_Low_H
#define __MerkleTree_New_Low_H

#include "Hacl_Kremlib.h"
#include "MerkleTree_New_Low_Datastructures.h"
#include "MerkleTree_New_Low_Hashfunctions.h"


typedef uint32_t index_t;

extern uint32_t uint32_32_max;

extern uint64_t uint32_max;

extern uint64_t uint64_max;

extern uint64_t offset_range_limit;

typedef uint64_t offset_t;

extern uint32_t merkle_tree_size_lg;

typedef struct LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t__s
{
  uint32_t sz;
  uint32_t cap;
  LowStar_Vector_vector_str___uint8_t_ *vs;
}
LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_;

typedef struct merkle_tree_s
{
  uint32_t hash_size;
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

uint32_t __proj__MT__item__hash_size(merkle_tree projectee);

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

LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
LowStar_Vector_alloc_rid__LowStar_Vector_vector_str__uint8_t_(
  uint32_t len,
  LowStar_Vector_vector_str___uint8_t_ v1
);

typedef struct
LowStar_Regional_regional__LowStar_Regional_regional__uint32_t__uint8_t__LowStar_Vector_vector_str___uint8_t__s
{
  LowStar_Regional_regional__uint32_t__uint8_t_ state;
  LowStar_Vector_vector_str___uint8_t_
  (*dummy)(LowStar_Regional_regional__uint32_t__uint8_t_ x0);
  LowStar_Vector_vector_str___uint8_t_
  (*r_alloc)(LowStar_Regional_regional__uint32_t__uint8_t_ x0);
  void
  (*r_free)(
    LowStar_Regional_regional__uint32_t__uint8_t_ x0,
    LowStar_Vector_vector_str___uint8_t_ x1
  );
}
LowStar_Regional_regional__LowStar_Regional_regional__uint32_t__uint8_t__LowStar_Vector_vector_str___uint8_t_;

LowStar_Vector_vector_str___uint8_t_
LowStar_Regional_rg_dummy__LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_(
  LowStar_Regional_regional__LowStar_Regional_regional__uint32_t__uint8_t__LowStar_Vector_vector_str___uint8_t_
  rg
);

void
LowStar_Vector_assign__LowStar_Vector_vector_str__uint8_t_(
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ vec,
  uint32_t i1,
  LowStar_Vector_vector_str___uint8_t_ v1
);

LowStar_Vector_vector_str___uint8_t_
LowStar_Vector_alloc_rid___uint8_t_(uint32_t len, uint8_t *v1);

void
LowStar_Vector_assign___uint8_t_(
  LowStar_Vector_vector_str___uint8_t_ vec,
  uint32_t i1,
  uint8_t *v1
);

LowStar_Vector_vector_str___uint8_t_
LowStar_Vector_index__LowStar_Vector_vector_str__uint8_t_(
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ vec,
  uint32_t i1
);

uint8_t
*LowStar_Vector_index___uint8_t_(LowStar_Vector_vector_str___uint8_t_ vec, uint32_t i1);

void mt_free(merkle_tree *mt);

bool mt_insert_pre(const merkle_tree *mt, uint8_t *v1);

void mt_insert(merkle_tree *mt, uint8_t *v1);

merkle_tree
*mt_create_custom(
  uint32_t hsz,
  uint8_t *init1,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
);

merkle_tree *mt_create(uint8_t *init1);

LowStar_Vector_vector_str___uint8_t_ *init_path(uint32_t hsz);

void clear_path(uint32_t uu____3215, LowStar_Vector_vector_str___uint8_t_ *p1);

void free_path(uint32_t uu____3362, LowStar_Vector_vector_str___uint8_t_ *p1);

bool mt_get_root_pre(const merkle_tree *mt, uint8_t *rt);

void mt_get_root(const merkle_tree *mt, uint8_t *rt);

void path_insert(uint32_t hsz, LowStar_Vector_vector_str___uint8_t_ *p1, uint8_t *hp);

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

void move_left___uint8_t_(uint8_t **b, uint32_t dst, uint32_t src, uint32_t l);

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

#define __MerkleTree_New_Low_H_DEFINED
#endif
