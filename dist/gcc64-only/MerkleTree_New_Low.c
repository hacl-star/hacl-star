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


#include "MerkleTree_New_Low.h"

uint32_t uint32_32_max = (uint32_t)4294967295U;

uint64_t uint32_max = (uint64_t)4294967295U;

uint64_t uint64_max = (uint64_t)18446744073709551615U;

uint64_t offset_range_limit = (uint64_t)4294967295U;

uint32_t merkle_tree_size_lg = (uint32_t)32U;

bool uu___is_MT(merkle_tree projectee)
{
  return true;
}

uint32_t __proj__MT__item__hash_size(merkle_tree projectee)
{
  return projectee.hash_size;
}

uint64_t __proj__MT__item__offset(merkle_tree projectee)
{
  return projectee.offset;
}

uint32_t __proj__MT__item__i(merkle_tree projectee)
{
  return projectee.i;
}

uint32_t __proj__MT__item__j(merkle_tree projectee)
{
  return projectee.j;
}

LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
__proj__MT__item__hs(merkle_tree projectee)
{
  return projectee.hs;
}

bool __proj__MT__item__rhs_ok(merkle_tree projectee)
{
  return projectee.rhs_ok;
}

LowStar_Vector_vector_str___uint8_t_ __proj__MT__item__rhs(merkle_tree projectee)
{
  return projectee.rhs;
}

uint8_t *__proj__MT__item__mroot(merkle_tree projectee)
{
  return projectee.mroot;
}

void
(*__proj__MT__item__hash_fun(merkle_tree projectee))(uint8_t *x0, uint8_t *x1, uint8_t *x2)
{
  return projectee.hash_fun;
}

bool
merkle_tree_conditions(
  uint64_t offset1,
  uint32_t i1,
  uint32_t j1,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs,
  bool rhs_ok,
  LowStar_Vector_vector_str___uint8_t_ rhs,
  uint8_t *mroot
)
{
  return
    j1
    >= i1
    && uint64_max - offset1 >= (uint64_t)j1
    && hs.sz == (uint32_t)32U
    && rhs.sz == (uint32_t)32U;
}

uint32_t offset_of(uint32_t i1)
{
  if (i1 % (uint32_t)2U == (uint32_t)0U)
  {
    return i1;
  }
  return i1 - (uint32_t)1U;
}

LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
LowStar_Vector_alloc_rid__LowStar_Vector_vector_str__uint8_t_(
  uint32_t len,
  LowStar_Vector_vector_str___uint8_t_ v1
)
{
  KRML_CHECK_SIZE(sizeof (LowStar_Vector_vector_str___uint8_t_), len);
  LowStar_Vector_vector_str___uint8_t_
  *buf = KRML_HOST_MALLOC(sizeof (LowStar_Vector_vector_str___uint8_t_) * len);
  for (uint32_t _i = 0U; _i < len; ++_i)
    buf[_i] = v1;
  return
    (
      (LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_){
        .sz = len,
        .cap = len,
        .vs = buf
      }
    );
}

LowStar_Vector_vector_str___uint8_t_
LowStar_Regional_rg_dummy__LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_(
  LowStar_Regional_regional__LowStar_Regional_regional__uint32_t__uint8_t__LowStar_Vector_vector_str___uint8_t_
  rg
)
{
  return rg.dummy(rg.state);
}

static LowStar_Vector_vector_str___uint8_t_
rg_alloc__LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_(
  LowStar_Regional_regional__LowStar_Regional_regional__uint32_t__uint8_t__LowStar_Vector_vector_str___uint8_t_
  rg
)
{
  return rg.r_alloc(rg.state);
}

void
LowStar_Vector_assign__LowStar_Vector_vector_str__uint8_t_(
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ vec,
  uint32_t i1,
  LowStar_Vector_vector_str___uint8_t_ v1
)
{
  (vec.vs + i1)[0U] = v1;
}

static void
alloc___LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_(
  LowStar_Regional_regional__LowStar_Regional_regional__uint32_t__uint8_t__LowStar_Vector_vector_str___uint8_t_
  rg,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ rv,
  uint32_t cidx
)
{
  if (!(cidx == (uint32_t)0U))
  {
    LowStar_Vector_vector_str___uint8_t_
    v1 =
      rg_alloc__LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_(rg);
    LowStar_Vector_assign__LowStar_Vector_vector_str__uint8_t_(rv, cidx - (uint32_t)1U, v1);
    alloc___LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_(rg,
      rv,
      cidx - (uint32_t)1U);
    return;
  }
}

static LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
alloc_rid__LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_(
  LowStar_Regional_regional__LowStar_Regional_regional__uint32_t__uint8_t__LowStar_Vector_vector_str___uint8_t_
  rg,
  uint32_t len
)
{
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
  vec =
    LowStar_Vector_alloc_rid__LowStar_Vector_vector_str__uint8_t_(len,
      LowStar_Regional_rg_dummy__LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_(rg));
  alloc___LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_(rg,
    vec,
    len);
  return vec;
}

LowStar_Vector_vector_str___uint8_t_
LowStar_Vector_alloc_rid___uint8_t_(uint32_t len, uint8_t *v1)
{
  KRML_CHECK_SIZE(sizeof (uint8_t *), len);
  uint8_t **buf = KRML_HOST_MALLOC(sizeof (uint8_t *) * len);
  for (uint32_t _i = 0U; _i < len; ++_i)
    buf[_i] = v1;
  return ((LowStar_Vector_vector_str___uint8_t_){ .sz = len, .cap = len, .vs = buf });
}

void
LowStar_Vector_assign___uint8_t_(
  LowStar_Vector_vector_str___uint8_t_ vec,
  uint32_t i1,
  uint8_t *v1
)
{
  (vec.vs + i1)[0U] = v1;
}

static void
alloc____uint8_t__uint32_t(
  LowStar_Regional_regional__uint32_t__uint8_t_ rg,
  LowStar_Vector_vector_str___uint8_t_ rv,
  uint32_t cidx
)
{
  if (!(cidx == (uint32_t)0U))
  {
    uint8_t *v1 = LowStar_Regional_rg_alloc___uint8_t__uint32_t(rg);
    LowStar_Vector_assign___uint8_t_(rv, cidx - (uint32_t)1U, v1);
    alloc____uint8_t__uint32_t(rg, rv, cidx - (uint32_t)1U);
    return;
  }
}

static LowStar_Vector_vector_str___uint8_t_
alloc_rid___uint8_t__uint32_t(LowStar_Regional_regional__uint32_t__uint8_t_ rg, uint32_t len)
{
  LowStar_Vector_vector_str___uint8_t_
  vec =
    LowStar_Vector_alloc_rid___uint8_t_(len,
      LowStar_Regional_rg_dummy___uint8_t__uint32_t(rg));
  alloc____uint8_t__uint32_t(rg, vec, len);
  return vec;
}

static merkle_tree
*create_empty_mt(uint32_t hsz, void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2))
{
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
  hs =
    alloc_rid__LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_((
        (LowStar_Regional_regional__LowStar_Regional_regional__uint32_t__uint8_t__LowStar_Vector_vector_str___uint8_t_){
          .state = {
            .state = hsz,
            .dummy = hash_dummy,
            .r_alloc = hash_r_alloc,
            .r_free = hash_r_free
          },
          .dummy = hash_vec_dummy,
          .r_alloc = hash_vec_r_alloc,
          .r_free = hash_vec_r_free
        }
      ),
      (uint32_t)32U);
  LowStar_Vector_vector_str___uint8_t_
  rhs =
    alloc_rid___uint8_t__uint32_t((
        (LowStar_Regional_regional__uint32_t__uint8_t_){
          .state = hsz,
          .dummy = hash_dummy,
          .r_alloc = hash_r_alloc,
          .r_free = hash_r_free
        }
      ),
      (uint32_t)32U);
  uint8_t
  *mroot =
    LowStar_Regional_rg_alloc___uint8_t__uint32_t((
        (LowStar_Regional_regional__uint32_t__uint8_t_){
          .state = hsz,
          .dummy = hash_dummy,
          .r_alloc = hash_r_alloc,
          .r_free = hash_r_free
        }
      ));
  KRML_CHECK_SIZE(sizeof (merkle_tree), (uint32_t)1U);
  merkle_tree *mt = KRML_HOST_MALLOC(sizeof (merkle_tree));
  mt[0U]
  =
    (
      (merkle_tree){
        .hash_size = hsz,
        .offset = (uint64_t)0U,
        .i = (uint32_t)0U,
        .j = (uint32_t)0U,
        .hs = hs,
        .rhs_ok = false,
        .rhs = rhs,
        .mroot = mroot,
        .hash_fun = hash_fun
      }
    );
  return mt;
}

LowStar_Vector_vector_str___uint8_t_
LowStar_Vector_index__LowStar_Vector_vector_str__uint8_t_(
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ vec,
  uint32_t i1
)
{
  return vec.vs[i1];
}

static void
rg_free__LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_(
  LowStar_Regional_regional__LowStar_Regional_regional__uint32_t__uint8_t__LowStar_Vector_vector_str___uint8_t_
  rg,
  LowStar_Vector_vector_str___uint8_t_ v1
)
{
  rg.r_free(rg.state, v1);
}

static void
free_elems__LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_(
  LowStar_Regional_regional__LowStar_Regional_regional__uint32_t__uint8_t__LowStar_Vector_vector_str___uint8_t_
  rg,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ rv,
  uint32_t idx
)
{
  rg_free__LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_(rg,
    LowStar_Vector_index__LowStar_Vector_vector_str__uint8_t_(rv, idx));
  if (idx != (uint32_t)0U)
  {
    free_elems__LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_(rg,
      rv,
      idx - (uint32_t)1U);
    return;
  }
}

static void
free__LowStar_Vector_vector_str__uint8_t_(
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ vec
)
{
  KRML_HOST_FREE(vec.vs);
}

static void
free__LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_(
  LowStar_Regional_regional__LowStar_Regional_regional__uint32_t__uint8_t__LowStar_Vector_vector_str___uint8_t_
  rg,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ rv
)
{
  if (!(rv.sz == (uint32_t)0U))
  {
    free_elems__LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_(rg,
      rv,
      rv.sz - (uint32_t)1U);
  }
  free__LowStar_Vector_vector_str__uint8_t_(rv);
}

uint8_t *LowStar_Vector_index___uint8_t_(LowStar_Vector_vector_str___uint8_t_ vec, uint32_t i1)
{
  return vec.vs[i1];
}

static void
free_elems___uint8_t__uint32_t(
  LowStar_Regional_regional__uint32_t__uint8_t_ rg,
  LowStar_Vector_vector_str___uint8_t_ rv,
  uint32_t idx
)
{
  LowStar_Regional_rg_free___uint8_t__uint32_t(rg, LowStar_Vector_index___uint8_t_(rv, idx));
  if (idx != (uint32_t)0U)
  {
    free_elems___uint8_t__uint32_t(rg, rv, idx - (uint32_t)1U);
    return;
  }
}

static void
free___uint8_t__uint32_t(
  LowStar_Regional_regional__uint32_t__uint8_t_ rg,
  LowStar_Vector_vector_str___uint8_t_ rv
)
{
  if (!(rv.sz == (uint32_t)0U))
  {
    free_elems___uint8_t__uint32_t(rg, rv, rv.sz - (uint32_t)1U);
  }
  LowStar_Vector_free___uint8_t_(rv);
}

void mt_free(merkle_tree *mt)
{
  merkle_tree mtv = *mt;
  free__LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_((
      (LowStar_Regional_regional__LowStar_Regional_regional__uint32_t__uint8_t__LowStar_Vector_vector_str___uint8_t_){
        .state = {
          .state = mtv.hash_size,
          .dummy = hash_dummy,
          .r_alloc = hash_r_alloc,
          .r_free = hash_r_free
        },
        .dummy = hash_vec_dummy,
        .r_alloc = hash_vec_r_alloc,
        .r_free = hash_vec_r_free
      }
    ),
    mtv.hs);
  free___uint8_t__uint32_t((
      (LowStar_Regional_regional__uint32_t__uint8_t_){
        .state = mtv.hash_size,
        .dummy = hash_dummy,
        .r_alloc = hash_r_alloc,
        .r_free = hash_r_free
      }
    ),
    mtv.rhs);
  LowStar_Regional_rg_free___uint8_t__uint32_t((
      (LowStar_Regional_regional__uint32_t__uint8_t_){
        .state = mtv.hash_size,
        .dummy = hash_dummy,
        .r_alloc = hash_r_alloc,
        .r_free = hash_r_free
      }
    ),
    mtv.mroot);
  KRML_HOST_FREE(mt);
}

static LowStar_Vector_vector_str___uint8_t_
insert___uint8_t_(LowStar_Vector_vector_str___uint8_t_ vec, uint8_t *v1)
{
  uint32_t sz = vec.sz;
  uint32_t cap = vec.cap;
  uint8_t **vs = vec.vs;
  if (sz == cap)
  {
    uint32_t ncap = LowStar_Vector_new_capacity(cap);
    KRML_CHECK_SIZE(sizeof (uint8_t *), ncap);
    uint8_t **nvs = KRML_HOST_MALLOC(sizeof (uint8_t *) * ncap);
    for (uint32_t _i = 0U; _i < ncap; ++_i)
      nvs[_i] = v1;
    memcpy(nvs, vs, sz * sizeof (vs[0U]));
    nvs[sz] = v1;
    KRML_HOST_FREE(vs);
    return
      ((LowStar_Vector_vector_str___uint8_t_){ .sz = sz + (uint32_t)1U, .cap = ncap, .vs = nvs });
  }
  vs[sz] = v1;
  return
    ((LowStar_Vector_vector_str___uint8_t_){ .sz = sz + (uint32_t)1U, .cap = cap, .vs = vs });
}

static LowStar_Vector_vector_str___uint8_t_
insert___uint8_t__uint32_t(LowStar_Vector_vector_str___uint8_t_ rv, uint8_t *v1)
{
  LowStar_Vector_vector_str___uint8_t_ irv = insert___uint8_t_(rv, v1);
  return irv;
}

static LowStar_Vector_vector_str___uint8_t_
insert_copy___uint8_t__uint32_t(
  LowStar_Regional_regional__uint32_t__uint8_t_ rg,
  void (*cp)(uint32_t x0, uint8_t *x1, uint8_t *x2),
  LowStar_Vector_vector_str___uint8_t_ rv,
  uint8_t *v1
)
{
  uint8_t *nv = LowStar_Regional_rg_alloc___uint8_t__uint32_t(rg);
  cp(rg.state, v1, nv);
  return insert___uint8_t__uint32_t(rv, nv);
}

static void
assign__LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_(
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ rv,
  uint32_t i1,
  LowStar_Vector_vector_str___uint8_t_ v1
)
{
  LowStar_Vector_assign__LowStar_Vector_vector_str__uint8_t_(rv, i1, v1);
}

static void
insert_(
  uint32_t hsz,
  uint32_t lv,
  uint32_t j1,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs,
  uint8_t *acc,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
)
{
  LowStar_Vector_vector_str___uint8_t_
  ihv =
    insert_copy___uint8_t__uint32_t((
        (LowStar_Regional_regional__uint32_t__uint8_t_){
          .state = hsz,
          .dummy = hash_dummy,
          .r_alloc = hash_r_alloc,
          .r_free = hash_r_free
        }
      ),
      hash_copy,
      LowStar_Vector_index__LowStar_Vector_vector_str__uint8_t_(hs, lv),
      acc);
  assign__LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_(hs,
    lv,
    ihv);
  if (j1 % (uint32_t)2U == (uint32_t)1U)
  {
    LowStar_Vector_vector_str___uint8_t_
    lvhs = LowStar_Vector_index__LowStar_Vector_vector_str__uint8_t_(hs, lv);
    hash_fun(LowStar_Vector_index___uint8_t_(lvhs, lvhs.sz - (uint32_t)2U), acc, acc);
    insert_(hsz, lv + (uint32_t)1U, j1 / (uint32_t)2U, hs, acc, hash_fun);
    return;
  }
}

bool mt_insert_pre(const merkle_tree *mt, uint8_t *v1)
{
  merkle_tree mt1 = *(merkle_tree *)mt;
  return mt1.j < uint32_32_max && uint64_max - mt1.offset >= (uint64_t)(mt1.j + (uint32_t)1U);
}

void mt_insert(merkle_tree *mt, uint8_t *v1)
{
  merkle_tree mtv = *mt;
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs = mtv.hs;
  uint32_t hsz1 = mtv.hash_size;
  insert_(hsz1, (uint32_t)0U, mtv.j, hs, v1, mtv.hash_fun);
  *mt
  =
    (
      (merkle_tree){
        .hash_size = mtv.hash_size,
        .offset = mtv.offset,
        .i = mtv.i,
        .j = mtv.j + (uint32_t)1U,
        .hs = mtv.hs,
        .rhs_ok = false,
        .rhs = mtv.rhs,
        .mroot = mtv.mroot,
        .hash_fun = mtv.hash_fun
      }
    );
}

merkle_tree
*mt_create_custom(
  uint32_t hsz,
  uint8_t *init1,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
)
{
  merkle_tree *mt = create_empty_mt(hsz, hash_fun);
  mt_insert(mt, init1);
  return mt;
}

merkle_tree *mt_create(uint8_t *init1)
{
  return mt_create_custom((uint32_t)32U, init1, sha256_compress);
}

LowStar_Vector_vector_str___uint8_t_ *init_path(uint32_t hsz)
{
  KRML_CHECK_SIZE(sizeof (LowStar_Vector_vector_str___uint8_t_), (uint32_t)1U);
  LowStar_Vector_vector_str___uint8_t_
  *buf = KRML_HOST_MALLOC(sizeof (LowStar_Vector_vector_str___uint8_t_));
  buf[0U]
  =
    rg_alloc__LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_((
        (LowStar_Regional_regional__LowStar_Regional_regional__uint32_t__uint8_t__LowStar_Vector_vector_str___uint8_t_){
          .state = {
            .state = hsz,
            .dummy = hash_dummy,
            .r_alloc = hash_r_alloc,
            .r_free = hash_r_free
          },
          .dummy = hash_vec_dummy,
          .r_alloc = hash_vec_r_alloc,
          .r_free = hash_vec_r_free
        }
      ));
  return buf;
}

static LowStar_Vector_vector_str___uint8_t_
clear___uint8_t_(LowStar_Vector_vector_str___uint8_t_ vec)
{
  return
    ((LowStar_Vector_vector_str___uint8_t_){ .sz = (uint32_t)0U, .cap = vec.cap, .vs = vec.vs });
}

void clear_path(uint32_t uu____3215, LowStar_Vector_vector_str___uint8_t_ *p1)
{
  *p1 = clear___uint8_t_(*p1);
}

void free_path(uint32_t uu____3362, LowStar_Vector_vector_str___uint8_t_ *p1)
{
  LowStar_Vector_free___uint8_t_(*p1);
  KRML_HOST_FREE(p1);
}

static void
assign_copy___uint8_t__uint32_t(
  LowStar_Regional_regional__uint32_t__uint8_t_ rg,
  void (*cp)(uint32_t x0, uint8_t *x1, uint8_t *x2),
  LowStar_Vector_vector_str___uint8_t_ rv,
  uint32_t i1,
  uint8_t *v1
)
{
  uint8_t *uu____0 = LowStar_Vector_index___uint8_t_(rv, i1);
  cp(rg.state, v1, uu____0);
}

static void
construct_rhs(
  uint32_t hsz,
  uint32_t lv,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs,
  LowStar_Vector_vector_str___uint8_t_ rhs,
  uint32_t i1,
  uint32_t j1,
  uint8_t *acc,
  bool actd,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
)
{
  if (!(j1 == (uint32_t)0U))
  {
    uint32_t ofs = offset_of(i1);
    if (j1 % (uint32_t)2U == (uint32_t)0U)
    {
      construct_rhs(hsz,
        lv + (uint32_t)1U,
        hs,
        rhs,
        i1 / (uint32_t)2U,
        j1 / (uint32_t)2U,
        acc,
        actd,
        hash_fun);
      return;
    }
    if (actd)
    {
      assign_copy___uint8_t__uint32_t((
          (LowStar_Regional_regional__uint32_t__uint8_t_){
            .state = hsz,
            .dummy = hash_dummy,
            .r_alloc = hash_r_alloc,
            .r_free = hash_r_free
          }
        ),
        hash_copy,
        rhs,
        lv,
        acc);
      hash_fun(LowStar_Vector_index___uint8_t_(LowStar_Vector_index__LowStar_Vector_vector_str__uint8_t_(hs,
            lv),
          j1 - (uint32_t)1U - ofs),
        acc,
        acc);
    }
    else
    {
      hash_copy(hsz,
        LowStar_Vector_index___uint8_t_(LowStar_Vector_index__LowStar_Vector_vector_str__uint8_t_(hs,
            lv),
          j1 - (uint32_t)1U - ofs),
        acc);
    }
    construct_rhs(hsz,
      lv + (uint32_t)1U,
      hs,
      rhs,
      i1 / (uint32_t)2U,
      j1 / (uint32_t)2U,
      acc,
      true,
      hash_fun);
    return;
  }
}

bool mt_get_root_pre(const merkle_tree *mt, uint8_t *rt)
{
  merkle_tree *mt1 = (merkle_tree *)mt;
  merkle_tree mt2 = *mt1;
  return true;
}

void mt_get_root(const merkle_tree *mt, uint8_t *rt)
{
  merkle_tree *mt1 = (merkle_tree *)mt;
  merkle_tree mtv = *mt1;
  uint64_t prefix = mtv.offset;
  uint32_t i1 = mtv.i;
  uint32_t j1 = mtv.j;
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs = mtv.hs;
  LowStar_Vector_vector_str___uint8_t_ rhs = mtv.rhs;
  uint8_t *mroot = mtv.mroot;
  uint32_t hash_size = mtv.hash_size;
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2) = mtv.hash_fun;
  if (mtv.rhs_ok)
  {
    hash_copy(hash_size, mroot, rt);
    return;
  }
  construct_rhs(hash_size, (uint32_t)0U, hs, rhs, i1, j1, rt, false, hash_fun);
  hash_copy(hash_size, rt, mroot);
  *mt1
  =
    (
      (merkle_tree){
        .hash_size = hash_size,
        .offset = prefix,
        .i = i1,
        .j = j1,
        .hs = hs,
        .rhs_ok = true,
        .rhs = rhs,
        .mroot = mroot,
        .hash_fun = hash_fun
      }
    );
}

void path_insert(uint32_t hsz, LowStar_Vector_vector_str___uint8_t_ *p1, uint8_t *hp)
{
  LowStar_Vector_vector_str___uint8_t_ pv = p1[0U];
  LowStar_Vector_vector_str___uint8_t_ ipv = insert___uint8_t_(pv, hp);
  *p1 = ipv;
}

static uint32_t mt_path_length_step(uint32_t k1, uint32_t j1, bool actd)
{
  if (j1 == (uint32_t)0U)
  {
    return (uint32_t)0U;
  }
  if (k1 % (uint32_t)2U == (uint32_t)0U)
  {
    if (j1 == k1 || (j1 == k1 + (uint32_t)1U && !actd))
    {
      return (uint32_t)0U;
    }
    return (uint32_t)1U;
  }
  return (uint32_t)1U;
}

static uint32_t mt_path_length(uint32_t lv, uint32_t k1, uint32_t j1, bool actd)
{
  if (j1 == (uint32_t)0U)
  {
    return (uint32_t)0U;
  }
  bool nactd = actd || j1 % (uint32_t)2U == (uint32_t)1U;
  return
    mt_path_length_step(k1,
      j1,
      actd)
    + mt_path_length(lv + (uint32_t)1U, k1 / (uint32_t)2U, j1 / (uint32_t)2U, nactd);
}

static void
mt_get_path_(
  uint32_t hsz,
  uint32_t lv,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs,
  LowStar_Vector_vector_str___uint8_t_ rhs,
  uint32_t i1,
  uint32_t j1,
  uint32_t k1,
  LowStar_Vector_vector_str___uint8_t_ *p1,
  bool actd
)
{
  uint32_t ofs = offset_of(i1);
  if (!(j1 == (uint32_t)0U))
  {
    uint32_t ofs1 = offset_of(i1);
    if (k1 % (uint32_t)2U == (uint32_t)1U)
    {
      uint8_t
      *uu____0 =
        LowStar_Vector_index___uint8_t_(LowStar_Vector_index__LowStar_Vector_vector_str__uint8_t_(hs,
            lv),
          k1 - (uint32_t)1U - ofs1);
      LowStar_Vector_vector_str___uint8_t_ pv = p1[0U];
      LowStar_Vector_vector_str___uint8_t_ ipv = insert___uint8_t_(pv, uu____0);
      *p1 = ipv;
    }
    else if (!(k1 == j1))
    {
      if (k1 + (uint32_t)1U == j1)
      {
        if (actd)
        {
          uint8_t *uu____1 = LowStar_Vector_index___uint8_t_(rhs, lv);
          LowStar_Vector_vector_str___uint8_t_ pv = p1[0U];
          LowStar_Vector_vector_str___uint8_t_ ipv = insert___uint8_t_(pv, uu____1);
          *p1 = ipv;
        }
      }
      else
      {
        uint8_t
        *uu____2 =
          LowStar_Vector_index___uint8_t_(LowStar_Vector_index__LowStar_Vector_vector_str__uint8_t_(hs,
              lv),
            k1 + (uint32_t)1U - ofs1);
        LowStar_Vector_vector_str___uint8_t_ pv = p1[0U];
        LowStar_Vector_vector_str___uint8_t_ ipv = insert___uint8_t_(pv, uu____2);
        *p1 = ipv;
      }
    }
    bool ite;
    if (j1 % (uint32_t)2U == (uint32_t)0U)
    {
      ite = actd;
    }
    else
    {
      ite = true;
    }
    mt_get_path_(hsz,
      lv + (uint32_t)1U,
      hs,
      rhs,
      i1 / (uint32_t)2U,
      j1 / (uint32_t)2U,
      k1 / (uint32_t)2U,
      p1,
      ite);
    return;
  }
}

bool
mt_get_path_pre(
  const merkle_tree *mt,
  uint64_t idx,
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *root
)
{
  merkle_tree *mt1 = (merkle_tree *)mt;
  LowStar_Vector_vector_str___uint8_t_ *p2 = (LowStar_Vector_vector_str___uint8_t_ *)p1;
  merkle_tree mtv = *mt1;
  LowStar_Vector_vector_str___uint8_t_ uu____0 = *p2;
  return
    idx
    >= mtv.offset
    && idx - mtv.offset <= offset_range_limit
    &&
      mtv.i
      <= (uint32_t)(idx - mtv.offset)
      && (uint32_t)(idx - mtv.offset) < mtv.j
      && uu____0.sz == (uint32_t)0U;
}

uint32_t
mt_get_path(
  const merkle_tree *mt,
  uint64_t idx,
  LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *root
)
{
  merkle_tree *ncmt = (merkle_tree *)mt;
  mt_get_root(mt, root);
  merkle_tree mtv = *ncmt;
  uint32_t idx1 = (uint32_t)(idx - mtv.offset);
  uint32_t i1 = mtv.i;
  uint32_t ofs = offset_of(mtv.i);
  uint32_t j1 = mtv.j;
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs = mtv.hs;
  LowStar_Vector_vector_str___uint8_t_ rhs = mtv.rhs;
  uint8_t
  *ih =
    LowStar_Vector_index___uint8_t_(LowStar_Vector_index__LowStar_Vector_vector_str__uint8_t_(hs,
        (uint32_t)0U),
      idx1 - ofs);
  LowStar_Vector_vector_str___uint8_t_ pv = p1[0U];
  LowStar_Vector_vector_str___uint8_t_ ipv = insert___uint8_t_(pv, ih);
  *p1 = ipv;
  mt_get_path_(mtv.hash_size, (uint32_t)0U, hs, rhs, i1, j1, idx1, p1, false);
  return j1;
}

void move_left___uint8_t_(uint8_t **b, uint32_t dst, uint32_t src, uint32_t l)
{
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    b[dst + i] = b[src + i];
  }
}

static void
mt_flush_to_(
  uint32_t hsz,
  uint32_t lv,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs,
  uint32_t pi,
  uint32_t i1
)
{
  uint32_t oi = offset_of(i1);
  uint32_t opi = offset_of(pi);
  if (!(oi == opi))
  {
    uint32_t ofs = oi - opi;
    LowStar_Vector_vector_str___uint8_t_
    hvec = LowStar_Vector_index__LowStar_Vector_vector_str__uint8_t_(hs, lv);
    LowStar_Vector_vector_str___uint8_t_ flushed;
    if (ofs >= hvec.sz)
    {
      flushed =
        (
          (LowStar_Vector_vector_str___uint8_t_){
            .sz = (uint32_t)0U,
            .cap = hvec.cap,
            .vs = hvec.vs
          }
        );
    }
    else if (ofs == (uint32_t)0U)
    {
      flushed = hvec;
    }
    else
    {
      uint32_t n_shifted = hvec.sz - ofs;
      move_left___uint8_t_(hvec.vs, (uint32_t)0U, ofs, n_shifted);
      flushed =
        ((LowStar_Vector_vector_str___uint8_t_){ .sz = n_shifted, .cap = hvec.cap, .vs = hvec.vs });
    }
    assign__LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_(hs,
      lv,
      flushed);
    mt_flush_to_(hsz, lv + (uint32_t)1U, hs, pi / (uint32_t)2U, i1 / (uint32_t)2U);
    return;
  }
}

bool mt_flush_to_pre(const merkle_tree *mt, uint64_t idx)
{
  merkle_tree *mt1 = (merkle_tree *)mt;
  merkle_tree mtv = *mt1;
  return
    idx
    >= mtv.offset
    && idx - mtv.offset <= offset_range_limit
    && (uint32_t)(idx - mtv.offset) >= mtv.i && (uint32_t)(idx - mtv.offset) < mtv.j;
}

void mt_flush_to(merkle_tree *mt, uint64_t idx)
{
  merkle_tree mtv = *mt;
  uint64_t offset1 = mtv.offset;
  uint32_t idx1 = (uint32_t)(idx - offset1);
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs = mtv.hs;
  mt_flush_to_(mtv.hash_size, (uint32_t)0U, hs, mtv.i, idx1);
  *mt
  =
    (
      (merkle_tree){
        .hash_size = mtv.hash_size,
        .offset = mtv.offset,
        .i = idx1,
        .j = mtv.j,
        .hs = hs,
        .rhs_ok = mtv.rhs_ok,
        .rhs = mtv.rhs,
        .mroot = mtv.mroot,
        .hash_fun = mtv.hash_fun
      }
    );
}

bool mt_flush_pre(const merkle_tree *mt)
{
  merkle_tree uu____0 = *(merkle_tree *)mt;
  return uu____0.j > uu____0.i;
}

void mt_flush(merkle_tree *mt)
{
  merkle_tree mtv = *mt;
  uint64_t off = mtv.offset;
  uint32_t j1 = mtv.j;
  uint32_t j11 = j1 - (uint32_t)1U;
  uint64_t jo = off + (uint64_t)j11;
  mt_flush_to(mt, jo);
}

static void
free_elems_from___uint8_t__uint32_t(
  LowStar_Regional_regional__uint32_t__uint8_t_ rg,
  LowStar_Vector_vector_str___uint8_t_ rv,
  uint32_t idx
)
{
  LowStar_Regional_rg_free___uint8_t__uint32_t(rg, LowStar_Vector_index___uint8_t_(rv, idx));
  if (idx + (uint32_t)1U < rv.sz)
  {
    free_elems_from___uint8_t__uint32_t(rg, rv, idx + (uint32_t)1U);
    return;
  }
}

static LowStar_Vector_vector_str___uint8_t_
shrink___uint8_t_(LowStar_Vector_vector_str___uint8_t_ vec, uint32_t new_size)
{
  return
    ((LowStar_Vector_vector_str___uint8_t_){ .sz = new_size, .cap = vec.cap, .vs = vec.vs });
}

static LowStar_Vector_vector_str___uint8_t_
shrink___uint8_t__uint32_t(
  LowStar_Regional_regional__uint32_t__uint8_t_ rg,
  LowStar_Vector_vector_str___uint8_t_ rv,
  uint32_t new_size
)
{
  uint32_t size = rv.sz;
  if (new_size >= size)
  {
    return rv;
  }
  free_elems_from___uint8_t__uint32_t(rg, rv, new_size);
  LowStar_Vector_vector_str___uint8_t_ frv = shrink___uint8_t_(rv, new_size);
  return frv;
}

static void
mt_retract_to_(
  uint32_t hsz,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs,
  uint32_t lv,
  uint32_t i1,
  uint32_t s,
  uint32_t j1
)
{
  if (!(lv >= hs.sz))
  {
    LowStar_Vector_vector_str___uint8_t_
    hvec = LowStar_Vector_index__LowStar_Vector_vector_str__uint8_t_(hs, lv);
    uint32_t old_len = j1 - offset_of(i1);
    uint32_t new_len = s - offset_of(i1);
    LowStar_Vector_vector_str___uint8_t_
    retracted =
      shrink___uint8_t__uint32_t((
          (LowStar_Regional_regional__uint32_t__uint8_t_){
            .state = hsz,
            .dummy = hash_dummy,
            .r_alloc = hash_r_alloc,
            .r_free = hash_r_free
          }
        ),
        hvec,
        new_len);
    assign__LowStar_Vector_vector_str__uint8_t__LowStar_Regional_regional_uint32_t__uint8_t_(hs,
      lv,
      retracted);
    if (lv + (uint32_t)1U < hs.sz)
    {
      mt_retract_to_(hsz,
        hs,
        lv + (uint32_t)1U,
        i1 / (uint32_t)2U,
        s / (uint32_t)2U,
        j1 / (uint32_t)2U);
      return;
    }
    return;
  }
}

bool mt_retract_to_pre(const merkle_tree *mt, uint64_t r)
{
  merkle_tree *mt1 = (merkle_tree *)mt;
  merkle_tree mtv = *mt1;
  return
    r
    >= mtv.offset
    && r - mtv.offset <= offset_range_limit
    && mtv.i <= (uint32_t)(r - mtv.offset) && (uint32_t)(r - mtv.offset) < mtv.j;
}

void mt_retract_to(merkle_tree *mt, uint64_t r)
{
  merkle_tree mtv = *mt;
  uint64_t offset1 = mtv.offset;
  uint32_t r1 = (uint32_t)(r - offset1);
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs = mtv.hs;
  mt_retract_to_(mtv.hash_size, hs, (uint32_t)0U, mtv.i, r1 + (uint32_t)1U, mtv.j);
  *mt
  =
    (
      (merkle_tree){
        .hash_size = mtv.hash_size,
        .offset = mtv.offset,
        .i = mtv.i,
        .j = r1 + (uint32_t)1U,
        .hs = hs,
        .rhs_ok = false,
        .rhs = mtv.rhs,
        .mroot = mtv.mroot,
        .hash_fun = mtv.hash_fun
      }
    );
}

static void
mt_verify_(
  uint32_t hsz,
  uint32_t k1,
  uint32_t j1,
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  uint32_t ppos,
  uint8_t *acc,
  bool actd,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
)
{
  LowStar_Vector_vector_str___uint8_t_ *ncp = (LowStar_Vector_vector_str___uint8_t_ *)p1;
  if (!(j1 == (uint32_t)0U))
  {
    bool nactd = actd || j1 % (uint32_t)2U == (uint32_t)1U;
    if (k1 % (uint32_t)2U == (uint32_t)0U)
    {
      if (j1 == k1 || (j1 == k1 + (uint32_t)1U && !actd))
      {
        mt_verify_(hsz, k1 / (uint32_t)2U, j1 / (uint32_t)2U, p1, ppos, acc, nactd, hash_fun);
        return;
      }
      uint8_t *phash = LowStar_Vector_index___uint8_t_(*ncp, ppos);
      hash_fun(acc, phash, acc);
      mt_verify_(hsz,
        k1 / (uint32_t)2U,
        j1 / (uint32_t)2U,
        p1,
        ppos + (uint32_t)1U,
        acc,
        nactd,
        hash_fun);
      return;
    }
    uint8_t *phash = LowStar_Vector_index___uint8_t_(*ncp, ppos);
    hash_fun(phash, acc, acc);
    mt_verify_(hsz,
      k1 / (uint32_t)2U,
      j1 / (uint32_t)2U,
      p1,
      ppos + (uint32_t)1U,
      acc,
      nactd,
      hash_fun);
    return;
  }
}

bool
mt_verify_pre(
  const merkle_tree *mt,
  uint64_t k1,
  uint64_t j1,
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *rt
)
{
  merkle_tree *mt1 = (merkle_tree *)mt;
  LowStar_Vector_vector_str___uint8_t_ *p2 = (LowStar_Vector_vector_str___uint8_t_ *)p1;
  merkle_tree mtv = *mt1;
  LowStar_Vector_vector_str___uint8_t_ uu____0 = *p2;
  return
    k1
    < j1
    && k1 >= mtv.offset && k1 - mtv.offset <= offset_range_limit
    && j1 >= mtv.offset && j1 - mtv.offset <= offset_range_limit
    &&
      uu____0.sz
      ==
        (uint32_t)1U
        +
          mt_path_length((uint32_t)0U,
            (uint32_t)(k1 - mtv.offset),
            (uint32_t)(j1 - mtv.offset),
            false);
}

bool
mt_verify(
  const merkle_tree *mt,
  uint64_t k1,
  uint64_t j1,
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *rt
)
{
  merkle_tree *ncmt = (merkle_tree *)mt;
  LowStar_Vector_vector_str___uint8_t_ *ncp = (LowStar_Vector_vector_str___uint8_t_ *)p1;
  merkle_tree mtv = *ncmt;
  uint32_t hsz1 = mtv.hash_size;
  LowStar_Regional_regional__uint32_t__uint8_t_
  hrg = { .state = hsz1, .dummy = hash_dummy, .r_alloc = hash_r_alloc, .r_free = hash_r_free };
  uint32_t k2 = (uint32_t)(k1 - mtv.offset);
  uint32_t j2 = (uint32_t)(j1 - mtv.offset);
  uint8_t *ih = LowStar_Regional_rg_alloc___uint8_t__uint32_t(hrg);
  hash_copy(hsz1, LowStar_Vector_index___uint8_t_(*ncp, (uint32_t)0U), ih);
  mt_verify_(hsz1, k2, j2, p1, (uint32_t)1U, ih, false, mtv.hash_fun);
  uint8_t res = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < hsz1; i++)
  {
    uint8_t uu____0 = FStar_UInt8_eq_mask(ih[i], rt[i]);
    res = uu____0 & res;
  }
  uint8_t z = res;
  bool r = z == (uint8_t)255U;
  LowStar_Regional_rg_free___uint8_t__uint32_t(hrg, ih);
  return r;
}

