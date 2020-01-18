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


#include "MerkleTree.h"

uint32_t hash_size = (uint32_t)32U;

static uint8_t *hash_r_alloc()
{
  KRML_CHECK_SIZE(sizeof (uint8_t), hash_size);
  uint8_t *buf = KRML_HOST_CALLOC(hash_size, sizeof (uint8_t));
  return buf;
}

void hash_r_free(uint8_t *v1)
{
  KRML_HOST_FREE(v1);
}

void hash_copy(uint8_t *src, uint8_t *dst)
{
  memcpy(dst, src, hash_size * sizeof (src[0U]));
}

#define Cpy 0

typedef uint8_t copyable___uint8_t__tags;

typedef void (*copyable___uint8_t_)(uint8_t *x0, uint8_t *x1);

static void (*hcpy)(uint8_t *x0, uint8_t *x1) = hash_copy;

static LowStar_Vector_vector_str___uint8_t_
hash_vec_dummy = { .sz = (uint32_t)0U, .cap = (uint32_t)0U, .vs = NULL };

typedef struct regional___uint8_t__s
{
  uint8_t *dummy;
  uint8_t *(*r_alloc)();
  void (*r_free)(uint8_t *x0);
}
regional___uint8_t_;

static LowStar_Vector_vector_str___uint8_t_ alloc_reserve___uint8_t_(uint32_t len, uint8_t *ia)
{
  KRML_CHECK_SIZE(sizeof (uint8_t *), len);
  uint8_t **buf = KRML_HOST_MALLOC(sizeof (uint8_t *) * len);
  for (uint32_t _i = 0U; _i < len; ++_i)
    buf[_i] = ia;
  return ((LowStar_Vector_vector_str___uint8_t_){ .sz = (uint32_t)0U, .cap = len, .vs = buf });
}

static LowStar_Vector_vector_str___uint8_t_ hash_vec_r_alloc()
{
  regional___uint8_t_ x0 = { .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free };
  uint8_t *ia1 = x0.dummy;
  return alloc_reserve___uint8_t_((uint32_t)1U, ia1);
}

static uint8_t *index___uint8_t_(LowStar_Vector_vector_str___uint8_t_ vec, uint32_t i1)
{
  return vec.vs[i1];
}

static void
free_elems___uint8_t_(
  regional___uint8_t_ rg0,
  LowStar_Vector_vector_str___uint8_t_ rv0,
  uint32_t idx0
)
{
  regional___uint8_t_ rg = rg0;
  LowStar_Vector_vector_str___uint8_t_ rv = rv0;
  uint32_t idx = idx0;
  while (true)
  {
    uint8_t *uu____0 = index___uint8_t_(rv, idx);
    rg.r_free(uu____0);
    if (idx != (uint32_t)0U)
    {
      idx--;
    }
    else
    {
      return;
    }
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable, returns inserted above");
  KRML_HOST_EXIT(255U);
}

static void free___uint8_t_(LowStar_Vector_vector_str___uint8_t_ vec)
{
  KRML_HOST_FREE(vec.vs);
}

static void free___uint8_t_0(regional___uint8_t_ rg, LowStar_Vector_vector_str___uint8_t_ rv)
{
  if (!(rv.sz == (uint32_t)0U))
  {
    free_elems___uint8_t_(rg, rv, rv.sz - (uint32_t)1U);
  }
  free___uint8_t_(rv);
}

void hash_vec_r_free(LowStar_Vector_vector_str___uint8_t_ v1)
{
  free___uint8_t_0((
      (regional___uint8_t_){ .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free }
    ),
    v1);
}

uint8_t *(*init_hash)() = hash_r_alloc;

void (*free_hash)(uint8_t *x0) = hash_r_free;

void hash_2(uint8_t *src1, uint8_t *src2, uint8_t *dst)
{
  uint8_t cb[64U] = { 0U };
  memcpy(cb, src1, hash_size * sizeof (src1[0U]));
  memcpy(cb + (uint32_t)32U, src2, hash_size * sizeof (src2[0U]));
  uint32_t buf[8U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_SHA2_256_s, { .case_SHA2_256_s = buf } };
  EverCrypt_Hash_state_s st = s;
  EverCrypt_Hash_init(&st);
  EverCrypt_Hash_update(&st, cb);
  EverCrypt_Hash_finish(&st, dst);
}

uint32_t uint32_32_max = (uint32_t)4294967295U;

uint64_t uint32_max = (uint64_t)4294967295U;

uint64_t uint64_max = (uint64_t)18446744073709551615U;

uint64_t offset_range_limit = (uint64_t)4294967295U;

uint32_t merkle_tree_size_lg = (uint32_t)32U;

bool uu___is_MT(merkle_tree projectee)
{
  return true;
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

static LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
alloc_rid__LowStar_Vector_vector_str__uint8_t_(
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

typedef struct regional__LowStar_Vector_vector_str___uint8_t__s
{
  LowStar_Vector_vector_str___uint8_t_ dummy;
  LowStar_Vector_vector_str___uint8_t_ (*r_alloc)();
  void (*r_free)(LowStar_Vector_vector_str___uint8_t_ x0);
}
regional__LowStar_Vector_vector_str___uint8_t_;

static void
assign__LowStar_Vector_vector_str__uint8_t_(
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ vec,
  uint32_t i1,
  LowStar_Vector_vector_str___uint8_t_ v1
)
{
  (vec.vs + i1)[0U] = v1;
}

static void
alloc___LowStar_Vector_vector_str__uint8_t_(
  regional__LowStar_Vector_vector_str___uint8_t_ rg0,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ rv0,
  uint32_t cidx0
)
{
  regional__LowStar_Vector_vector_str___uint8_t_ rg = rg0;
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ rv = rv0;
  uint32_t cidx = cidx0;
  while (true)
  {
    if (cidx == (uint32_t)0U)
    {
      return;
    }
    else
    {
      LowStar_Vector_vector_str___uint8_t_ v1 = rg.r_alloc();
      assign__LowStar_Vector_vector_str__uint8_t_(rv, cidx - (uint32_t)1U, v1);
      cidx--;
    }
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable, returns inserted above");
  KRML_HOST_EXIT(255U);
}

static LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
alloc_rid__LowStar_Vector_vector_str__uint8_t_0(
  regional__LowStar_Vector_vector_str___uint8_t_ rg,
  uint32_t len
)
{
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
  vec = alloc_rid__LowStar_Vector_vector_str__uint8_t_(len, rg.dummy);
  alloc___LowStar_Vector_vector_str__uint8_t_(rg, vec, len);
  return vec;
}

static LowStar_Vector_vector_str___uint8_t_ alloc_rid___uint8_t_(uint32_t len, uint8_t *v1)
{
  KRML_CHECK_SIZE(sizeof (uint8_t *), len);
  uint8_t **buf = KRML_HOST_MALLOC(sizeof (uint8_t *) * len);
  for (uint32_t _i = 0U; _i < len; ++_i)
    buf[_i] = v1;
  return ((LowStar_Vector_vector_str___uint8_t_){ .sz = len, .cap = len, .vs = buf });
}

static void
assign___uint8_t_(LowStar_Vector_vector_str___uint8_t_ vec, uint32_t i1, uint8_t *v1)
{
  (vec.vs + i1)[0U] = v1;
}

static void
alloc____uint8_t_(
  regional___uint8_t_ rg0,
  LowStar_Vector_vector_str___uint8_t_ rv0,
  uint32_t cidx0
)
{
  regional___uint8_t_ rg = rg0;
  LowStar_Vector_vector_str___uint8_t_ rv = rv0;
  uint32_t cidx = cidx0;
  while (true)
  {
    if (cidx == (uint32_t)0U)
    {
      return;
    }
    else
    {
      uint8_t *v1 = rg.r_alloc();
      assign___uint8_t_(rv, cidx - (uint32_t)1U, v1);
      cidx--;
    }
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable, returns inserted above");
  KRML_HOST_EXIT(255U);
}

static LowStar_Vector_vector_str___uint8_t_
alloc_rid___uint8_t_0(regional___uint8_t_ rg, uint32_t len)
{
  LowStar_Vector_vector_str___uint8_t_ vec = alloc_rid___uint8_t_(len, rg.dummy);
  alloc____uint8_t_(rg, vec, len);
  return vec;
}

static merkle_tree *create_empty_mt(void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2))
{
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
  hs =
    alloc_rid__LowStar_Vector_vector_str__uint8_t_0((
        (regional__LowStar_Vector_vector_str___uint8_t_){
          .dummy = hash_vec_dummy,
          .r_alloc = hash_vec_r_alloc,
          .r_free = hash_vec_r_free
        }
      ),
      (uint32_t)32U);
  LowStar_Vector_vector_str___uint8_t_
  rhs =
    alloc_rid___uint8_t_0((
        (regional___uint8_t_){ .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free }
      ),
      (uint32_t)32U);
  regional___uint8_t_ x0 = { .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free };
  uint8_t *mroot = x0.r_alloc();
  KRML_CHECK_SIZE(sizeof (merkle_tree), (uint32_t)1U);
  merkle_tree *mt = KRML_HOST_MALLOC(sizeof (merkle_tree));
  mt[0U]
  =
    (
      (merkle_tree){
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

static LowStar_Vector_vector_str___uint8_t_
index__LowStar_Vector_vector_str__uint8_t_(
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ vec,
  uint32_t i1
)
{
  return vec.vs[i1];
}

static void
free_elems__LowStar_Vector_vector_str__uint8_t_(
  regional__LowStar_Vector_vector_str___uint8_t_ rg0,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ rv0,
  uint32_t idx0
)
{
  regional__LowStar_Vector_vector_str___uint8_t_ rg = rg0;
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ rv = rv0;
  uint32_t idx = idx0;
  while (true)
  {
    LowStar_Vector_vector_str___uint8_t_
    uu____0 = index__LowStar_Vector_vector_str__uint8_t_(rv, idx);
    rg.r_free(uu____0);
    if (idx != (uint32_t)0U)
    {
      idx--;
    }
    else
    {
      return;
    }
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable, returns inserted above");
  KRML_HOST_EXIT(255U);
}

static void
free__LowStar_Vector_vector_str__uint8_t_(
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ vec
)
{
  KRML_HOST_FREE(vec.vs);
}

static void
free__LowStar_Vector_vector_str__uint8_t_0(
  regional__LowStar_Vector_vector_str___uint8_t_ rg,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ rv
)
{
  if (!(rv.sz == (uint32_t)0U))
  {
    free_elems__LowStar_Vector_vector_str__uint8_t_(rg, rv, rv.sz - (uint32_t)1U);
  }
  free__LowStar_Vector_vector_str__uint8_t_(rv);
}

void mt_free(merkle_tree *mt)
{
  merkle_tree mtv = *mt;
  free__LowStar_Vector_vector_str__uint8_t_0((
      (regional__LowStar_Vector_vector_str___uint8_t_){
        .dummy = hash_vec_dummy,
        .r_alloc = hash_vec_r_alloc,
        .r_free = hash_vec_r_free
      }
    ),
    mtv.hs);
  free___uint8_t_0((
      (regional___uint8_t_){ .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free }
    ),
    mtv.rhs);
  regional___uint8_t_ x0 = { .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free };
  x0.r_free(mtv.mroot);
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
insert___uint8_t_0(LowStar_Vector_vector_str___uint8_t_ rv, uint8_t *v1)
{
  LowStar_Vector_vector_str___uint8_t_ irv = insert___uint8_t_(rv, v1);
  return irv;
}

static LowStar_Vector_vector_str___uint8_t_
insert_copy___uint8_t_(
  regional___uint8_t_ rg,
  void (*cp)(uint8_t *x0, uint8_t *x1),
  LowStar_Vector_vector_str___uint8_t_ rv,
  uint8_t *v1
)
{
  uint8_t *nv = rg.r_alloc();
  void (*copy)(uint8_t *x0, uint8_t *x1) = cp;
  copy(v1, nv);
  return insert___uint8_t_0(rv, nv);
}

static void
assign__LowStar_Vector_vector_str__uint8_t_0(
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ rv,
  uint32_t i1,
  LowStar_Vector_vector_str___uint8_t_ v1
)
{
  assign__LowStar_Vector_vector_str__uint8_t_(rv, i1, v1);
}

static void
insert_(
  uint32_t lv0,
  uint32_t j10,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs0,
  uint8_t *acc0,
  void (*hash_fun0)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
)
{
  uint32_t lv = lv0;
  uint32_t j1 = j10;
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs = hs0;
  uint8_t *acc = acc0;
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2) = hash_fun0;
  while (true)
  {
    LowStar_Vector_vector_str___uint8_t_
    uu____0 = index__LowStar_Vector_vector_str__uint8_t_(hs, lv);
    LowStar_Vector_vector_str___uint8_t_
    ihv =
      insert_copy___uint8_t_((
          (regional___uint8_t_){ .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free }
        ),
        hcpy,
        uu____0,
        acc);
    assign__LowStar_Vector_vector_str__uint8_t_0(hs, lv, ihv);
    if (j1 % (uint32_t)2U == (uint32_t)1U)
    {
      LowStar_Vector_vector_str___uint8_t_
      lvhs = index__LowStar_Vector_vector_str__uint8_t_(hs, lv);
      hash_fun(index___uint8_t_(lvhs, lvhs.sz - (uint32_t)2U), acc, acc);
      lv++;
      j1 = j1 / (uint32_t)2U;
    }
    else
    {
      return;
    }
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable, returns inserted above");
  KRML_HOST_EXIT(255U);
}

bool mt_insert_pre(const merkle_tree *mt, uint8_t *v1)
{
  merkle_tree *mt1 = (merkle_tree *)mt;
  merkle_tree uu____0 = *mt1;
  return
    uu____0.j
    < uint32_32_max
    && uint64_max - uu____0.offset >= (uint64_t)(uu____0.j + (uint32_t)1U);
}

void mt_insert(merkle_tree *mt, uint8_t *v1)
{
  merkle_tree mtv = *mt;
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs = mtv.hs;
  insert_((uint32_t)0U, mtv.j, hs, v1, mtv.hash_fun);
  *mt
  =
    (
      (merkle_tree){
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
*mt_create_custom(uint8_t *init1, void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2))
{
  merkle_tree *mt = create_empty_mt(hash_fun);
  mt_insert(mt, init1);
  return mt;
}

merkle_tree *mt_create(uint8_t *init1)
{
  return mt_create_custom(init1, hash_2);
}

LowStar_Vector_vector_str___uint8_t_ *init_path()
{
  KRML_CHECK_SIZE(sizeof (LowStar_Vector_vector_str___uint8_t_), (uint32_t)1U);
  LowStar_Vector_vector_str___uint8_t_
  *buf = KRML_HOST_MALLOC(sizeof (LowStar_Vector_vector_str___uint8_t_));
  buf[0U] = hash_vec_r_alloc();
  return buf;
}

static LowStar_Vector_vector_str___uint8_t_
clear___uint8_t_(LowStar_Vector_vector_str___uint8_t_ vec)
{
  return
    ((LowStar_Vector_vector_str___uint8_t_){ .sz = (uint32_t)0U, .cap = vec.cap, .vs = vec.vs });
}

void clear_path(LowStar_Vector_vector_str___uint8_t_ *p1)
{
  *p1 = clear___uint8_t_(*p1);
}

void free_path(LowStar_Vector_vector_str___uint8_t_ *p1)
{
  free___uint8_t_(*p1);
  KRML_HOST_FREE(p1);
}

static void
assign_copy___uint8_t_(
  void (*cp)(uint8_t *x0, uint8_t *x1),
  LowStar_Vector_vector_str___uint8_t_ rv,
  uint32_t i1,
  uint8_t *v1
)
{
  void (*copy)(uint8_t *x0, uint8_t *x1) = cp;
  copy(v1, index___uint8_t_(rv, i1));
}

static void
construct_rhs(
  uint32_t lv0,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs0,
  LowStar_Vector_vector_str___uint8_t_ rhs0,
  uint32_t i10,
  uint32_t j10,
  uint8_t *acc0,
  bool actd0,
  void (*hash_fun0)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
)
{
  uint32_t lv = lv0;
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs = hs0;
  LowStar_Vector_vector_str___uint8_t_ rhs = rhs0;
  uint32_t i1 = i10;
  uint32_t j1 = j10;
  uint8_t *acc = acc0;
  bool actd = actd0;
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2) = hash_fun0;
  while (true)
  {
    uint32_t ofs = offset_of(i1);
    regional___uint8_t_ x0 = { .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free };
    void (*copy1)(uint8_t *x0, uint8_t *x1) = hcpy;
    if (j1 == (uint32_t)0U)
    {
      return;
    }
    else if (j1 % (uint32_t)2U == (uint32_t)0U)
    {
      lv++;
      i1 = i1 / (uint32_t)2U;
      j1 = j1 / (uint32_t)2U;
    }
    else
    {
      if (actd)
      {
        regional___uint8_t_
        unused = { .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free };
        assign_copy___uint8_t_(hcpy, rhs, lv, acc);
        hash_fun(index___uint8_t_(index__LowStar_Vector_vector_str__uint8_t_(hs, lv),
            j1 - (uint32_t)1U - ofs),
          acc,
          acc);
      }
      else
      {
        copy1(index___uint8_t_(index__LowStar_Vector_vector_str__uint8_t_(hs, lv),
            j1 - (uint32_t)1U - ofs),
          acc);
      }
      lv++;
      i1 = i1 / (uint32_t)2U;
      j1 = j1 / (uint32_t)2U;
      actd = true;
    }
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable, returns inserted above");
  KRML_HOST_EXIT(255U);
}

bool mt_get_root_pre(const merkle_tree *mt, uint8_t *rt)
{
  merkle_tree *mt1 = (merkle_tree *)mt;
  merkle_tree uu____0 = *mt1;
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
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2) = mtv.hash_fun;
  if (mtv.rhs_ok)
  {
    regional___uint8_t_ x0 = { .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free };
    hcpy(mroot, rt);
    return;
  }
  construct_rhs((uint32_t)0U, hs, rhs, i1, j1, rt, false, hash_fun);
  regional___uint8_t_ x0 = { .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free };
  hcpy(rt, mroot);
  *mt1
  =
    (
      (merkle_tree){
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

void path_insert(LowStar_Vector_vector_str___uint8_t_ *p1, uint8_t *hp)
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
  uint32_t lv0,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs0,
  LowStar_Vector_vector_str___uint8_t_ rhs0,
  uint32_t i10,
  uint32_t j10,
  uint32_t k10,
  LowStar_Vector_vector_str___uint8_t_ *p10,
  bool actd0
)
{
  uint32_t lv = lv0;
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs = hs0;
  LowStar_Vector_vector_str___uint8_t_ rhs = rhs0;
  uint32_t i1 = i10;
  uint32_t j1 = j10;
  uint32_t k1 = k10;
  LowStar_Vector_vector_str___uint8_t_ *p1 = p10;
  bool actd = actd0;
  while (true)
  {
    uint32_t ofs = offset_of(i1);
    if (j1 == (uint32_t)0U)
    {
      return;
    }
    else
    {
      uint32_t ofs1 = offset_of(i1);
      if (k1 % (uint32_t)2U == (uint32_t)1U)
      {
        uint8_t
        *uu____0 =
          index___uint8_t_(index__LowStar_Vector_vector_str__uint8_t_(hs, lv),
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
            uint8_t *uu____1 = index___uint8_t_(rhs, lv);
            LowStar_Vector_vector_str___uint8_t_ pv = p1[0U];
            LowStar_Vector_vector_str___uint8_t_ ipv = insert___uint8_t_(pv, uu____1);
            *p1 = ipv;
          }
        }
        else
        {
          uint8_t
          *uu____2 =
            index___uint8_t_(index__LowStar_Vector_vector_str__uint8_t_(hs, lv),
              k1 + (uint32_t)1U - ofs1);
          LowStar_Vector_vector_str___uint8_t_ pv = p1[0U];
          LowStar_Vector_vector_str___uint8_t_ ipv = insert___uint8_t_(pv, uu____2);
          *p1 = ipv;
        }
      }
      lv++;
      i1 = i1 / (uint32_t)2U;
      j1 = j1 / (uint32_t)2U;
      k1 = k1 / (uint32_t)2U;
      bool ite;
      if (j1 % (uint32_t)2U == (uint32_t)0U)
      {
        ite = actd;
      }
      else
      {
        ite = true;
      }
      actd = ite;
    }
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable, returns inserted above");
  KRML_HOST_EXIT(255U);
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
  merkle_tree uu____0 = *mt1;
  LowStar_Vector_vector_str___uint8_t_ uu____1 = *p2;
  return
    idx
    >= uu____0.offset
    && idx - uu____0.offset <= offset_range_limit
    &&
      uu____0.i
      <= (uint32_t)(idx - uu____0.offset)
      && (uint32_t)(idx - uu____0.offset) < uu____0.j
      && uu____1.sz == (uint32_t)0U;
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
  regional___uint8_t_ x0 = { .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free };
  void (*copy1)(uint8_t *x0, uint8_t *x1) = hcpy;
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
    index___uint8_t_(index__LowStar_Vector_vector_str__uint8_t_(hs, (uint32_t)0U),
      idx1 - ofs);
  LowStar_Vector_vector_str___uint8_t_ pv = p1[0U];
  LowStar_Vector_vector_str___uint8_t_ ipv = insert___uint8_t_(pv, ih);
  *p1 = ipv;
  mt_get_path_((uint32_t)0U, hs, rhs, i1, j1, idx1, p1, false);
  return j1;
}

static LowStar_Vector_vector_str___uint8_t_
flush___uint8_t_(LowStar_Vector_vector_str___uint8_t_ vec, uint8_t *ia, uint32_t i1)
{
  uint32_t fsz = vec.sz - i1;
  uint32_t asz;
  if (vec.sz == i1)
  {
    asz = (uint32_t)1U;
  }
  else
  {
    asz = fsz;
  }
  uint8_t **vs = vec.vs;
  KRML_CHECK_SIZE(sizeof (uint8_t *), asz);
  uint8_t **fvs = KRML_HOST_MALLOC(sizeof (uint8_t *) * asz);
  for (uint32_t _i = 0U; _i < asz; ++_i)
    fvs[_i] = ia;
  memcpy(fvs, vs + i1, fsz * sizeof (vs[0U]));
  KRML_HOST_FREE(vs);
  return ((LowStar_Vector_vector_str___uint8_t_){ .sz = fsz, .cap = asz, .vs = fvs });
}

static LowStar_Vector_vector_str___uint8_t_
flush___uint8_t_0(regional___uint8_t_ rg, LowStar_Vector_vector_str___uint8_t_ rv, uint32_t i1)
{
  if (!(i1 == (uint32_t)0U))
  {
    free_elems___uint8_t_(rg, rv, i1 - (uint32_t)1U);
  }
  LowStar_Vector_vector_str___uint8_t_ frv = flush___uint8_t_(rv, rg.dummy, i1);
  return frv;
}

static void
mt_flush_to_(
  uint32_t lv0,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs0,
  uint32_t pi0,
  uint32_t i10
)
{
  uint32_t lv = lv0;
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs = hs0;
  uint32_t pi = pi0;
  uint32_t i1 = i10;
  while (true)
  {
    uint32_t oi = offset_of(i1);
    uint32_t opi = offset_of(pi);
    if (oi == opi)
    {
      return;
    }
    else
    {
      uint32_t ofs = oi - opi;
      LowStar_Vector_vector_str___uint8_t_
      hvec = index__LowStar_Vector_vector_str__uint8_t_(hs, lv);
      LowStar_Vector_vector_str___uint8_t_
      flushed =
        flush___uint8_t_0((
            (regional___uint8_t_){ .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free }
          ),
          hvec,
          ofs);
      assign__LowStar_Vector_vector_str__uint8_t_0(hs, lv, flushed);
      lv++;
      pi = pi / (uint32_t)2U;
      i1 = i1 / (uint32_t)2U;
    }
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable, returns inserted above");
  KRML_HOST_EXIT(255U);
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
  mt_flush_to_((uint32_t)0U, hs, mtv.i, idx1);
  *mt
  =
    (
      (merkle_tree){
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
free_elems_from___uint8_t_(
  regional___uint8_t_ rg0,
  LowStar_Vector_vector_str___uint8_t_ rv0,
  uint32_t idx0
)
{
  regional___uint8_t_ rg = rg0;
  LowStar_Vector_vector_str___uint8_t_ rv = rv0;
  uint32_t idx = idx0;
  while (true)
  {
    uint8_t *uu____0 = index___uint8_t_(rv, idx);
    rg.r_free(uu____0);
    if (idx + (uint32_t)1U < rv.sz)
    {
      idx++;
    }
    else
    {
      return;
    }
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable, returns inserted above");
  KRML_HOST_EXIT(255U);
}

static LowStar_Vector_vector_str___uint8_t_
shrink___uint8_t_(LowStar_Vector_vector_str___uint8_t_ vec, uint32_t new_size)
{
  return
    ((LowStar_Vector_vector_str___uint8_t_){ .sz = new_size, .cap = vec.cap, .vs = vec.vs });
}

static LowStar_Vector_vector_str___uint8_t_
shrink___uint8_t_0(
  regional___uint8_t_ rg,
  LowStar_Vector_vector_str___uint8_t_ rv,
  uint32_t new_size
)
{
  uint32_t size = rv.sz;
  if (new_size >= size)
  {
    return rv;
  }
  free_elems_from___uint8_t_(rg, rv, new_size);
  LowStar_Vector_vector_str___uint8_t_ frv = shrink___uint8_t_(rv, new_size);
  return frv;
}

static void
mt_retract_to_(
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs0,
  uint32_t lv0,
  uint32_t i10,
  uint32_t s0,
  uint32_t j10
)
{
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs = hs0;
  uint32_t lv = lv0;
  uint32_t i1 = i10;
  uint32_t s = s0;
  uint32_t j1 = j10;
  while (true)
  {
    if (lv >= hs.sz)
    {
      return;
    }
    else
    {
      LowStar_Vector_vector_str___uint8_t_
      hvec = index__LowStar_Vector_vector_str__uint8_t_(hs, lv);
      uint32_t old_len = j1 - offset_of(i1);
      uint32_t new_len = s - offset_of(i1);
      LowStar_Vector_vector_str___uint8_t_
      retracted =
        shrink___uint8_t_0((
            (regional___uint8_t_){ .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free }
          ),
          hvec,
          new_len);
      assign__LowStar_Vector_vector_str__uint8_t_0(hs, lv, retracted);
      if (lv + (uint32_t)1U < hs.sz)
      {
        lv++;
        i1 = i1 / (uint32_t)2U;
        s = s / (uint32_t)2U;
        j1 = j1 / (uint32_t)2U;
      }
      else
      {
        return;
      }
    }
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable, returns inserted above");
  KRML_HOST_EXIT(255U);
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
  mt_retract_to_(hs, (uint32_t)0U, mtv.i, r1 + (uint32_t)1U, mtv.j);
  *mt
  =
    (
      (merkle_tree){
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
  uint32_t k10,
  uint32_t j10,
  const LowStar_Vector_vector_str___uint8_t_ *p10,
  uint32_t ppos0,
  uint8_t *acc0,
  bool actd0,
  void (*hash_fun0)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
)
{
  uint32_t k1 = k10;
  uint32_t j1 = j10;
  const LowStar_Vector_vector_str___uint8_t_ *p1 = p10;
  uint32_t ppos = ppos0;
  uint8_t *acc = acc0;
  bool actd = actd0;
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2) = hash_fun0;
  while (true)
  {
    LowStar_Vector_vector_str___uint8_t_ *ncp = (LowStar_Vector_vector_str___uint8_t_ *)p1;
    if (j1 == (uint32_t)0U)
    {
      return;
    }
    else
    {
      bool nactd = actd || j1 % (uint32_t)2U == (uint32_t)1U;
      if (k1 % (uint32_t)2U == (uint32_t)0U)
      {
        if (j1 == k1 || (j1 == k1 + (uint32_t)1U && !actd))
        {
          k1 = k1 / (uint32_t)2U;
          j1 = j1 / (uint32_t)2U;
          actd = nactd;
        }
        else
        {
          uint8_t *phash = index___uint8_t_(*ncp, ppos);
          hash_fun(acc, phash, acc);
          k1 = k1 / (uint32_t)2U;
          j1 = j1 / (uint32_t)2U;
          ppos++;
          actd = nactd;
        }
      }
      else
      {
        uint8_t *phash = index___uint8_t_(*ncp, ppos);
        hash_fun(phash, acc, acc);
        k1 = k1 / (uint32_t)2U;
        j1 = j1 / (uint32_t)2U;
        ppos++;
        actd = nactd;
      }
    }
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable, returns inserted above");
  KRML_HOST_EXIT(255U);
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
  merkle_tree uu____0 = *mt1;
  LowStar_Vector_vector_str___uint8_t_ uu____1 = *p2;
  return
    k1
    < j1
    && k1 >= uu____0.offset && k1 - uu____0.offset <= offset_range_limit
    && j1 >= uu____0.offset && j1 - uu____0.offset <= offset_range_limit
    &&
      uu____1.sz
      ==
        (uint32_t)1U
        +
          mt_path_length((uint32_t)0U,
            (uint32_t)(k1 - uu____0.offset),
            (uint32_t)(j1 - uu____0.offset),
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
  uint32_t k2 = (uint32_t)(k1 - mtv.offset);
  uint32_t j2 = (uint32_t)(j1 - mtv.offset);
  regional___uint8_t_ x00 = { .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free };
  uint8_t *ih = x00.r_alloc();
  regional___uint8_t_ x01 = { .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free };
  void (*copy1)(uint8_t *x0, uint8_t *x1) = hcpy;
  copy1(index___uint8_t_(*ncp, (uint32_t)0U), ih);
  mt_verify_(k2, j2, p1, (uint32_t)1U, ih, false, mtv.hash_fun);
  uint8_t res = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < hash_size; i++)
  {
    uint8_t uu____0 = FStar_UInt8_eq_mask(ih[i], rt[i]);
    res = uu____0 & res;
  }
  uint8_t z = res;
  bool r = z == (uint8_t)255U;
  regional___uint8_t_ x0 = { .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free };
  x0.r_free(ih);
  return r;
}

typedef struct __bool_uint32_t_s
{
  bool fst;
  uint32_t snd;
}
__bool_uint32_t;

static __bool_uint32_t
serialize_bool(bool ok, bool x, uint8_t *buf1, uint32_t sz, uint32_t pos)
{
  if (!ok || pos >= sz)
  {
    return ((__bool_uint32_t){ .fst = false, .snd = (uint32_t)0U });
  }
  uint8_t ite;
  if (x)
  {
    ite = (uint8_t)1U;
  }
  else
  {
    ite = (uint8_t)0U;
  }
  buf1[pos] = ite;
  return ((__bool_uint32_t){ .fst = true, .snd = pos + (uint32_t)1U });
}

static __bool_uint32_t
serialize_uint8_t(bool ok, uint8_t x, uint8_t *buf1, uint32_t sz, uint32_t pos)
{
  if (!ok || pos >= sz)
  {
    return ((__bool_uint32_t){ .fst = false, .snd = (uint32_t)0U });
  }
  buf1[pos] = x;
  return ((__bool_uint32_t){ .fst = true, .snd = pos + (uint32_t)1U });
}

static __bool_uint32_t
serialize_uint16_t(bool ok, uint16_t x, uint8_t *buf1, uint32_t sz, uint32_t pos)
{
  __bool_uint32_t scrut = serialize_uint8_t(ok, (uint8_t)(x >> (uint32_t)8U), buf1, sz, pos);
  bool ok1 = scrut.fst;
  uint32_t pos1 = scrut.snd;
  return serialize_uint8_t(ok1, (uint8_t)x, buf1, sz, pos1);
}

static __bool_uint32_t
serialize_uint32_t(bool ok, uint32_t x, uint8_t *buf1, uint32_t sz, uint32_t pos)
{
  __bool_uint32_t scrut = serialize_uint16_t(ok, (uint16_t)(x >> (uint32_t)16U), buf1, sz, pos);
  bool ok1 = scrut.fst;
  uint32_t pos1 = scrut.snd;
  return serialize_uint16_t(ok1, (uint16_t)x, buf1, sz, pos1);
}

static __bool_uint32_t
serialize_uint64_t(bool ok, uint64_t x, uint8_t *buf1, uint32_t sz, uint32_t pos)
{
  __bool_uint32_t scrut = serialize_uint32_t(ok, (uint32_t)(x >> (uint32_t)32U), buf1, sz, pos);
  bool ok1 = scrut.fst;
  uint32_t pos1 = scrut.snd;
  return serialize_uint32_t(ok1, (uint32_t)x, buf1, sz, pos1);
}

static __bool_uint32_t
(*serialize_offset_t)(bool x0, uint64_t x1, uint8_t *x2, uint32_t x3, uint32_t x4) =
  serialize_uint64_t;

static __bool_uint32_t
serialize_hash_i(
  bool ok0,
  uint8_t *x0,
  uint8_t *buf10,
  uint32_t sz0,
  uint32_t pos0,
  uint32_t i10
)
{
  bool ok = ok0;
  uint8_t *x = x0;
  uint8_t *buf1 = buf10;
  uint32_t sz = sz0;
  uint32_t pos = pos0;
  uint32_t i1 = i10;
  while (true)
  {
    if (!ok || pos >= sz)
    {
      return ((__bool_uint32_t){ .fst = false, .snd = (uint32_t)0U });
    }
    else
    {
      uint8_t b = x[i1];
      __bool_uint32_t scrut = serialize_uint8_t(ok, b, buf1, sz, pos);
      bool ok1 = scrut.fst;
      uint32_t pos1 = scrut.snd;
      uint32_t j1 = i1 + (uint32_t)1U;
      if (j1 < hash_size)
      {
        ok = ok1;
        pos = pos1;
        i1 = j1;
      }
      else
      {
        return ((__bool_uint32_t){ .fst = ok1, .snd = pos1 });
      }
    }
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable, returns inserted above");
  KRML_HOST_EXIT(255U);
}

static __bool_uint32_t
serialize_hash(bool ok, uint8_t *x, uint8_t *buf1, uint32_t sz, uint32_t pos)
{
  if (!ok || pos >= sz)
  {
    return ((__bool_uint32_t){ .fst = false, .snd = (uint32_t)0U });
  }
  return serialize_hash_i(ok, x, buf1, sz, pos, (uint32_t)0U);
}

static __bool_uint32_t
serialize_hash_vec_i(
  bool ok0,
  LowStar_Vector_vector_str___uint8_t_ x0,
  uint8_t *buf10,
  uint32_t sz0,
  uint32_t pos0,
  uint32_t i10
)
{
  bool ok = ok0;
  LowStar_Vector_vector_str___uint8_t_ x = x0;
  uint8_t *buf1 = buf10;
  uint32_t sz = sz0;
  uint32_t pos = pos0;
  uint32_t i1 = i10;
  while (true)
  {
    if (!ok || pos >= sz)
    {
      return ((__bool_uint32_t){ .fst = false, .snd = (uint32_t)0U });
    }
    else
    {
      uint8_t *vi = index___uint8_t_(x, i1);
      __bool_uint32_t scrut = serialize_hash(ok, vi, buf1, sz, pos);
      bool ok1 = scrut.fst;
      uint32_t pos1 = scrut.snd;
      uint32_t j1 = i1 + (uint32_t)1U;
      if (j1 < x.sz)
      {
        ok = ok1;
        pos = pos1;
        i1 = j1;
      }
      else
      {
        return ((__bool_uint32_t){ .fst = ok1, .snd = pos1 });
      }
    }
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable, returns inserted above");
  KRML_HOST_EXIT(255U);
}

static __bool_uint32_t
serialize_hash_vec(
  bool ok,
  LowStar_Vector_vector_str___uint8_t_ x,
  uint8_t *buf1,
  uint32_t sz,
  uint32_t pos
)
{
  if (!ok || pos >= sz)
  {
    return ((__bool_uint32_t){ .fst = false, .snd = (uint32_t)0U });
  }
  __bool_uint32_t scrut = serialize_uint32_t(ok, x.sz, buf1, sz, pos);
  bool ok1 = scrut.fst;
  uint32_t pos1 = scrut.snd;
  if (ok1 && x.sz > (uint32_t)0U)
  {
    return serialize_hash_vec_i(ok1, x, buf1, sz, pos1, (uint32_t)0U);
  }
  return ((__bool_uint32_t){ .fst = ok1, .snd = pos1 });
}

static uint64_t
hash_vv_bytes_i(
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ vv1,
  uint32_t i1
)
{
  if (i1 >= vv1.sz)
  {
    return (uint64_t)4U;
  }
  LowStar_Vector_vector_str___uint8_t_ vvi = index__LowStar_Vector_vector_str__uint8_t_(vv1, i1);
  uint64_t r = (uint64_t)4U + (uint64_t)vvi.sz * (uint64_t)hash_size;
  uint64_t rest = hash_vv_bytes_i(vv1, i1 + (uint32_t)1U);
  if (uint64_max - rest < r)
  {
    return uint64_max;
  }
  return rest + r;
}

static __bool_uint32_t
serialize_hash_vv_i(
  bool ok0,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ x0,
  uint8_t *buf10,
  uint32_t sz0,
  uint32_t pos0,
  uint32_t i10
)
{
  bool ok = ok0;
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ x = x0;
  uint8_t *buf1 = buf10;
  uint32_t sz = sz0;
  uint32_t pos = pos0;
  uint32_t i1 = i10;
  while (true)
  {
    if (!ok || pos >= sz)
    {
      return ((__bool_uint32_t){ .fst = false, .snd = (uint32_t)0U });
    }
    else
    {
      LowStar_Vector_vector_str___uint8_t_ vi = index__LowStar_Vector_vector_str__uint8_t_(x, i1);
      __bool_uint32_t scrut = serialize_hash_vec(ok, vi, buf1, sz, pos);
      bool ok1 = scrut.fst;
      uint32_t pos1 = scrut.snd;
      uint32_t j1 = i1 + (uint32_t)1U;
      if (j1 < x.sz)
      {
        ok = ok1;
        pos = pos1;
        i1 = j1;
      }
      else
      {
        return ((__bool_uint32_t){ .fst = ok1, .snd = pos1 });
      }
    }
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable, returns inserted above");
  KRML_HOST_EXIT(255U);
}

static __bool_uint32_t
serialize_hash_vv(
  bool ok,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ x,
  uint8_t *buf1,
  uint32_t sz,
  uint32_t pos
)
{
  if (!ok || pos >= sz)
  {
    return ((__bool_uint32_t){ .fst = false, .snd = (uint32_t)0U });
  }
  __bool_uint32_t scrut = serialize_uint32_t(ok, x.sz, buf1, sz, pos);
  bool ok1 = scrut.fst;
  uint32_t pos1 = scrut.snd;
  if (x.sz > (uint32_t)0U)
  {
    return serialize_hash_vv_i(ok1, x, buf1, sz, pos1, (uint32_t)0U);
  }
  return ((__bool_uint32_t){ .fst = ok1, .snd = pos1 });
}

typedef struct __bool_uint32_t_bool_s
{
  bool fst;
  uint32_t snd;
  bool thd;
}
__bool_uint32_t_bool;

static __bool_uint32_t_bool
deserialize_bool(bool ok, const uint8_t *buf1, uint32_t sz, uint32_t pos)
{
  if (!ok || pos >= sz)
  {
    return ((__bool_uint32_t_bool){ .fst = false, .snd = pos, .thd = false });
  }
  bool sw;
  switch (buf1[pos])
  {
    case 0U:
      {
        sw = false;
        break;
      }
    default:
      {
        sw = true;
      }
  }
  return ((__bool_uint32_t_bool){ .fst = true, .snd = pos + (uint32_t)1U, .thd = sw });
}

typedef struct __bool_uint32_t_uint8_t_s
{
  bool fst;
  uint32_t snd;
  uint8_t thd;
}
__bool_uint32_t_uint8_t;

static __bool_uint32_t_uint8_t
deserialize_uint8_t(bool ok, const uint8_t *buf1, uint32_t sz, uint32_t pos)
{
  if (!ok || pos >= sz)
  {
    return ((__bool_uint32_t_uint8_t){ .fst = false, .snd = pos, .thd = (uint8_t)0U });
  }
  return ((__bool_uint32_t_uint8_t){ .fst = true, .snd = pos + (uint32_t)1U, .thd = buf1[pos] });
}

typedef struct __bool_uint32_t_uint16_t_s
{
  bool fst;
  uint32_t snd;
  uint16_t thd;
}
__bool_uint32_t_uint16_t;

static __bool_uint32_t_uint16_t
deserialize_uint16_t(bool ok, const uint8_t *buf1, uint32_t sz, uint32_t pos)
{
  if (!ok || pos >= sz)
  {
    return ((__bool_uint32_t_uint16_t){ .fst = false, .snd = pos, .thd = (uint16_t)0U });
  }
  __bool_uint32_t_uint8_t scrut0 = deserialize_uint8_t(ok, buf1, sz, pos);
  bool ok1 = scrut0.fst;
  uint32_t pos1 = scrut0.snd;
  uint8_t b0 = scrut0.thd;
  __bool_uint32_t_uint8_t scrut = deserialize_uint8_t(ok1, buf1, sz, pos1);
  bool ok2 = scrut.fst;
  uint32_t pos2 = scrut.snd;
  uint8_t b1 = scrut.thd;
  return
    (
      (__bool_uint32_t_uint16_t){
        .fst = ok2,
        .snd = pos2,
        .thd = ((uint16_t)b0 << (uint32_t)8U) + (uint16_t)b1
      }
    );
}

typedef struct __bool_uint32_t_uint32_t_s
{
  bool fst;
  uint32_t snd;
  uint32_t thd;
}
__bool_uint32_t_uint32_t;

static __bool_uint32_t_uint32_t
deserialize_uint32_t(bool ok, const uint8_t *buf1, uint32_t sz, uint32_t pos)
{
  if (!ok || pos >= sz)
  {
    return ((__bool_uint32_t_uint32_t){ .fst = false, .snd = pos, .thd = (uint32_t)0U });
  }
  __bool_uint32_t_uint16_t scrut0 = deserialize_uint16_t(ok, buf1, sz, pos);
  bool ok1 = scrut0.fst;
  uint32_t pos1 = scrut0.snd;
  uint16_t b0 = scrut0.thd;
  __bool_uint32_t_uint16_t scrut = deserialize_uint16_t(ok1, buf1, sz, pos1);
  bool ok2 = scrut.fst;
  uint32_t pos2 = scrut.snd;
  uint16_t b1 = scrut.thd;
  return
    (
      (__bool_uint32_t_uint32_t){
        .fst = ok2,
        .snd = pos2,
        .thd = ((uint32_t)b0 << (uint32_t)16U) + (uint32_t)b1
      }
    );
}

typedef struct __bool_uint32_t_uint64_t_s
{
  bool fst;
  uint32_t snd;
  uint64_t thd;
}
__bool_uint32_t_uint64_t;

static __bool_uint32_t_uint64_t
deserialize_uint64_t(bool ok, const uint8_t *buf1, uint32_t sz, uint32_t pos)
{
  if (!ok || pos >= sz)
  {
    return ((__bool_uint32_t_uint64_t){ .fst = false, .snd = pos, .thd = (uint64_t)0U });
  }
  __bool_uint32_t_uint32_t scrut0 = deserialize_uint32_t(ok, buf1, sz, pos);
  bool ok1 = scrut0.fst;
  uint32_t pos1 = scrut0.snd;
  uint32_t b0 = scrut0.thd;
  __bool_uint32_t_uint32_t scrut = deserialize_uint32_t(ok1, buf1, sz, pos1);
  bool ok2 = scrut.fst;
  uint32_t pos2 = scrut.snd;
  uint32_t b1 = scrut.thd;
  return
    (
      (__bool_uint32_t_uint64_t){
        .fst = ok2,
        .snd = pos2,
        .thd = ((uint64_t)b0 << (uint32_t)32U) + (uint64_t)b1
      }
    );
}

static __bool_uint32_t_uint64_t
(*deserialize_offset_t)(bool x0, const uint8_t *x1, uint32_t x2, uint32_t x3) =
  deserialize_uint64_t;

static __bool_uint32_t_uint32_t
(*deserialize_index_t)(bool x0, const uint8_t *x1, uint32_t x2, uint32_t x3) =
  deserialize_uint32_t;

typedef struct __bool_uint32_t__uint8_t__s
{
  bool fst;
  uint32_t snd;
  uint8_t *thd;
}
__bool_uint32_t__uint8_t_;

static __bool_uint32_t__uint8_t_
deserialize_hash(bool ok, const uint8_t *buf1, uint32_t sz, uint32_t pos)
{
  if (!ok || pos >= sz)
  {
    regional___uint8_t_ x0 = { .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free };
    return ((__bool_uint32_t__uint8_t_){ .fst = false, .snd = pos, .thd = x0.dummy });
  }
  if (sz - pos < hash_size)
  {
    regional___uint8_t_ x0 = { .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free };
    return ((__bool_uint32_t__uint8_t_){ .fst = false, .snd = pos, .thd = x0.dummy });
  }
  regional___uint8_t_ x0 = { .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free };
  uint8_t *hash1 = x0.r_alloc();
  memcpy(hash1, (uint8_t *)buf1 + pos, hash_size * sizeof (((uint8_t *)buf1)[0U]));
  return ((__bool_uint32_t__uint8_t_){ .fst = true, .snd = pos + hash_size, .thd = hash1 });
}

static __bool_uint32_t
deserialize_hash_vec_i(
  bool ok0,
  const uint8_t *buf10,
  uint32_t sz0,
  uint32_t pos0,
  LowStar_Vector_vector_str___uint8_t_ res0,
  uint32_t i10
)
{
  bool ok = ok0;
  const uint8_t *buf1 = buf10;
  uint32_t sz = sz0;
  uint32_t pos = pos0;
  LowStar_Vector_vector_str___uint8_t_ res = res0;
  uint32_t i1 = i10;
  while (true)
  {
    if (!ok || pos >= sz)
    {
      return ((__bool_uint32_t){ .fst = false, .snd = pos });
    }
    else
    {
      __bool_uint32_t__uint8_t_ scrut = deserialize_hash(ok, buf1, sz, pos);
      bool ok1 = scrut.fst;
      uint32_t pos1 = scrut.snd;
      uint8_t *h1 = scrut.thd;
      if (!ok1)
      {
        return ((__bool_uint32_t){ .fst = false, .snd = pos1 });
      }
      else
      {
        assign___uint8_t_(res, i1, h1);
        uint32_t j1 = i1 + (uint32_t)1U;
        if (j1 < res.sz)
        {
          ok = ok1;
          pos = pos1;
          i1 = j1;
        }
        else
        {
          return ((__bool_uint32_t){ .fst = true, .snd = pos1 });
        }
      }
    }
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable, returns inserted above");
  KRML_HOST_EXIT(255U);
}

static LowStar_Vector_vector_str___uint8_t_ alloc___uint8_t_(uint32_t len, uint8_t *v1)
{
  return alloc_rid___uint8_t_(len, v1);
}

typedef struct __bool_uint32_t_LowStar_Vector_vector_str___uint8_t__s
{
  bool fst;
  uint32_t snd;
  LowStar_Vector_vector_str___uint8_t_ thd;
}
__bool_uint32_t_LowStar_Vector_vector_str___uint8_t_;

static __bool_uint32_t_LowStar_Vector_vector_str___uint8_t_
deserialize_hash_vec(bool ok, const uint8_t *buf1, uint32_t sz, uint32_t pos)
{
  if (!ok || pos >= sz)
  {
    regional__LowStar_Vector_vector_str___uint8_t_
    scrut = { .dummy = hash_vec_dummy, .r_alloc = hash_vec_r_alloc, .r_free = hash_vec_r_free };
    return
      (
        (__bool_uint32_t_LowStar_Vector_vector_str___uint8_t_){
          .fst = false,
          .snd = pos,
          .thd = scrut.dummy
        }
      );
  }
  __bool_uint32_t_uint32_t scrut0 = deserialize_uint32_t(ok, buf1, sz, pos);
  bool ok1 = scrut0.fst;
  uint32_t pos1 = scrut0.snd;
  uint32_t n1 = scrut0.thd;
  if (!ok1)
  {
    return
      (
        (__bool_uint32_t_LowStar_Vector_vector_str___uint8_t_){
          .fst = false,
          .snd = pos1,
          .thd = { .sz = (uint32_t)0U, .cap = (uint32_t)0U, .vs = NULL }
        }
      );
  }
  if (n1 == (uint32_t)0U)
  {
    return
      (
        (__bool_uint32_t_LowStar_Vector_vector_str___uint8_t_){
          .fst = true,
          .snd = pos1,
          .thd = { .sz = (uint32_t)0U, .cap = (uint32_t)0U, .vs = NULL }
        }
      );
  }
  regional___uint8_t_ x0 = { .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free };
  LowStar_Vector_vector_str___uint8_t_ res = alloc___uint8_t_(n1, x0.dummy);
  __bool_uint32_t scrut = deserialize_hash_vec_i(ok1, buf1, sz, pos1, res, (uint32_t)0U);
  bool ok2 = scrut.fst;
  uint32_t pos2 = scrut.snd;
  return
    ((__bool_uint32_t_LowStar_Vector_vector_str___uint8_t_){ .fst = ok2, .snd = pos2, .thd = res });
}

static __bool_uint32_t
deserialize_hash_vv_i(
  bool ok0,
  const uint8_t *buf10,
  uint32_t sz0,
  uint32_t pos0,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ res0,
  uint32_t i10
)
{
  bool ok = ok0;
  const uint8_t *buf1 = buf10;
  uint32_t sz = sz0;
  uint32_t pos = pos0;
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ res = res0;
  uint32_t i1 = i10;
  while (true)
  {
    if (!ok || pos >= sz)
    {
      return ((__bool_uint32_t){ .fst = false, .snd = (uint32_t)0U });
    }
    else
    {
      __bool_uint32_t_LowStar_Vector_vector_str___uint8_t_
      scrut = deserialize_hash_vec(ok, buf1, sz, pos);
      bool ok1 = scrut.fst;
      uint32_t pos1 = scrut.snd;
      LowStar_Vector_vector_str___uint8_t_ hv = scrut.thd;
      if (!ok1)
      {
        return ((__bool_uint32_t){ .fst = false, .snd = pos1 });
      }
      else
      {
        assign__LowStar_Vector_vector_str__uint8_t_(res, i1, hv);
        uint32_t j1 = i1 + (uint32_t)1U;
        if (j1 == res.sz)
        {
          return ((__bool_uint32_t){ .fst = true, .snd = pos1 });
        }
        else
        {
          ok = ok1;
          pos = pos1;
          i1 = j1;
        }
      }
    }
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable, returns inserted above");
  KRML_HOST_EXIT(255U);
}

static LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
alloc__LowStar_Vector_vector_str__uint8_t_(
  uint32_t len,
  LowStar_Vector_vector_str___uint8_t_ v1
)
{
  return alloc_rid__LowStar_Vector_vector_str__uint8_t_(len, v1);
}

typedef struct
__bool_uint32_t_LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t__s
{
  bool fst;
  uint32_t snd;
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ thd;
}
__bool_uint32_t_LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_;

static __bool_uint32_t_LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
deserialize_hash_vv(bool ok, const uint8_t *buf1, uint32_t sz, uint32_t pos)
{
  if (!ok || pos >= sz)
  {
    return
      (
        (__bool_uint32_t_LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_){
          .fst = false,
          .snd = pos,
          .thd = { .sz = (uint32_t)0U, .cap = (uint32_t)0U, .vs = NULL }
        }
      );
  }
  __bool_uint32_t_uint32_t scrut0 = deserialize_uint32_t(ok, buf1, sz, pos);
  bool ok1 = scrut0.fst;
  uint32_t pos1 = scrut0.snd;
  uint32_t n1 = scrut0.thd;
  if (!ok1)
  {
    return
      (
        (__bool_uint32_t_LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_){
          .fst = false,
          .snd = pos1,
          .thd = { .sz = (uint32_t)0U, .cap = (uint32_t)0U, .vs = NULL }
        }
      );
  }
  if (n1 == (uint32_t)0U)
  {
    return
      (
        (__bool_uint32_t_LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_){
          .fst = true,
          .snd = pos1,
          .thd = { .sz = (uint32_t)0U, .cap = (uint32_t)0U, .vs = NULL }
        }
      );
  }
  regional__LowStar_Vector_vector_str___uint8_t_
  scrut1 = { .dummy = hash_vec_dummy, .r_alloc = hash_vec_r_alloc, .r_free = hash_vec_r_free };
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
  res = alloc__LowStar_Vector_vector_str__uint8_t_(n1, scrut1.dummy);
  __bool_uint32_t scrut = deserialize_hash_vv_i(ok1, buf1, sz, pos1, res, (uint32_t)0U);
  bool ok2 = scrut.fst;
  uint32_t pos2 = scrut.snd;
  return
    (
      (__bool_uint32_t_LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_){
        .fst = ok2,
        .snd = pos2,
        .thd = res
      }
    );
}

uint64_t mt_serialize_size(const merkle_tree *mt)
{
  merkle_tree mtv = *(merkle_tree *)mt;
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs = mtv.hs;
  LowStar_Vector_vector_str___uint8_t_ rhs = mtv.rhs;
  uint64_t hs_sz = hash_vv_bytes_i(hs, (uint32_t)0U);
  if (hs_sz < (uint64_t)4294967295U)
  {
    return
      (uint64_t)21U
      + hs_sz
      + (uint64_t)1U
      + (uint64_t)4U + (uint64_t)rhs.sz * (uint64_t)hash_size
      + (uint64_t)hash_size;
  }
  return uint64_max;
}

uint64_t mt_serialize(const merkle_tree *mt, uint8_t *output, uint64_t sz)
{
  merkle_tree *mt1 = (merkle_tree *)mt;
  uint32_t sz1 = (uint32_t)sz;
  merkle_tree mtv = *mt1;
  __bool_uint32_t scrut = serialize_uint8_t(true, (uint8_t)0U, output, sz1, (uint32_t)0U);
  bool ok = scrut.fst;
  uint32_t pos = scrut.snd;
  __bool_uint32_t scrut0 = serialize_uint32_t(ok, hash_size, output, sz1, pos);
  bool ok1 = scrut0.fst;
  uint32_t pos1 = scrut0.snd;
  __bool_uint32_t scrut1 = serialize_offset_t(ok1, mtv.offset, output, sz1, pos1);
  bool ok2 = scrut1.fst;
  uint32_t pos2 = scrut1.snd;
  __bool_uint32_t scrut2 = serialize_uint32_t(ok2, mtv.i, output, sz1, pos2);
  bool ok3 = scrut2.fst;
  uint32_t pos3 = scrut2.snd;
  __bool_uint32_t scrut3 = serialize_uint32_t(ok3, mtv.j, output, sz1, pos3);
  bool ok4 = scrut3.fst;
  uint32_t pos4 = scrut3.snd;
  __bool_uint32_t scrut4 = serialize_hash_vv(ok4, mtv.hs, output, sz1, pos4);
  bool ok5 = scrut4.fst;
  uint32_t pos5 = scrut4.snd;
  __bool_uint32_t scrut5 = serialize_bool(ok5, mtv.rhs_ok, output, sz1, pos5);
  bool ok6 = scrut5.fst;
  uint32_t pos6 = scrut5.snd;
  __bool_uint32_t scrut6 = serialize_hash_vec(ok6, mtv.rhs, output, sz1, pos6);
  bool ok7 = scrut6.fst;
  uint32_t pos7 = scrut6.snd;
  __bool_uint32_t scrut7 = serialize_hash(ok7, mtv.mroot, output, sz1, pos7);
  bool ok8 = scrut7.fst;
  uint32_t pos8 = scrut7.snd;
  if (ok8)
  {
    return (uint64_t)pos8;
  }
  return (uint64_t)0U;
}

merkle_tree *mt_deserialize(const uint8_t *input, uint64_t sz)
{
  uint32_t sz1 = (uint32_t)sz;
  __bool_uint32_t_uint8_t scrut0 = deserialize_uint8_t(true, input, sz1, (uint32_t)0U);
  bool ok = scrut0.fst;
  uint32_t pos = scrut0.snd;
  __bool_uint32_t_uint32_t scrut1 = deserialize_uint32_t(ok, input, sz1, pos);
  bool ok1 = scrut1.fst;
  uint32_t pos1 = scrut1.snd;
  uint32_t hash_size1 = scrut1.thd;
  __bool_uint32_t_uint64_t scrut2 = deserialize_offset_t(ok1, input, sz1, pos1);
  bool ok2 = scrut2.fst;
  uint32_t pos2 = scrut2.snd;
  uint64_t offset1 = scrut2.thd;
  __bool_uint32_t_uint32_t scrut3 = deserialize_index_t(ok2, input, sz1, pos2);
  bool ok3 = scrut3.fst;
  uint32_t pos3 = scrut3.snd;
  uint32_t i1 = scrut3.thd;
  __bool_uint32_t_uint32_t scrut4 = deserialize_index_t(ok3, input, sz1, pos3);
  bool ok4 = scrut4.fst;
  uint32_t pos4 = scrut4.snd;
  uint32_t j1 = scrut4.thd;
  __bool_uint32_t_LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
  scrut5 = deserialize_hash_vv(ok4, input, sz1, pos4);
  bool ok5 = scrut5.fst;
  uint32_t pos5 = scrut5.snd;
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs = scrut5.thd;
  __bool_uint32_t_bool scrut6 = deserialize_bool(ok5, input, sz1, pos5);
  bool ok6 = scrut6.fst;
  uint32_t pos6 = scrut6.snd;
  bool rhs_ok = scrut6.thd;
  __bool_uint32_t_LowStar_Vector_vector_str___uint8_t_
  scrut7 = deserialize_hash_vec(ok6, input, sz1, pos6);
  bool ok7 = scrut7.fst;
  uint32_t pos7 = scrut7.snd;
  LowStar_Vector_vector_str___uint8_t_ rhs = scrut7.thd;
  __bool_uint32_t__uint8_t_ scrut = deserialize_hash(ok7, input, sz1, pos7);
  bool ok8 = scrut.fst;
  uint8_t *mroot = scrut.thd;
  if
  (
    !ok8
    || hash_size1 != hash_size
    ||
      !(j1
      >= i1
      && uint64_max - offset1 >= (uint64_t)j1
      && hs.sz == (uint32_t)32U
      && rhs.sz == (uint32_t)32U)
  )
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (merkle_tree), (uint32_t)1U);
  merkle_tree *buf = KRML_HOST_MALLOC(sizeof (merkle_tree));
  buf[0U]
  =
    (
      (merkle_tree){
        .offset = offset1,
        .i = i1,
        .j = j1,
        .hs = hs,
        .rhs_ok = rhs_ok,
        .rhs = rhs,
        .mroot = mroot,
        .hash_fun = hash_2
      }
    );
  return buf;
}

uint64_t
mt_serialize_path(
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  const merkle_tree *mt,
  uint8_t *output,
  uint64_t sz
)
{
  uint32_t sz1 = (uint32_t)sz;
  LowStar_Vector_vector_str___uint8_t_ *ncp = (LowStar_Vector_vector_str___uint8_t_ *)p1;
  __bool_uint32_t scrut = serialize_uint32_t(true, hash_size, output, sz1, (uint32_t)0U);
  bool ok = scrut.fst;
  uint32_t pos = scrut.snd;
  __bool_uint32_t scrut0 = serialize_hash_vec(ok, *ncp, output, sz1, pos);
  bool ok1 = scrut0.fst;
  uint32_t pos1 = scrut0.snd;
  if (ok1)
  {
    return (uint64_t)pos1;
  }
  return (uint64_t)0U;
}

LowStar_Vector_vector_str___uint8_t_ *mt_deserialize_path(const uint8_t *input, uint64_t sz)
{
  uint32_t sz1 = (uint32_t)sz;
  __bool_uint32_t_uint32_t scrut0 = deserialize_uint32_t(true, input, sz1, (uint32_t)0U);
  bool ok = scrut0.fst;
  uint32_t pos = scrut0.snd;
  uint32_t hash_size1 = scrut0.thd;
  __bool_uint32_t_LowStar_Vector_vector_str___uint8_t_
  scrut = deserialize_hash_vec(ok, input, sz1, pos);
  bool ok1 = scrut.fst;
  LowStar_Vector_vector_str___uint8_t_ hs = scrut.thd;
  if (!ok1 || hash_size1 != hash_size)
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (LowStar_Vector_vector_str___uint8_t_), (uint32_t)1U);
  LowStar_Vector_vector_str___uint8_t_
  *buf = KRML_HOST_MALLOC(sizeof (LowStar_Vector_vector_str___uint8_t_));
  buf[0U] = hs;
  return buf;
}

