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

static uint8_t *hash_r_alloc(uint32_t s)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), s);
  uint8_t *buf = KRML_HOST_CALLOC(s, sizeof (uint8_t));
  return buf;
}

static void hash_r_free(uint8_t *v1)
{
  KRML_HOST_FREE(v1);
}

static void hash_copy(uint32_t s, uint8_t *src, uint8_t *dst)
{
  memcpy(dst, src, s * sizeof (src[0U]));
}

static LowStar_Vector_vector_str___uint8_t_ alloc_reserve___uint8_t_(uint32_t len, uint8_t *ia)
{
  KRML_CHECK_SIZE(sizeof (uint8_t *), len);
  uint8_t **buf = KRML_HOST_MALLOC(sizeof (uint8_t *) * len);
  for (uint32_t _i = 0U; _i < len; ++_i)
    buf[_i] = ia;
  return ((LowStar_Vector_vector_str___uint8_t_){ .sz = (uint32_t)0U, .cap = len, .vs = buf });
}

static LowStar_Vector_vector_str___uint8_t_ hash_vec_r_alloc(uint32_t hsz)
{
  return alloc_reserve___uint8_t_((uint32_t)1U, NULL);
}

static void free___uint8_t_(LowStar_Vector_vector_str___uint8_t_ vec)
{
  KRML_HOST_FREE(vec.vs);
}

static void hash_vec_r_free(LowStar_Vector_vector_str___uint8_t_ v1)
{
  free___uint8_t_(v1);
}

/*
  Constructor for hashes
*/
inline uint8_t *mt_init_hash(uint32_t hash_size)
{
  return MerkleTree_Low_Hashfunctions_init_hash(hash_size);
}

/*
  Destructor for hashes
*/
inline void mt_free_hash(uint8_t *h1)
{
  MerkleTree_Low_Hashfunctions_free_hash(h1);
}

/*
  Constructor for paths
*/
inline MerkleTree_Low_path *mt_init_path(uint32_t hash_size)
{
  return MerkleTree_Low_init_path(hash_size);
}

/*
  Destructor for paths
*/
inline void mt_free_path(MerkleTree_Low_path *p1)
{
  MerkleTree_Low_free_path(p1);
}

/*
  Length of a path

  @param[in] p Path  
  
  return The length of the path
*/
inline uint32_t mt_get_path_length(const MerkleTree_Low_path *p1)
{
  return MerkleTree_Low_mt_get_path_length(p1);
}

/*
  Get step on a path

  @param[in] p Path
  @param[in] i Path step index
  
  return The hash at step i of p
*/
inline uint8_t *mt_get_path_step(const MerkleTree_Low_path *p1, uint32_t i1)
{
  return MerkleTree_Low_mt_get_path_step(p1, i1);
}

/*
  Precondition predicate for mt_get_path_step
*/
inline bool mt_get_path_step_pre(const MerkleTree_Low_path *p1, uint32_t i1)
{
  return MerkleTree_Low_mt_get_path_step_pre(p1, i1);
}

/*
  Construction with custom hash functions

  @param[in]  hash_size Hash size (in bytes)
  @param[in]  i         The initial hash
  
  return The new Merkle tree
*/
inline MerkleTree_Low_merkle_tree
*mt_create_custom(
  uint32_t hash_size,
  uint8_t *i1,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
)
{
  return MerkleTree_Low_mt_create_custom(hash_size, i1, hash_fun);
}

/*
    Destruction

  @param[in]  mt  The Merkle tree
*/
inline void mt_free(MerkleTree_Low_merkle_tree *mt)
{
  MerkleTree_Low_mt_free(mt);
}

/*
  Insertion

  @param[in]  mt  The Merkle tree
  @param[in]  v   The tree does not take ownership of the hash, it makes a copy of its content.

 Note: The content of the hash will be overwritten with an arbitrary value.
*/
inline void mt_insert(MerkleTree_Low_merkle_tree *mt, uint8_t *v1)
{
  MerkleTree_Low_mt_insert(mt, v1);
}

/*
  Precondition predicate for mt_insert
*/
inline bool mt_insert_pre(const MerkleTree_Low_merkle_tree *mt, uint8_t *v1)
{
  return MerkleTree_Low_mt_insert_pre(mt, v1);
}

/*
  Getting the Merkle root

  @param[in]  mt   The Merkle tree
  @param[out] root The Merkle root
*/
inline void mt_get_root(const MerkleTree_Low_merkle_tree *mt, uint8_t *root)
{
  MerkleTree_Low_mt_get_root(mt, root);
}

/*
  Precondition predicate for mt_get_root
*/
inline bool mt_get_root_pre(const MerkleTree_Low_merkle_tree *mt, uint8_t *root)
{
  return MerkleTree_Low_mt_get_root_pre(mt, root);
}

/*
  Getting a Merkle path

  @param[in]  mt   The Merkle tree
  @param[in]  idx  The index of the target hash
  @param[out] path A resulting Merkle path that contains the leaf hash.
  @param[out] root The Merkle root

  return The number of elements in the tree

  Notes:
  - The resulting path contains pointers to hashes in the tree, not copies of
    the hash values.
  - idx must be within the currently held indices in the tree (past the
    last flush index).
*/
inline uint32_t
mt_get_path(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t idx,
  MerkleTree_Low_path *path,
  uint8_t *root
)
{
  return MerkleTree_Low_mt_get_path(mt, idx, path, root);
}

/*
  Precondition predicate for mt_get_path
*/
inline bool
mt_get_path_pre(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t idx,
  const MerkleTree_Low_path *path,
  uint8_t *root
)
{
  return MerkleTree_Low_mt_get_path_pre(mt, idx, path, root);
}

/*
  Flush the Merkle tree

  @param[in]  mt   The Merkle tree
*/
inline void mt_flush(MerkleTree_Low_merkle_tree *mt)
{
  MerkleTree_Low_mt_flush(mt);
}

/*
  Precondition predicate for mt_flush
*/
inline bool mt_flush_pre(const MerkleTree_Low_merkle_tree *mt)
{
  return MerkleTree_Low_mt_flush_pre(mt);
}

/*
  Flush the Merkle tree up to a given index

  @param[in]  mt   The Merkle tree
  @param[in]  idx  The index up to which to flush the tree
*/
inline void mt_flush_to(MerkleTree_Low_merkle_tree *mt, uint64_t idx)
{
  MerkleTree_Low_mt_flush_to(mt, idx);
}

/*
  Precondition predicate for mt_flush_to
*/
bool mt_flush_to_pre(const MerkleTree_Low_merkle_tree *mt, uint64_t idx)
{
  return MerkleTree_Low_mt_flush_to_pre(mt, idx);
}

/*
  Retract the Merkle tree down to a given index

  @param[in]  mt   The Merkle tree
  @param[in]  idx  The index to retract the tree to

 Note: The element and idx will remain in the tree.
*/
inline void mt_retract_to(MerkleTree_Low_merkle_tree *mt, uint64_t idx)
{
  MerkleTree_Low_mt_retract_to(mt, idx);
}

/*
  Precondition predicate for mt_retract_to
*/
inline bool mt_retract_to_pre(const MerkleTree_Low_merkle_tree *mt, uint64_t idx)
{
  return MerkleTree_Low_mt_retract_to_pre(mt, idx);
}

/*
  Client-side verification

  @param[in]  mt   The Merkle tree
  @param[in]  tgt  The index of the target hash
  @param[in]  max  The maximum index + 1 of the tree when the path was generated
  @param[in]  path The Merkle path to verify
  @param[in]  root

  return true if the verification succeeded, false otherwise

  Note: max - tgt must be less than 2^32.
*/
inline bool
mt_verify(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t tgt,
  uint64_t max1,
  const MerkleTree_Low_path *path,
  uint8_t *root
)
{
  return MerkleTree_Low_mt_verify(mt, tgt, max1, path, root);
}

/*
  Precondition predicate for mt_verify
*/
inline bool
mt_verify_pre(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t tgt,
  uint64_t max1,
  const MerkleTree_Low_path *path,
  uint8_t *root
)
{
  return MerkleTree_Low_mt_verify_pre(mt, tgt, max1, path, root);
}

/*
  Serialization size

  @param[in]  mt   The Merkle tree

  return the number of bytes required to serialize the tree
*/
inline uint64_t mt_serialize_size(const MerkleTree_Low_merkle_tree *mt)
{
  return MerkleTree_Low_Serialization_mt_serialize_size(mt);
}

/*
  Merkle tree serialization

  @param[in]  mt   The Merkle tree
  @param[out] buf  The buffer to serialize the tree into
  @param[in]  len  Length of buf

  return the number of bytes written

  Note: buf must be a buffer of size mt_serialize_size(mt) or larger, but
  smaller than 2^32 (larger buffers are currently not supported).
*/
inline uint64_t mt_serialize(const MerkleTree_Low_merkle_tree *mt, uint8_t *buf1, uint64_t len)
{
  return MerkleTree_Low_Serialization_mt_serialize(mt, buf1, len);
}

/*
  Merkle tree deserialization

  @param[in]  expected_hash_size Expected hash size to match hash_fun
  @param[in]  buf  The buffer to deserialize the tree from
  @param[in]  len  Length of buf
  @param[in]  hash_fun Hash function

  return pointer to the new tree if successful, NULL otherwise

  Note: buf must point to an allocated buffer.
*/
inline MerkleTree_Low_merkle_tree
*mt_deserialize(
  const uint8_t *buf1,
  uint64_t len,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
)
{
  return MerkleTree_Low_Serialization_mt_deserialize(buf1, len, hash_fun);
}

/*
  Path serialization

  @param[in]  path The path
  @param[out] buf  The buffer to serialize the path into
  @param[in]  len  Length of buf

  return the number of bytes written
*/
inline uint64_t mt_serialize_path(const MerkleTree_Low_path *path, uint8_t *buf1, uint64_t len)
{
  return MerkleTree_Low_Serialization_mt_serialize_path(path, buf1, len);
}

/*
  Path deserialization

  @param[in]  buf  The buffer to deserialize the path from
  @param[in]  len  Length of buf

  return pointer to the new path if successful, NULL otherwise

 Note: buf must point to an allocated buffer.
*/
inline MerkleTree_Low_path
*mt_deserialize_path(uint32_t hash_size, const uint8_t *buf1, uint64_t len)
{
  return MerkleTree_Low_Serialization_mt_deserialize_path(buf1, len);
}

/*
  Default hash function
*/
void mt_sha256_compress(uint8_t *src1, uint8_t *src2, uint8_t *dst)
{
  uint32_t hash_size = (uint32_t)32U;
  Spec_Hash_Definitions_hash_alg hash_alg = Spec_Hash_Definitions_SHA2_256;
  uint8_t cb[64U] = { 0U };
  memcpy(cb, src1, hash_size * sizeof (src1[0U]));
  memcpy(cb + (uint32_t)32U, src2, hash_size * sizeof (src2[0U]));
  uint32_t buf0[4U];
  uint32_t buf1[5U];
  uint32_t buf2[8U];
  uint32_t buf3[8U];
  uint64_t buf4[8U];
  uint64_t buf[8U];
  EverCrypt_Hash_state_s s;
  switch (hash_alg)
  {
    case Spec_Hash_Definitions_MD5:
      {
        uint32_t init = (uint32_t)0U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          buf0[i] = init;
        }
        s = ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_MD5_s, { .case_MD5_s = buf0 } });
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        uint32_t init = (uint32_t)0U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)5U; i++)
        {
          buf1[i] = init;
        }
        s = ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_SHA1_s, { .case_SHA1_s = buf1 } });
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        uint32_t init = (uint32_t)0U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
        {
          buf2[i] = init;
        }
        s =
          (
            (EverCrypt_Hash_state_s){
              .tag = EverCrypt_Hash_SHA2_224_s,
              { .case_SHA2_224_s = buf2 }
            }
          );
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        uint32_t init = (uint32_t)0U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
        {
          buf3[i] = init;
        }
        s =
          (
            (EverCrypt_Hash_state_s){
              .tag = EverCrypt_Hash_SHA2_256_s,
              { .case_SHA2_256_s = buf3 }
            }
          );
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        uint64_t init = (uint64_t)0U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
        {
          buf4[i] = init;
        }
        s =
          (
            (EverCrypt_Hash_state_s){
              .tag = EverCrypt_Hash_SHA2_384_s,
              { .case_SHA2_384_s = buf4 }
            }
          );
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        uint64_t init = (uint64_t)0U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
        {
          buf[i] = init;
        }
        s =
          ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_SHA2_512_s, { .case_SHA2_512_s = buf } });
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  EverCrypt_Hash_state_s st = s;
  EverCrypt_Hash_init(&st);
  EverCrypt_Hash_update(&st, cb);
  EverCrypt_Hash_finish(&st, dst);
}

/*
  Construction wired to sha256 from EverCrypt

  @param[in]  init   The initial hash
*/
inline MerkleTree_Low_merkle_tree *mt_create(uint8_t *init1)
{
  return MerkleTree_Low_mt_create_custom((uint32_t)32U, init1, mt_sha256_compress);
}

uint32_t MerkleTree_Low_uint32_32_max = (uint32_t)4294967295U;

uint64_t MerkleTree_Low_uint32_max = (uint64_t)4294967295U;

uint64_t MerkleTree_Low_uint64_max = (uint64_t)18446744073709551615U;

uint64_t MerkleTree_Low_offset_range_limit = (uint64_t)4294967295U;

uint32_t MerkleTree_Low_merkle_tree_size_lg = (uint32_t)32U;

bool MerkleTree_Low_uu___is_MT(MerkleTree_Low_merkle_tree projectee)
{
  return true;
}

uint32_t MerkleTree_Low___proj__MT__item__hash_size(MerkleTree_Low_merkle_tree projectee)
{
  return projectee.hash_size;
}

uint64_t MerkleTree_Low___proj__MT__item__offset(MerkleTree_Low_merkle_tree projectee)
{
  return projectee.offset;
}

uint32_t MerkleTree_Low___proj__MT__item__i(MerkleTree_Low_merkle_tree projectee)
{
  return projectee.i;
}

uint32_t MerkleTree_Low___proj__MT__item__j(MerkleTree_Low_merkle_tree projectee)
{
  return projectee.j;
}

LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
MerkleTree_Low___proj__MT__item__hs(MerkleTree_Low_merkle_tree projectee)
{
  return projectee.hs;
}

bool MerkleTree_Low___proj__MT__item__rhs_ok(MerkleTree_Low_merkle_tree projectee)
{
  return projectee.rhs_ok;
}

LowStar_Vector_vector_str___uint8_t_
MerkleTree_Low___proj__MT__item__rhs(MerkleTree_Low_merkle_tree projectee)
{
  return projectee.rhs;
}

uint8_t *MerkleTree_Low___proj__MT__item__mroot(MerkleTree_Low_merkle_tree projectee)
{
  return projectee.mroot;
}

void
(*MerkleTree_Low___proj__MT__item__hash_fun(MerkleTree_Low_merkle_tree projectee))(
  uint8_t *x0,
  uint8_t *x1,
  uint8_t *x2
)
{
  return projectee.hash_fun;
}

bool
MerkleTree_Low_merkle_tree_conditions(
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
    && MerkleTree_Low_uint64_max - offset1 >= (uint64_t)j1
    && hs.sz == (uint32_t)32U
    && rhs.sz == (uint32_t)32U;
}

uint32_t MerkleTree_Low_offset_of(uint32_t i1)
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

typedef struct regional__uint32_t_LowStar_Vector_vector_str___uint8_t__s
{
  uint32_t state;
  LowStar_Vector_vector_str___uint8_t_ dummy;
  LowStar_Vector_vector_str___uint8_t_ (*r_alloc)(uint32_t x0);
  void (*r_free)(LowStar_Vector_vector_str___uint8_t_ x0);
}
regional__uint32_t_LowStar_Vector_vector_str___uint8_t_;

static LowStar_Vector_vector_str___uint8_t_
rg_alloc__LowStar_Vector_vector_str__uint8_t__uint32_t(
  regional__uint32_t_LowStar_Vector_vector_str___uint8_t_ rg
)
{
  return rg.r_alloc(rg.state);
}

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
alloc___LowStar_Vector_vector_str__uint8_t__uint32_t(
  regional__uint32_t_LowStar_Vector_vector_str___uint8_t_ rg,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ rv,
  uint32_t cidx
)
{
  if (!(cidx == (uint32_t)0U))
  {
    LowStar_Vector_vector_str___uint8_t_
    v1 = rg_alloc__LowStar_Vector_vector_str__uint8_t__uint32_t(rg);
    assign__LowStar_Vector_vector_str__uint8_t_(rv, cidx - (uint32_t)1U, v1);
    alloc___LowStar_Vector_vector_str__uint8_t__uint32_t(rg, rv, cidx - (uint32_t)1U);
    return;
  }
}

static LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
alloc_rid__LowStar_Vector_vector_str__uint8_t__uint32_t(
  regional__uint32_t_LowStar_Vector_vector_str___uint8_t_ rg,
  uint32_t len
)
{
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
  vec = alloc_rid__LowStar_Vector_vector_str__uint8_t_(len, rg.dummy);
  alloc___LowStar_Vector_vector_str__uint8_t__uint32_t(rg, vec, len);
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

typedef struct regional__uint32_t__uint8_t__s
{
  uint32_t state;
  uint8_t *dummy;
  uint8_t *(*r_alloc)(uint32_t x0);
  void (*r_free)(uint8_t *x0);
}
regional__uint32_t__uint8_t_;

static uint8_t *rg_alloc___uint8_t__uint32_t(regional__uint32_t__uint8_t_ rg)
{
  return rg.r_alloc(rg.state);
}

static void
assign___uint8_t_(LowStar_Vector_vector_str___uint8_t_ vec, uint32_t i1, uint8_t *v1)
{
  (vec.vs + i1)[0U] = v1;
}

static void
alloc____uint8_t__uint32_t(
  regional__uint32_t__uint8_t_ rg,
  LowStar_Vector_vector_str___uint8_t_ rv,
  uint32_t cidx
)
{
  if (!(cidx == (uint32_t)0U))
  {
    uint8_t *v1 = rg_alloc___uint8_t__uint32_t(rg);
    assign___uint8_t_(rv, cidx - (uint32_t)1U, v1);
    alloc____uint8_t__uint32_t(rg, rv, cidx - (uint32_t)1U);
    return;
  }
}

static LowStar_Vector_vector_str___uint8_t_
alloc_rid___uint8_t__uint32_t(regional__uint32_t__uint8_t_ rg, uint32_t len)
{
  LowStar_Vector_vector_str___uint8_t_ vec = alloc_rid___uint8_t_(len, rg.dummy);
  alloc____uint8_t__uint32_t(rg, vec, len);
  return vec;
}

static MerkleTree_Low_merkle_tree
*create_empty_mt(uint32_t hsz, void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2))
{
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
  hs =
    alloc_rid__LowStar_Vector_vector_str__uint8_t__uint32_t((
        (regional__uint32_t_LowStar_Vector_vector_str___uint8_t_){
          .state = hsz,
          .dummy = { .sz = (uint32_t)0U, .cap = (uint32_t)0U, .vs = NULL },
          .r_alloc = hash_vec_r_alloc,
          .r_free = hash_vec_r_free
        }
      ),
      (uint32_t)32U);
  LowStar_Vector_vector_str___uint8_t_
  rhs =
    alloc_rid___uint8_t__uint32_t((
        (regional__uint32_t__uint8_t_){
          .state = hsz,
          .dummy = NULL,
          .r_alloc = hash_r_alloc,
          .r_free = hash_r_free
        }
      ),
      (uint32_t)32U);
  uint8_t
  *mroot =
    rg_alloc___uint8_t__uint32_t((
        (regional__uint32_t__uint8_t_){
          .state = hsz,
          .dummy = NULL,
          .r_alloc = hash_r_alloc,
          .r_free = hash_r_free
        }
      ));
  KRML_CHECK_SIZE(sizeof (MerkleTree_Low_merkle_tree), (uint32_t)1U);
  MerkleTree_Low_merkle_tree *mt = KRML_HOST_MALLOC(sizeof (MerkleTree_Low_merkle_tree));
  mt[0U]
  =
    (
      (MerkleTree_Low_merkle_tree){
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

static LowStar_Vector_vector_str___uint8_t_
index__LowStar_Vector_vector_str__uint8_t_(
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ vec,
  uint32_t i1
)
{
  return vec.vs[i1];
}

static void
rg_free__LowStar_Vector_vector_str__uint8_t__uint32_t(
  regional__uint32_t_LowStar_Vector_vector_str___uint8_t_ rg,
  LowStar_Vector_vector_str___uint8_t_ v1
)
{
  rg.r_free(v1);
}

static void
free_elems__LowStar_Vector_vector_str__uint8_t__uint32_t(
  regional__uint32_t_LowStar_Vector_vector_str___uint8_t_ rg,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ rv,
  uint32_t idx
)
{
  rg_free__LowStar_Vector_vector_str__uint8_t__uint32_t(rg,
    index__LowStar_Vector_vector_str__uint8_t_(rv, idx));
  if (idx != (uint32_t)0U)
  {
    free_elems__LowStar_Vector_vector_str__uint8_t__uint32_t(rg, rv, idx - (uint32_t)1U);
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
free__LowStar_Vector_vector_str__uint8_t__uint32_t(
  regional__uint32_t_LowStar_Vector_vector_str___uint8_t_ rg,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ rv
)
{
  if (!(rv.sz == (uint32_t)0U))
  {
    free_elems__LowStar_Vector_vector_str__uint8_t__uint32_t(rg, rv, rv.sz - (uint32_t)1U);
  }
  free__LowStar_Vector_vector_str__uint8_t_(rv);
}

static uint8_t *index___uint8_t_(LowStar_Vector_vector_str___uint8_t_ vec, uint32_t i1)
{
  return vec.vs[i1];
}

static void rg_free___uint8_t__uint32_t(regional__uint32_t__uint8_t_ rg, uint8_t *v1)
{
  rg.r_free(v1);
}

static void
free_elems___uint8_t__uint32_t(
  regional__uint32_t__uint8_t_ rg,
  LowStar_Vector_vector_str___uint8_t_ rv,
  uint32_t idx
)
{
  rg_free___uint8_t__uint32_t(rg, index___uint8_t_(rv, idx));
  if (idx != (uint32_t)0U)
  {
    free_elems___uint8_t__uint32_t(rg, rv, idx - (uint32_t)1U);
    return;
  }
}

static void
free___uint8_t__uint32_t(
  regional__uint32_t__uint8_t_ rg,
  LowStar_Vector_vector_str___uint8_t_ rv
)
{
  if (!(rv.sz == (uint32_t)0U))
  {
    free_elems___uint8_t__uint32_t(rg, rv, rv.sz - (uint32_t)1U);
  }
  free___uint8_t_(rv);
}

void MerkleTree_Low_mt_free(MerkleTree_Low_merkle_tree *mt)
{
  MerkleTree_Low_merkle_tree mtv = *mt;
  free__LowStar_Vector_vector_str__uint8_t__uint32_t((
      (regional__uint32_t_LowStar_Vector_vector_str___uint8_t_){
        .state = mtv.hash_size,
        .dummy = { .sz = (uint32_t)0U, .cap = (uint32_t)0U, .vs = NULL },
        .r_alloc = hash_vec_r_alloc,
        .r_free = hash_vec_r_free
      }
    ),
    mtv.hs);
  free___uint8_t__uint32_t((
      (regional__uint32_t__uint8_t_){
        .state = mtv.hash_size,
        .dummy = NULL,
        .r_alloc = hash_r_alloc,
        .r_free = hash_r_free
      }
    ),
    mtv.rhs);
  rg_free___uint8_t__uint32_t((
      (regional__uint32_t__uint8_t_){
        .state = mtv.hash_size,
        .dummy = NULL,
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

#define Cpy 0

typedef uint8_t copyable__uint32_t__uint8_t__tags;

typedef void (*copyable__uint32_t__uint8_t_)(uint32_t x0, uint8_t *x1, uint8_t *x2);

static LowStar_Vector_vector_str___uint8_t_
insert_copy___uint8_t__uint32_t(
  regional__uint32_t__uint8_t_ rg,
  void (*cp)(uint32_t x0, uint8_t *x1, uint8_t *x2),
  LowStar_Vector_vector_str___uint8_t_ rv,
  uint8_t *v1
)
{
  uint8_t *nv = rg_alloc___uint8_t__uint32_t(rg);
  cp(rg.state, v1, nv);
  return insert___uint8_t__uint32_t(rv, nv);
}

static void
assign__LowStar_Vector_vector_str__uint8_t__uint32_t(
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ rv,
  uint32_t i1,
  LowStar_Vector_vector_str___uint8_t_ v1
)
{
  assign__LowStar_Vector_vector_str__uint8_t_(rv, i1, v1);
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
  uu____0 = index__LowStar_Vector_vector_str__uint8_t_(hs, lv);
  LowStar_Vector_vector_str___uint8_t_
  ihv =
    insert_copy___uint8_t__uint32_t((
        (regional__uint32_t__uint8_t_){
          .state = hsz,
          .dummy = NULL,
          .r_alloc = hash_r_alloc,
          .r_free = hash_r_free
        }
      ),
      hash_copy,
      uu____0,
      acc);
  assign__LowStar_Vector_vector_str__uint8_t__uint32_t(hs, lv, ihv);
  if (j1 % (uint32_t)2U == (uint32_t)1U)
  {
    LowStar_Vector_vector_str___uint8_t_ lvhs = index__LowStar_Vector_vector_str__uint8_t_(hs, lv);
    hash_fun(index___uint8_t_(lvhs, lvhs.sz - (uint32_t)2U), acc, acc);
    insert_(hsz, lv + (uint32_t)1U, j1 / (uint32_t)2U, hs, acc, hash_fun);
    return;
  }
}

bool MerkleTree_Low_mt_insert_pre(const MerkleTree_Low_merkle_tree *mt, uint8_t *v1)
{
  MerkleTree_Low_merkle_tree mt1 = *(MerkleTree_Low_merkle_tree *)mt;
  return
    mt1.j
    < MerkleTree_Low_uint32_32_max
    && MerkleTree_Low_uint64_max - mt1.offset >= (uint64_t)(mt1.j + (uint32_t)1U);
}

void MerkleTree_Low_mt_insert(MerkleTree_Low_merkle_tree *mt, uint8_t *v1)
{
  MerkleTree_Low_merkle_tree mtv = *mt;
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs = mtv.hs;
  uint32_t hsz1 = mtv.hash_size;
  insert_(hsz1, (uint32_t)0U, mtv.j, hs, v1, mtv.hash_fun);
  *mt
  =
    (
      (MerkleTree_Low_merkle_tree){
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

MerkleTree_Low_merkle_tree
*MerkleTree_Low_mt_create_custom(
  uint32_t hsz,
  uint8_t *init1,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
)
{
  MerkleTree_Low_merkle_tree *mt = create_empty_mt(hsz, hash_fun);
  MerkleTree_Low_mt_insert(mt, init1);
  return mt;
}

bool MerkleTree_Low_uu___is_Path(MerkleTree_Low_path projectee)
{
  return true;
}

uint32_t MerkleTree_Low___proj__Path__item__hash_size(MerkleTree_Low_path projectee)
{
  return projectee.hash_size;
}

LowStar_Vector_vector_str___uint8_t_
MerkleTree_Low___proj__Path__item__hashes(MerkleTree_Low_path projectee)
{
  return projectee.hashes;
}

MerkleTree_Low_path *MerkleTree_Low_init_path(uint32_t hsz)
{
  KRML_CHECK_SIZE(sizeof (MerkleTree_Low_path), (uint32_t)1U);
  MerkleTree_Low_path *buf = KRML_HOST_MALLOC(sizeof (MerkleTree_Low_path));
  buf[0U]
  =
    (
      (MerkleTree_Low_path){
        .hash_size = hsz,
        .hashes = rg_alloc__LowStar_Vector_vector_str__uint8_t__uint32_t((
            (regional__uint32_t_LowStar_Vector_vector_str___uint8_t_){
              .state = hsz,
              .dummy = { .sz = (uint32_t)0U, .cap = (uint32_t)0U, .vs = NULL },
              .r_alloc = hash_vec_r_alloc,
              .r_free = hash_vec_r_free
            }
          ))
      }
    );
  return buf;
}

static LowStar_Vector_vector_str___uint8_t_
clear___uint8_t_(LowStar_Vector_vector_str___uint8_t_ vec)
{
  return
    ((LowStar_Vector_vector_str___uint8_t_){ .sz = (uint32_t)0U, .cap = vec.cap, .vs = vec.vs });
}

void MerkleTree_Low_clear_path(MerkleTree_Low_path *p1)
{
  MerkleTree_Low_path pv = *p1;
  *p1
  = ((MerkleTree_Low_path){ .hash_size = pv.hash_size, .hashes = clear___uint8_t_(pv.hashes) });
}

void MerkleTree_Low_free_path(MerkleTree_Low_path *p1)
{
  MerkleTree_Low_path pv = *p1;
  free___uint8_t_(pv.hashes);
  KRML_HOST_FREE(p1);
}

static void
assign_copy___uint8_t__uint32_t(
  regional__uint32_t__uint8_t_ rg,
  void (*cp)(uint32_t x0, uint8_t *x1, uint8_t *x2),
  LowStar_Vector_vector_str___uint8_t_ rv,
  uint32_t i1,
  uint8_t *v1
)
{
  uint8_t *uu____0 = index___uint8_t_(rv, i1);
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
    uint32_t ofs = MerkleTree_Low_offset_of(i1);
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
          (regional__uint32_t__uint8_t_){
            .state = hsz,
            .dummy = NULL,
            .r_alloc = hash_r_alloc,
            .r_free = hash_r_free
          }
        ),
        hash_copy,
        rhs,
        lv,
        acc);
      hash_fun(index___uint8_t_(index__LowStar_Vector_vector_str__uint8_t_(hs, lv),
          j1 - (uint32_t)1U - ofs),
        acc,
        acc);
    }
    else
    {
      hash_copy(hsz,
        index___uint8_t_(index__LowStar_Vector_vector_str__uint8_t_(hs, lv),
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

bool MerkleTree_Low_mt_get_root_pre(const MerkleTree_Low_merkle_tree *mt, uint8_t *rt)
{
  MerkleTree_Low_merkle_tree *mt1 = (MerkleTree_Low_merkle_tree *)mt;
  MerkleTree_Low_merkle_tree mt2 = *mt1;
  return true;
}

void MerkleTree_Low_mt_get_root(const MerkleTree_Low_merkle_tree *mt, uint8_t *rt)
{
  MerkleTree_Low_merkle_tree *mt1 = (MerkleTree_Low_merkle_tree *)mt;
  MerkleTree_Low_merkle_tree mtv = *mt1;
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
      (MerkleTree_Low_merkle_tree){
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

void MerkleTree_Low_path_insert(uint32_t hsz, MerkleTree_Low_path *p1, uint8_t *hp)
{
  MerkleTree_Low_path pth = *p1;
  LowStar_Vector_vector_str___uint8_t_ pv = pth.hashes;
  LowStar_Vector_vector_str___uint8_t_ ipv = insert___uint8_t_(pv, hp);
  *p1 = ((MerkleTree_Low_path){ .hash_size = hsz, .hashes = ipv });
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

uint32_t MerkleTree_Low_mt_get_path_length(const MerkleTree_Low_path *p1)
{
  MerkleTree_Low_path pd = *(MerkleTree_Low_path *)p1;
  return pd.hashes.sz;
}

bool MerkleTree_Low_mt_get_path_step_pre(const MerkleTree_Low_path *p1, uint32_t i1)
{
  MerkleTree_Low_path *p2 = (MerkleTree_Low_path *)p1;
  MerkleTree_Low_path x0 = *p2;
  LowStar_Vector_vector_str___uint8_t_ scrut = x0.hashes;
  return i1 < scrut.sz;
}

uint8_t *MerkleTree_Low_mt_get_path_step(const MerkleTree_Low_path *p1, uint32_t i1)
{
  MerkleTree_Low_path pd = *(MerkleTree_Low_path *)p1;
  return index___uint8_t_(pd.hashes, i1);
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
  MerkleTree_Low_path *p1,
  bool actd
)
{
  uint32_t ofs = MerkleTree_Low_offset_of(i1);
  if (!(j1 == (uint32_t)0U))
  {
    MerkleTree_Low_path pth = *p1;
    uint32_t ofs1 = MerkleTree_Low_offset_of(i1);
    if (k1 % (uint32_t)2U == (uint32_t)1U)
    {
      uint8_t
      *uu____0 =
        index___uint8_t_(index__LowStar_Vector_vector_str__uint8_t_(hs, lv),
          k1 - (uint32_t)1U - ofs1);
      MerkleTree_Low_path pth1 = *p1;
      LowStar_Vector_vector_str___uint8_t_ pv = pth1.hashes;
      LowStar_Vector_vector_str___uint8_t_ ipv = insert___uint8_t_(pv, uu____0);
      *p1 = ((MerkleTree_Low_path){ .hash_size = hsz, .hashes = ipv });
    }
    else if (!(k1 == j1))
    {
      if (k1 + (uint32_t)1U == j1)
      {
        if (actd)
        {
          uint8_t *uu____1 = index___uint8_t_(rhs, lv);
          MerkleTree_Low_path pth1 = *p1;
          LowStar_Vector_vector_str___uint8_t_ pv = pth1.hashes;
          LowStar_Vector_vector_str___uint8_t_ ipv = insert___uint8_t_(pv, uu____1);
          *p1 = ((MerkleTree_Low_path){ .hash_size = hsz, .hashes = ipv });
        }
      }
      else
      {
        uint8_t
        *uu____2 =
          index___uint8_t_(index__LowStar_Vector_vector_str__uint8_t_(hs, lv),
            k1 + (uint32_t)1U - ofs1);
        MerkleTree_Low_path pth1 = *p1;
        LowStar_Vector_vector_str___uint8_t_ pv = pth1.hashes;
        LowStar_Vector_vector_str___uint8_t_ ipv = insert___uint8_t_(pv, uu____2);
        *p1 = ((MerkleTree_Low_path){ .hash_size = hsz, .hashes = ipv });
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
MerkleTree_Low_mt_get_path_pre(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t idx,
  const MerkleTree_Low_path *p1,
  uint8_t *root
)
{
  MerkleTree_Low_merkle_tree *mt1 = (MerkleTree_Low_merkle_tree *)mt;
  MerkleTree_Low_path *p2 = (MerkleTree_Low_path *)p1;
  MerkleTree_Low_merkle_tree mtv = *mt1;
  MerkleTree_Low_path uu____0 = *p2;
  return
    idx
    >= mtv.offset
    && idx - mtv.offset <= MerkleTree_Low_offset_range_limit
    && uu____0.hash_size == mtv.hash_size
    &&
      mtv.i
      <= (uint32_t)(idx - mtv.offset)
      && (uint32_t)(idx - mtv.offset) < mtv.j
      && uu____0.hashes.sz == (uint32_t)0U;
}

uint32_t
MerkleTree_Low_mt_get_path(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t idx,
  MerkleTree_Low_path *p1,
  uint8_t *root
)
{
  MerkleTree_Low_merkle_tree *ncmt = (MerkleTree_Low_merkle_tree *)mt;
  MerkleTree_Low_mt_get_root(mt, root);
  MerkleTree_Low_merkle_tree mtv = *ncmt;
  uint32_t hsz1 = mtv.hash_size;
  uint32_t idx1 = (uint32_t)(idx - mtv.offset);
  uint32_t i1 = mtv.i;
  uint32_t ofs = MerkleTree_Low_offset_of(mtv.i);
  uint32_t j1 = mtv.j;
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs = mtv.hs;
  LowStar_Vector_vector_str___uint8_t_ rhs = mtv.rhs;
  uint8_t
  *ih =
    index___uint8_t_(index__LowStar_Vector_vector_str__uint8_t_(hs, (uint32_t)0U),
      idx1 - ofs);
  MerkleTree_Low_path pth = *p1;
  LowStar_Vector_vector_str___uint8_t_ pv = pth.hashes;
  LowStar_Vector_vector_str___uint8_t_ ipv = insert___uint8_t_(pv, ih);
  *p1 = ((MerkleTree_Low_path){ .hash_size = hsz1, .hashes = ipv });
  mt_get_path_(mtv.hash_size, (uint32_t)0U, hs, rhs, i1, j1, idx1, p1, false);
  return j1;
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
  uint32_t oi = MerkleTree_Low_offset_of(i1);
  uint32_t opi = MerkleTree_Low_offset_of(pi);
  if (!(oi == opi))
  {
    uint32_t ofs = oi - opi;
    LowStar_Vector_vector_str___uint8_t_ hvec = index__LowStar_Vector_vector_str__uint8_t_(hs, lv);
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
      for (uint32_t i = (uint32_t)0U; i < n_shifted; i++)
      {
        uint8_t *uu____0 = hvec.vs[ofs + i];
        hvec.vs[(uint32_t)0U + i] = uu____0;
      }
      flushed =
        ((LowStar_Vector_vector_str___uint8_t_){ .sz = n_shifted, .cap = hvec.cap, .vs = hvec.vs });
    }
    assign__LowStar_Vector_vector_str__uint8_t__uint32_t(hs, lv, flushed);
    mt_flush_to_(hsz, lv + (uint32_t)1U, hs, pi / (uint32_t)2U, i1 / (uint32_t)2U);
    return;
  }
}

bool MerkleTree_Low_mt_flush_to_pre(const MerkleTree_Low_merkle_tree *mt, uint64_t idx)
{
  MerkleTree_Low_merkle_tree *mt1 = (MerkleTree_Low_merkle_tree *)mt;
  MerkleTree_Low_merkle_tree mtv = *mt1;
  return
    idx
    >= mtv.offset
    && idx - mtv.offset <= MerkleTree_Low_offset_range_limit
    && (uint32_t)(idx - mtv.offset) >= mtv.i && (uint32_t)(idx - mtv.offset) < mtv.j;
}

void MerkleTree_Low_mt_flush_to(MerkleTree_Low_merkle_tree *mt, uint64_t idx)
{
  MerkleTree_Low_merkle_tree mtv = *mt;
  uint64_t offset1 = mtv.offset;
  uint32_t hsz = mtv.hash_size;
  uint32_t idx1 = (uint32_t)(idx - offset1);
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs = mtv.hs;
  mt_flush_to_(hsz, (uint32_t)0U, hs, mtv.i, idx1);
  *mt
  =
    (
      (MerkleTree_Low_merkle_tree){
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

bool MerkleTree_Low_mt_flush_pre(const MerkleTree_Low_merkle_tree *mt)
{
  MerkleTree_Low_merkle_tree uu____0 = *(MerkleTree_Low_merkle_tree *)mt;
  return uu____0.j > uu____0.i;
}

void MerkleTree_Low_mt_flush(MerkleTree_Low_merkle_tree *mt)
{
  MerkleTree_Low_merkle_tree mtv = *mt;
  uint64_t off = mtv.offset;
  uint32_t j1 = mtv.j;
  uint32_t j11 = j1 - (uint32_t)1U;
  uint64_t jo = off + (uint64_t)j11;
  MerkleTree_Low_mt_flush_to(mt, jo);
}

static void
free_elems_from___uint8_t__uint32_t(
  regional__uint32_t__uint8_t_ rg,
  LowStar_Vector_vector_str___uint8_t_ rv,
  uint32_t idx
)
{
  rg_free___uint8_t__uint32_t(rg, index___uint8_t_(rv, idx));
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
  regional__uint32_t__uint8_t_ rg,
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
    LowStar_Vector_vector_str___uint8_t_ hvec = index__LowStar_Vector_vector_str__uint8_t_(hs, lv);
    uint32_t old_len = j1 - MerkleTree_Low_offset_of(i1);
    uint32_t new_len = s - MerkleTree_Low_offset_of(i1);
    LowStar_Vector_vector_str___uint8_t_
    retracted =
      shrink___uint8_t__uint32_t((
          (regional__uint32_t__uint8_t_){
            .state = hsz,
            .dummy = NULL,
            .r_alloc = hash_r_alloc,
            .r_free = hash_r_free
          }
        ),
        hvec,
        new_len);
    assign__LowStar_Vector_vector_str__uint8_t__uint32_t(hs, lv, retracted);
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

bool MerkleTree_Low_mt_retract_to_pre(const MerkleTree_Low_merkle_tree *mt, uint64_t r)
{
  MerkleTree_Low_merkle_tree *mt1 = (MerkleTree_Low_merkle_tree *)mt;
  MerkleTree_Low_merkle_tree mtv = *mt1;
  return
    r
    >= mtv.offset
    && r - mtv.offset <= MerkleTree_Low_offset_range_limit
    && mtv.i <= (uint32_t)(r - mtv.offset) && (uint32_t)(r - mtv.offset) < mtv.j;
}

void MerkleTree_Low_mt_retract_to(MerkleTree_Low_merkle_tree *mt, uint64_t r)
{
  MerkleTree_Low_merkle_tree mtv = *mt;
  uint64_t offset1 = mtv.offset;
  uint32_t r1 = (uint32_t)(r - offset1);
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs = mtv.hs;
  mt_retract_to_(mtv.hash_size, hs, (uint32_t)0U, mtv.i, r1 + (uint32_t)1U, mtv.j);
  *mt
  =
    (
      (MerkleTree_Low_merkle_tree){
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
  const MerkleTree_Low_path *p1,
  uint32_t ppos,
  uint8_t *acc,
  bool actd,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
)
{
  MerkleTree_Low_path *ncp = (MerkleTree_Low_path *)p1;
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
      MerkleTree_Low_path ncpd = *ncp;
      uint8_t *phash = index___uint8_t_(ncpd.hashes, ppos);
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
    MerkleTree_Low_path ncpd = *ncp;
    uint8_t *phash = index___uint8_t_(ncpd.hashes, ppos);
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
MerkleTree_Low_mt_verify_pre(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t k1,
  uint64_t j1,
  const MerkleTree_Low_path *p1,
  uint8_t *rt
)
{
  MerkleTree_Low_merkle_tree *mt1 = (MerkleTree_Low_merkle_tree *)mt;
  MerkleTree_Low_path *p2 = (MerkleTree_Low_path *)p1;
  MerkleTree_Low_merkle_tree mtv = *mt1;
  MerkleTree_Low_path uu____0 = *p2;
  return
    k1
    < j1
    && k1 >= mtv.offset && k1 - mtv.offset <= MerkleTree_Low_offset_range_limit
    && j1 >= mtv.offset && j1 - mtv.offset <= MerkleTree_Low_offset_range_limit
    && mtv.hash_size == uu____0.hash_size
    &&
      uu____0.hashes.sz
      ==
        (uint32_t)1U
        +
          mt_path_length((uint32_t)0U,
            (uint32_t)(k1 - mtv.offset),
            (uint32_t)(j1 - mtv.offset),
            false);
}

bool
MerkleTree_Low_mt_verify(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t k1,
  uint64_t j1,
  const MerkleTree_Low_path *p1,
  uint8_t *rt
)
{
  MerkleTree_Low_merkle_tree *ncmt = (MerkleTree_Low_merkle_tree *)mt;
  MerkleTree_Low_path *ncp = (MerkleTree_Low_path *)p1;
  MerkleTree_Low_merkle_tree mtv = *ncmt;
  uint32_t hash_size = mtv.hash_size;
  regional__uint32_t__uint8_t_
  hrg = { .state = hash_size, .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free };
  uint32_t k2 = (uint32_t)(k1 - mtv.offset);
  uint32_t j2 = (uint32_t)(j1 - mtv.offset);
  uint8_t *ih = rg_alloc___uint8_t__uint32_t(hrg);
  MerkleTree_Low_path pth = *ncp;
  uint8_t *first = index___uint8_t_(pth.hashes, (uint32_t)0U);
  hash_copy(hash_size, first, ih);
  mt_verify_(hash_size, k2, j2, p1, (uint32_t)1U, ih, false, mtv.hash_fun);
  uint8_t res = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < hash_size; i++)
  {
    uint8_t uu____0 = FStar_UInt8_eq_mask(ih[i], rt[i]);
    res = uu____0 & res;
  }
  uint8_t z = res;
  bool r = z == (uint8_t)255U;
  rg_free___uint8_t__uint32_t(hrg, ih);
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
  uint32_t hash_size,
  bool ok,
  uint8_t *x,
  uint8_t *buf1,
  uint32_t sz,
  uint32_t pos,
  uint32_t i1
)
{
  if (!ok || pos >= sz)
  {
    return ((__bool_uint32_t){ .fst = false, .snd = (uint32_t)0U });
  }
  uint8_t b = x[i1];
  __bool_uint32_t scrut = serialize_uint8_t(ok, b, buf1, sz, pos);
  bool ok1 = scrut.fst;
  uint32_t pos1 = scrut.snd;
  uint32_t j1 = i1 + (uint32_t)1U;
  if (j1 < hash_size)
  {
    return serialize_hash_i(hash_size, ok1, x, buf1, sz, pos1, j1);
  }
  return ((__bool_uint32_t){ .fst = ok1, .snd = pos1 });
}

static __bool_uint32_t
serialize_hash(
  uint32_t hash_size,
  bool ok,
  uint8_t *x,
  uint8_t *buf1,
  uint32_t sz,
  uint32_t pos
)
{
  if (!ok || pos >= sz)
  {
    return ((__bool_uint32_t){ .fst = false, .snd = (uint32_t)0U });
  }
  return serialize_hash_i(hash_size, ok, x, buf1, sz, pos, (uint32_t)0U);
}

static __bool_uint32_t
serialize_hash_vec_i(
  uint32_t hash_size,
  bool ok,
  LowStar_Vector_vector_str___uint8_t_ x,
  uint8_t *buf1,
  uint32_t sz,
  uint32_t pos,
  uint32_t i1
)
{
  if (!ok || pos >= sz)
  {
    return ((__bool_uint32_t){ .fst = false, .snd = (uint32_t)0U });
  }
  uint8_t *vi = index___uint8_t_(x, i1);
  __bool_uint32_t scrut = serialize_hash(hash_size, ok, vi, buf1, sz, pos);
  bool ok1 = scrut.fst;
  uint32_t pos1 = scrut.snd;
  uint32_t j1 = i1 + (uint32_t)1U;
  if (j1 < x.sz)
  {
    return serialize_hash_vec_i(hash_size, ok1, x, buf1, sz, pos1, j1);
  }
  return ((__bool_uint32_t){ .fst = ok1, .snd = pos1 });
}

static __bool_uint32_t
serialize_hash_vec(
  uint32_t hash_size,
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
    return serialize_hash_vec_i(hash_size, ok1, x, buf1, sz, pos1, (uint32_t)0U);
  }
  return ((__bool_uint32_t){ .fst = ok1, .snd = pos1 });
}

static uint64_t
hash_vv_bytes_i(
  uint32_t hash_size,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ vv1,
  uint32_t i1
)
{
  if (i1 >= vv1.sz)
  {
    return (uint64_t)4U;
  }
  LowStar_Vector_vector_str___uint8_t_ vvi = index__LowStar_Vector_vector_str__uint8_t_(vv1, i1);
  uint64_t vs_hs = (uint64_t)vvi.sz * (uint64_t)hash_size;
  uint64_t r;
  if (MerkleTree_Low_uint64_max - vs_hs >= (uint64_t)4U)
  {
    r = vs_hs + (uint64_t)4U;
  }
  else
  {
    r = MerkleTree_Low_uint64_max;
  }
  uint64_t rest = hash_vv_bytes_i(hash_size, vv1, i1 + (uint32_t)1U);
  if (MerkleTree_Low_uint64_max - r >= rest)
  {
    return r + rest;
  }
  return MerkleTree_Low_uint64_max;
}

static __bool_uint32_t
serialize_hash_vv_i(
  uint32_t hash_size,
  bool ok,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ x,
  uint8_t *buf1,
  uint32_t sz,
  uint32_t pos,
  uint32_t i1
)
{
  if (!ok || pos >= sz)
  {
    return ((__bool_uint32_t){ .fst = false, .snd = (uint32_t)0U });
  }
  LowStar_Vector_vector_str___uint8_t_ vi = index__LowStar_Vector_vector_str__uint8_t_(x, i1);
  __bool_uint32_t scrut = serialize_hash_vec(hash_size, ok, vi, buf1, sz, pos);
  bool ok1 = scrut.fst;
  uint32_t pos1 = scrut.snd;
  uint32_t j1 = i1 + (uint32_t)1U;
  if (j1 < x.sz)
  {
    return serialize_hash_vv_i(hash_size, ok1, x, buf1, sz, pos1, j1);
  }
  return ((__bool_uint32_t){ .fst = ok1, .snd = pos1 });
}

static __bool_uint32_t
serialize_hash_vv(
  uint32_t hash_size,
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
    return serialize_hash_vv_i(hash_size, ok1, x, buf1, sz, pos1, (uint32_t)0U);
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
deserialize_hash(uint32_t hash_size, bool ok, const uint8_t *buf1, uint32_t sz, uint32_t pos)
{
  regional__uint32_t__uint8_t_
  rg = { .state = hash_size, .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free };
  if (!ok || pos >= sz)
  {
    return ((__bool_uint32_t__uint8_t_){ .fst = false, .snd = pos, .thd = rg.dummy });
  }
  if (sz - pos < hash_size)
  {
    return ((__bool_uint32_t__uint8_t_){ .fst = false, .snd = pos, .thd = rg.dummy });
  }
  uint8_t *hash1 = rg_alloc___uint8_t__uint32_t(rg);
  memcpy(hash1, (uint8_t *)buf1 + pos, hash_size * sizeof (((uint8_t *)buf1)[0U]));
  return ((__bool_uint32_t__uint8_t_){ .fst = true, .snd = pos + hash_size, .thd = hash1 });
}

static __bool_uint32_t
deserialize_hash_vec_i(
  uint32_t hash_size,
  bool ok,
  const uint8_t *buf1,
  uint32_t sz,
  uint32_t pos,
  LowStar_Vector_vector_str___uint8_t_ res,
  uint32_t i1
)
{
  if (!ok || pos >= sz)
  {
    return ((__bool_uint32_t){ .fst = false, .snd = pos });
  }
  __bool_uint32_t__uint8_t_ scrut = deserialize_hash(hash_size, ok, buf1, sz, pos);
  bool ok1 = scrut.fst;
  uint32_t pos1 = scrut.snd;
  uint8_t *h1 = scrut.thd;
  if (!ok1)
  {
    return ((__bool_uint32_t){ .fst = false, .snd = pos1 });
  }
  assign___uint8_t_(res, i1, h1);
  uint32_t j1 = i1 + (uint32_t)1U;
  if (j1 < res.sz)
  {
    return deserialize_hash_vec_i(hash_size, ok1, buf1, sz, pos1, res, j1);
  }
  return ((__bool_uint32_t){ .fst = true, .snd = pos1 });
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
deserialize_hash_vec(
  uint32_t hash_size,
  bool ok,
  const uint8_t *buf1,
  uint32_t sz,
  uint32_t pos
)
{
  regional__uint32_t_LowStar_Vector_vector_str___uint8_t_
  rg =
    {
      .state = hash_size,
      .dummy = { .sz = (uint32_t)0U, .cap = (uint32_t)0U, .vs = NULL },
      .r_alloc = hash_vec_r_alloc,
      .r_free = hash_vec_r_free
    };
  if (!ok || pos >= sz)
  {
    return
      (
        (__bool_uint32_t_LowStar_Vector_vector_str___uint8_t_){
          .fst = false,
          .snd = pos,
          .thd = rg.dummy
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
  regional__uint32_t__uint8_t_
  hrg = { .state = hash_size, .dummy = NULL, .r_alloc = hash_r_alloc, .r_free = hash_r_free };
  LowStar_Vector_vector_str___uint8_t_ res = alloc___uint8_t_(n1, hrg.dummy);
  __bool_uint32_t
  scrut = deserialize_hash_vec_i(hash_size, ok1, buf1, sz, pos1, res, (uint32_t)0U);
  bool ok2 = scrut.fst;
  uint32_t pos2 = scrut.snd;
  return
    ((__bool_uint32_t_LowStar_Vector_vector_str___uint8_t_){ .fst = ok2, .snd = pos2, .thd = res });
}

static __bool_uint32_t
deserialize_hash_vv_i(
  uint32_t hash_size,
  bool ok,
  const uint8_t *buf1,
  uint32_t sz,
  uint32_t pos,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ res,
  uint32_t i1
)
{
  if (!ok || pos >= sz)
  {
    return ((__bool_uint32_t){ .fst = false, .snd = (uint32_t)0U });
  }
  __bool_uint32_t_LowStar_Vector_vector_str___uint8_t_
  scrut = deserialize_hash_vec(hash_size, ok, buf1, sz, pos);
  bool ok1 = scrut.fst;
  uint32_t pos1 = scrut.snd;
  LowStar_Vector_vector_str___uint8_t_ hv = scrut.thd;
  if (!ok1)
  {
    return ((__bool_uint32_t){ .fst = false, .snd = pos1 });
  }
  assign__LowStar_Vector_vector_str__uint8_t_(res, i1, hv);
  uint32_t j1 = i1 + (uint32_t)1U;
  if (j1 == res.sz)
  {
    return ((__bool_uint32_t){ .fst = true, .snd = pos1 });
  }
  return deserialize_hash_vv_i(hash_size, ok1, buf1, sz, pos1, res, j1);
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
deserialize_hash_vv(
  uint32_t hash_size,
  bool ok,
  const uint8_t *buf1,
  uint32_t sz,
  uint32_t pos
)
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
  regional__uint32_t_LowStar_Vector_vector_str___uint8_t_
  rg =
    {
      .state = hash_size,
      .dummy = { .sz = (uint32_t)0U, .cap = (uint32_t)0U, .vs = NULL },
      .r_alloc = hash_vec_r_alloc,
      .r_free = hash_vec_r_free
    };
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
  res = alloc__LowStar_Vector_vector_str__uint8_t_(n1, rg.dummy);
  __bool_uint32_t
  scrut = deserialize_hash_vv_i(hash_size, ok1, buf1, sz, pos1, res, (uint32_t)0U);
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

uint64_t MerkleTree_Low_Serialization_mt_serialize_size(const MerkleTree_Low_merkle_tree *mt)
{
  MerkleTree_Low_merkle_tree mtv = *(MerkleTree_Low_merkle_tree *)mt;
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs = mtv.hs;
  LowStar_Vector_vector_str___uint8_t_ rhs = mtv.rhs;
  uint64_t hs_sz = hash_vv_bytes_i(mtv.hash_size, hs, (uint32_t)0U);
  if (hs_sz < (uint64_t)4294967295U)
  {
    uint64_t vs_hs = (uint64_t)rhs.sz * (uint64_t)mtv.hash_size;
    uint64_t ite;
    if (MerkleTree_Low_uint64_max - vs_hs >= (uint64_t)4U)
    {
      ite = vs_hs + (uint64_t)4U;
    }
    else
    {
      ite = MerkleTree_Low_uint64_max;
    }
    return (uint64_t)21U + hs_sz + (uint64_t)1U + ite + (uint64_t)mtv.hash_size;
  }
  return MerkleTree_Low_uint64_max;
}

uint64_t
MerkleTree_Low_Serialization_mt_serialize(
  const MerkleTree_Low_merkle_tree *mt,
  uint8_t *output,
  uint64_t sz
)
{
  MerkleTree_Low_merkle_tree *mt1 = (MerkleTree_Low_merkle_tree *)mt;
  uint32_t sz1 = (uint32_t)sz;
  MerkleTree_Low_merkle_tree mtv = *mt1;
  __bool_uint32_t scrut = serialize_uint8_t(true, (uint8_t)1U, output, sz1, (uint32_t)0U);
  bool ok = scrut.fst;
  uint32_t pos = scrut.snd;
  __bool_uint32_t scrut0 = serialize_uint32_t(ok, mtv.hash_size, output, sz1, pos);
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
  __bool_uint32_t scrut4 = serialize_hash_vv(mtv.hash_size, ok4, mtv.hs, output, sz1, pos4);
  bool ok5 = scrut4.fst;
  uint32_t pos5 = scrut4.snd;
  __bool_uint32_t scrut5 = serialize_bool(ok5, mtv.rhs_ok, output, sz1, pos5);
  bool ok6 = scrut5.fst;
  uint32_t pos6 = scrut5.snd;
  __bool_uint32_t scrut6 = serialize_hash_vec(mtv.hash_size, ok6, mtv.rhs, output, sz1, pos6);
  bool ok7 = scrut6.fst;
  uint32_t pos7 = scrut6.snd;
  __bool_uint32_t scrut7 = serialize_hash(mtv.hash_size, ok7, mtv.mroot, output, sz1, pos7);
  bool ok8 = scrut7.fst;
  uint32_t pos8 = scrut7.snd;
  if (ok8)
  {
    return (uint64_t)pos8;
  }
  return (uint64_t)0U;
}

MerkleTree_Low_merkle_tree
*MerkleTree_Low_Serialization_mt_deserialize(
  const uint8_t *input,
  uint64_t sz,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
)
{
  uint32_t sz1 = (uint32_t)sz;
  __bool_uint32_t_uint8_t scrut0 = deserialize_uint8_t(true, input, sz1, (uint32_t)0U);
  bool ok = scrut0.fst;
  uint32_t pos = scrut0.snd;
  uint8_t format_version = scrut0.thd;
  bool ok1 = ok && format_version == (uint8_t)1U;
  __bool_uint32_t_uint32_t scrut1 = deserialize_uint32_t(ok1, input, sz1, pos);
  bool ok2 = scrut1.fst;
  uint32_t pos1 = scrut1.snd;
  uint32_t hsz = scrut1.thd;
  if (hsz == (uint32_t)0U)
  {
    return NULL;
  }
  __bool_uint32_t_uint64_t scrut2 = deserialize_offset_t(ok2, input, sz1, pos1);
  bool ok3 = scrut2.fst;
  uint32_t pos2 = scrut2.snd;
  uint64_t offset1 = scrut2.thd;
  __bool_uint32_t_uint32_t scrut3 = deserialize_index_t(ok3, input, sz1, pos2);
  bool ok4 = scrut3.fst;
  uint32_t pos3 = scrut3.snd;
  uint32_t i1 = scrut3.thd;
  __bool_uint32_t_uint32_t scrut4 = deserialize_index_t(ok4, input, sz1, pos3);
  bool ok5 = scrut4.fst;
  uint32_t pos4 = scrut4.snd;
  uint32_t j1 = scrut4.thd;
  __bool_uint32_t_LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
  scrut5 = deserialize_hash_vv(hsz, ok5, input, sz1, pos4);
  bool ok6 = scrut5.fst;
  uint32_t pos5 = scrut5.snd;
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs = scrut5.thd;
  __bool_uint32_t_bool scrut6 = deserialize_bool(ok6, input, sz1, pos5);
  bool ok7 = scrut6.fst;
  uint32_t pos6 = scrut6.snd;
  bool rhs_ok = scrut6.thd;
  __bool_uint32_t_LowStar_Vector_vector_str___uint8_t_
  scrut7 = deserialize_hash_vec(hsz, ok7, input, sz1, pos6);
  bool ok8 = scrut7.fst;
  uint32_t pos7 = scrut7.snd;
  LowStar_Vector_vector_str___uint8_t_ rhs = scrut7.thd;
  __bool_uint32_t__uint8_t_ scrut = deserialize_hash(hsz, ok8, input, sz1, pos7);
  bool ok9 = scrut.fst;
  uint8_t *mroot = scrut.thd;
  if
  (
    !ok9
    ||
      !(j1
      >= i1
      && MerkleTree_Low_uint64_max - offset1 >= (uint64_t)j1
      && hs.sz == (uint32_t)32U
      && rhs.sz == (uint32_t)32U)
  )
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (MerkleTree_Low_merkle_tree), (uint32_t)1U);
  MerkleTree_Low_merkle_tree *buf = KRML_HOST_MALLOC(sizeof (MerkleTree_Low_merkle_tree));
  buf[0U]
  =
    (
      (MerkleTree_Low_merkle_tree){
        .hash_size = hsz,
        .offset = offset1,
        .i = i1,
        .j = j1,
        .hs = hs,
        .rhs_ok = rhs_ok,
        .rhs = rhs,
        .mroot = mroot,
        .hash_fun = hash_fun
      }
    );
  return buf;
}

uint64_t
MerkleTree_Low_Serialization_mt_serialize_path(
  const MerkleTree_Low_path *p1,
  uint8_t *output,
  uint64_t sz
)
{
  MerkleTree_Low_path x0 = *(MerkleTree_Low_path *)p1;
  uint32_t hsz1 = x0.hash_size;
  uint32_t sz1 = (uint32_t)sz;
  MerkleTree_Low_path *ncp = (MerkleTree_Low_path *)p1;
  __bool_uint32_t scrut = serialize_uint32_t(true, hsz1, output, sz1, (uint32_t)0U);
  bool ok = scrut.fst;
  uint32_t pos = scrut.snd;
  MerkleTree_Low_path ncpd = *ncp;
  __bool_uint32_t scrut0 = serialize_hash_vec(hsz1, ok, ncpd.hashes, output, sz1, pos);
  bool ok1 = scrut0.fst;
  uint32_t pos1 = scrut0.snd;
  if (ok1)
  {
    return (uint64_t)pos1;
  }
  return (uint64_t)0U;
}

MerkleTree_Low_path
*MerkleTree_Low_Serialization_mt_deserialize_path(const uint8_t *input, uint64_t sz)
{
  uint32_t sz1 = (uint32_t)sz;
  __bool_uint32_t_uint32_t scrut0 = deserialize_uint32_t(true, input, sz1, (uint32_t)0U);
  bool ok = scrut0.fst;
  uint32_t pos = scrut0.snd;
  uint32_t hash_size = scrut0.thd;
  if (!ok || hash_size == (uint32_t)0U)
  {
    return NULL;
  }
  __bool_uint32_t_LowStar_Vector_vector_str___uint8_t_
  scrut = deserialize_hash_vec(hash_size, ok, input, sz1, pos);
  bool ok1 = scrut.fst;
  LowStar_Vector_vector_str___uint8_t_ hs = scrut.thd;
  if (!ok1)
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (MerkleTree_Low_path), (uint32_t)1U);
  MerkleTree_Low_path *buf = KRML_HOST_MALLOC(sizeof (MerkleTree_Low_path));
  buf[0U] = ((MerkleTree_Low_path){ .hash_size = hash_size, .hashes = hs });
  return buf;
}

uint8_t *MerkleTree_Low_Hashfunctions_init_hash(uint32_t hsz)
{
  return
    rg_alloc___uint8_t__uint32_t((
        (regional__uint32_t__uint8_t_){
          .state = hsz,
          .dummy = NULL,
          .r_alloc = hash_r_alloc,
          .r_free = hash_r_free
        }
      ));
}

void MerkleTree_Low_Hashfunctions_free_hash(uint8_t *h1)
{
  hash_r_free(h1);
}

