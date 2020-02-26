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
#include "MerkleTree_Low_Datastructures.h"
#include "Hacl_Spec.h"
#include "EverCrypt_Hash.h"


/* SNIPPET_START: hash_size_t */

typedef uint32_t hash_size_t;

/* SNIPPET_END: hash_size_t */

/* SNIPPET_START: offset_t */

typedef uint64_t offset_t;

/* SNIPPET_END: offset_t */

/* SNIPPET_START: index_t */

typedef uint32_t index_t;

/* SNIPPET_END: index_t */

/* SNIPPET_START: LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ */

typedef struct LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t__s
{
  uint32_t sz;
  uint32_t cap;
  LowStar_Vector_vector_str___uint8_t_ *vs;
}
LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_;

/* SNIPPET_END: LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ */

/* SNIPPET_START: MerkleTree_Low_merkle_tree */

typedef struct MerkleTree_Low_merkle_tree_s
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
MerkleTree_Low_merkle_tree;

/* SNIPPET_END: MerkleTree_Low_merkle_tree */

/* SNIPPET_START: merkle_tree */

typedef MerkleTree_Low_merkle_tree merkle_tree;

/* SNIPPET_END: merkle_tree */

/* SNIPPET_START: mt_p */

typedef MerkleTree_Low_merkle_tree *mt_p;

/* SNIPPET_END: mt_p */

/* SNIPPET_START: const_mt_p */

typedef const MerkleTree_Low_merkle_tree *const_mt_p;

/* SNIPPET_END: const_mt_p */

/* SNIPPET_START: mt_init_hash */

/*
  Constructors and destructors for hashes
*/
uint8_t *mt_init_hash(uint32_t hash_size);

/* SNIPPET_END: mt_init_hash */

/* SNIPPET_START: mt_free_hash */

void mt_free_hash(uint32_t hash_size, uint8_t *h1);

/* SNIPPET_END: mt_free_hash */

/* SNIPPET_START: mt_init_path */

/*
  Constructors and destructors for paths
*/
LowStar_Vector_vector_str___uint8_t_ *mt_init_path(uint32_t hash_size);

/* SNIPPET_END: mt_init_path */

/* SNIPPET_START: mt_clear_path */

void mt_clear_path(uint32_t hash_size, LowStar_Vector_vector_str___uint8_t_ *p1);

/* SNIPPET_END: mt_clear_path */

/* SNIPPET_START: mt_free_path */

void mt_free_path(uint32_t hash_size, LowStar_Vector_vector_str___uint8_t_ *p1);

/* SNIPPET_END: mt_free_path */

/* SNIPPET_START: mt_create */

/*
  Construction

  @param[in]  i   The initial hash
*/
MerkleTree_Low_merkle_tree *mt_create(uint8_t *i1);

/* SNIPPET_END: mt_create */

/* SNIPPET_START: mt_create_custom */

/*
  Construction with custom hash functions

  @param[in]  hash_size Hash size (in bytes)
  @param[in]  i         The initial hash
*/
MerkleTree_Low_merkle_tree
*mt_create_custom(
  uint32_t hash_size,
  uint8_t *i1,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
);

/* SNIPPET_END: mt_create_custom */

/* SNIPPET_START: mt_free */

/*
    Destruction

  @param[in]  mt  The Merkle tree
*/
void mt_free(MerkleTree_Low_merkle_tree *mt);

/* SNIPPET_END: mt_free */

/* SNIPPET_START: mt_insert */

/*
  Insertion

  @param[in]  mt  The Merkle tree
  @param[in]  v   The tree does not take ownership of the hash, it makes a copy of its content.

 Note: The content of the hash will be overwritten with an arbitrary value.
*/
void mt_insert(MerkleTree_Low_merkle_tree *mt, uint8_t *v1);

/* SNIPPET_END: mt_insert */

/* SNIPPET_START: mt_insert_pre */

/*
  Precondition predicate for mt_insert
*/
bool mt_insert_pre(const MerkleTree_Low_merkle_tree *mt, uint8_t *v1);

/* SNIPPET_END: mt_insert_pre */

/* SNIPPET_START: mt_get_root */

/*
  Getting the Merkle root

  @param[in]  mt   The Merkle tree
  @param[out] root The Merkle root
*/
void mt_get_root(const MerkleTree_Low_merkle_tree *mt, uint8_t *root);

/* SNIPPET_END: mt_get_root */

/* SNIPPET_START: mt_get_root_pre */

/*
  Precondition predicate for mt_get_root
*/
bool mt_get_root_pre(const MerkleTree_Low_merkle_tree *mt, uint8_t *root);

/* SNIPPET_END: mt_get_root_pre */

/* SNIPPET_START: mt_get_path */

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
uint32_t
mt_get_path(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t idx,
  LowStar_Vector_vector_str___uint8_t_ *path,
  uint8_t *root
);

/* SNIPPET_END: mt_get_path */

/* SNIPPET_START: mt_get_path_pre */

/*
  Precondition predicate for mt_get_path
*/
bool
mt_get_path_pre(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t idx,
  const LowStar_Vector_vector_str___uint8_t_ *path,
  uint8_t *root
);

/* SNIPPET_END: mt_get_path_pre */

/* SNIPPET_START: mt_flush */

/*
  Flush the Merkle tree

  @param[in]  mt   The Merkle tree
*/
void mt_flush(MerkleTree_Low_merkle_tree *mt);

/* SNIPPET_END: mt_flush */

/* SNIPPET_START: mt_flush_pre */

/*
  Precondition predicate for mt_flush
*/
bool mt_flush_pre(const MerkleTree_Low_merkle_tree *mt);

/* SNIPPET_END: mt_flush_pre */

/* SNIPPET_START: mt_flush_to */

/*
  Flush the Merkle tree up to a given index

  @param[in]  mt   The Merkle tree
  @param[in]  idx  The index up to which to flush the tree
*/
void mt_flush_to(MerkleTree_Low_merkle_tree *mt, uint64_t idx);

/* SNIPPET_END: mt_flush_to */

/* SNIPPET_START: mt_flush_to_pre */

/*
  Precondition predicate for mt_flush_to
*/
bool mt_flush_to_pre(const MerkleTree_Low_merkle_tree *mt, uint64_t idx);

/* SNIPPET_END: mt_flush_to_pre */

/* SNIPPET_START: mt_retract_to */

/*
  Retract the Merkle tree down to a given index

  @param[in]  mt   The Merkle tree
  @param[in]  idx  The index to retract the tree to

 Note: The element and idx will remain in the tree.
*/
void mt_retract_to(MerkleTree_Low_merkle_tree *mt, uint64_t idx);

/* SNIPPET_END: mt_retract_to */

/* SNIPPET_START: mt_retract_to_pre */

/*
  Precondition predicate for mt_retract_to
*/
bool mt_retract_to_pre(const MerkleTree_Low_merkle_tree *mt, uint64_t idx);

/* SNIPPET_END: mt_retract_to_pre */

/* SNIPPET_START: mt_verify */

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
bool
mt_verify(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t tgt,
  uint64_t max1,
  const LowStar_Vector_vector_str___uint8_t_ *path,
  uint8_t *root
);

/* SNIPPET_END: mt_verify */

/* SNIPPET_START: mt_verify_pre */

/*
  Precondition predicate for mt_verify
*/
bool
mt_verify_pre(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t tgt,
  uint64_t max1,
  const LowStar_Vector_vector_str___uint8_t_ *path,
  uint8_t *root
);

/* SNIPPET_END: mt_verify_pre */

/* SNIPPET_START: mt_serialize_size */

/*
  Serialization size

  @param[in]  mt   The Merkle tree

  return the number of bytes required to serialize the tree
*/
uint64_t mt_serialize_size(const MerkleTree_Low_merkle_tree *mt);

/* SNIPPET_END: mt_serialize_size */

/* SNIPPET_START: mt_serialize */

/*
  Merkle tree serialization

  @param[in]  mt   The Merkle tree
  @param[out] buf  The buffer to serialize the tree into
  @param[in]  len  Length of buf

  return the number of bytes written

  Note: buf must be a buffer of size mt_serialize_size(mt) or larger, but
  smaller than 2^32 (larger buffers are currently not supported).
*/
uint64_t mt_serialize(const MerkleTree_Low_merkle_tree *mt, uint8_t *buf1, uint64_t len);

/* SNIPPET_END: mt_serialize */

/* SNIPPET_START: mt_deserialize */

/*
  Merkle tree deserialization

  @param[in]  buf  The buffer to deserialize the tree from
  @param[in]  len  Length of buf

  return pointer to the new tree if successful, NULL otherwise

  Note: buf must point to an allocated buffer.
*/
MerkleTree_Low_merkle_tree
*mt_deserialize(
  uint32_t hash_size,
  const uint8_t *buf1,
  uint64_t len,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
);

/* SNIPPET_END: mt_deserialize */

/* SNIPPET_START: mt_serialize_path */

/*
  Path serialization

  @param[in]  path The path
  @param[in]  mt   The Merkle tree the path belongs to
  @param[out] buf  The buffer to serialize the path into
  @param[in]  len  Length of buf

  return the number of bytes written
*/
uint64_t
mt_serialize_path(
  const LowStar_Vector_vector_str___uint8_t_ *path,
  const MerkleTree_Low_merkle_tree *mt,
  uint8_t *buf1,
  uint64_t len
);

/* SNIPPET_END: mt_serialize_path */

/* SNIPPET_START: mt_deserialize_path */

/*
  Path deserialization

  @param[in]  buf  The buffer to deserialize the path from
  @param[in]  len  Length of buf

  return pointer to the new path if successful, NULL otherwise

 Note: buf must point to an allocated buffer.
*/
LowStar_Vector_vector_str___uint8_t_
*mt_deserialize_path(uint32_t hash_size, const uint8_t *buf1, uint64_t len);

/* SNIPPET_END: mt_deserialize_path */

/* SNIPPET_START: MerkleTree_Low_index_t */

typedef uint32_t MerkleTree_Low_index_t;

/* SNIPPET_END: MerkleTree_Low_index_t */

/* SNIPPET_START: MerkleTree_Low_uint32_32_max */

extern uint32_t MerkleTree_Low_uint32_32_max;

/* SNIPPET_END: MerkleTree_Low_uint32_32_max */

/* SNIPPET_START: MerkleTree_Low_uint32_max */

extern uint64_t MerkleTree_Low_uint32_max;

/* SNIPPET_END: MerkleTree_Low_uint32_max */

/* SNIPPET_START: MerkleTree_Low_uint64_max */

extern uint64_t MerkleTree_Low_uint64_max;

/* SNIPPET_END: MerkleTree_Low_uint64_max */

/* SNIPPET_START: MerkleTree_Low_offset_range_limit */

extern uint64_t MerkleTree_Low_offset_range_limit;

/* SNIPPET_END: MerkleTree_Low_offset_range_limit */

/* SNIPPET_START: MerkleTree_Low_offset_t */

typedef uint64_t MerkleTree_Low_offset_t;

/* SNIPPET_END: MerkleTree_Low_offset_t */

/* SNIPPET_START: MerkleTree_Low_merkle_tree_size_lg */

extern uint32_t MerkleTree_Low_merkle_tree_size_lg;

/* SNIPPET_END: MerkleTree_Low_merkle_tree_size_lg */

/* SNIPPET_START: MerkleTree_Low_uu___is_MT */

bool MerkleTree_Low_uu___is_MT(MerkleTree_Low_merkle_tree projectee);

/* SNIPPET_END: MerkleTree_Low_uu___is_MT */

/* SNIPPET_START: MerkleTree_Low___proj__MT__item__hash_size */

uint32_t MerkleTree_Low___proj__MT__item__hash_size(MerkleTree_Low_merkle_tree projectee);

/* SNIPPET_END: MerkleTree_Low___proj__MT__item__hash_size */

/* SNIPPET_START: MerkleTree_Low___proj__MT__item__offset */

uint64_t MerkleTree_Low___proj__MT__item__offset(MerkleTree_Low_merkle_tree projectee);

/* SNIPPET_END: MerkleTree_Low___proj__MT__item__offset */

/* SNIPPET_START: MerkleTree_Low___proj__MT__item__i */

uint32_t MerkleTree_Low___proj__MT__item__i(MerkleTree_Low_merkle_tree projectee);

/* SNIPPET_END: MerkleTree_Low___proj__MT__item__i */

/* SNIPPET_START: MerkleTree_Low___proj__MT__item__j */

uint32_t MerkleTree_Low___proj__MT__item__j(MerkleTree_Low_merkle_tree projectee);

/* SNIPPET_END: MerkleTree_Low___proj__MT__item__j */

/* SNIPPET_START: MerkleTree_Low___proj__MT__item__hs */

LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
MerkleTree_Low___proj__MT__item__hs(MerkleTree_Low_merkle_tree projectee);

/* SNIPPET_END: MerkleTree_Low___proj__MT__item__hs */

/* SNIPPET_START: MerkleTree_Low___proj__MT__item__rhs_ok */

bool MerkleTree_Low___proj__MT__item__rhs_ok(MerkleTree_Low_merkle_tree projectee);

/* SNIPPET_END: MerkleTree_Low___proj__MT__item__rhs_ok */

/* SNIPPET_START: MerkleTree_Low___proj__MT__item__rhs */

LowStar_Vector_vector_str___uint8_t_
MerkleTree_Low___proj__MT__item__rhs(MerkleTree_Low_merkle_tree projectee);

/* SNIPPET_END: MerkleTree_Low___proj__MT__item__rhs */

/* SNIPPET_START: MerkleTree_Low___proj__MT__item__mroot */

uint8_t *MerkleTree_Low___proj__MT__item__mroot(MerkleTree_Low_merkle_tree projectee);

/* SNIPPET_END: MerkleTree_Low___proj__MT__item__mroot */

/* SNIPPET_START: MerkleTree_Low___proj__MT__item__hash_fun */

void
(*MerkleTree_Low___proj__MT__item__hash_fun(MerkleTree_Low_merkle_tree projectee))(
  uint8_t *x0,
  uint8_t *x1,
  uint8_t *x2
);

/* SNIPPET_END: MerkleTree_Low___proj__MT__item__hash_fun */

/* SNIPPET_START: MerkleTree_Low_mt_p */

typedef MerkleTree_Low_merkle_tree *MerkleTree_Low_mt_p;

/* SNIPPET_END: MerkleTree_Low_mt_p */

/* SNIPPET_START: MerkleTree_Low_const_mt_p */

typedef const MerkleTree_Low_merkle_tree *MerkleTree_Low_const_mt_p;

/* SNIPPET_END: MerkleTree_Low_const_mt_p */

/* SNIPPET_START: MerkleTree_Low_merkle_tree_conditions */

bool
MerkleTree_Low_merkle_tree_conditions(
  uint64_t offset1,
  uint32_t i1,
  uint32_t j1,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs,
  bool rhs_ok,
  LowStar_Vector_vector_str___uint8_t_ rhs,
  uint8_t *mroot
);

/* SNIPPET_END: MerkleTree_Low_merkle_tree_conditions */

/* SNIPPET_START: MerkleTree_Low_offset_of */

uint32_t MerkleTree_Low_offset_of(uint32_t i1);

/* SNIPPET_END: MerkleTree_Low_offset_of */

/* SNIPPET_START: MerkleTree_Low_mt_free */

void MerkleTree_Low_mt_free(MerkleTree_Low_merkle_tree *mt);

/* SNIPPET_END: MerkleTree_Low_mt_free */

/* SNIPPET_START: MerkleTree_Low_mt_insert_pre */

bool MerkleTree_Low_mt_insert_pre(const MerkleTree_Low_merkle_tree *mt, uint8_t *v1);

/* SNIPPET_END: MerkleTree_Low_mt_insert_pre */

/* SNIPPET_START: MerkleTree_Low_mt_insert */

void MerkleTree_Low_mt_insert(MerkleTree_Low_merkle_tree *mt, uint8_t *v1);

/* SNIPPET_END: MerkleTree_Low_mt_insert */

/* SNIPPET_START: MerkleTree_Low_mt_create_custom */

MerkleTree_Low_merkle_tree
*MerkleTree_Low_mt_create_custom(
  uint32_t hsz,
  uint8_t *init1,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
);

/* SNIPPET_END: MerkleTree_Low_mt_create_custom */

/* SNIPPET_START: MerkleTree_Low_mt_create */

MerkleTree_Low_merkle_tree *MerkleTree_Low_mt_create(uint8_t *init1);

/* SNIPPET_END: MerkleTree_Low_mt_create */

/* SNIPPET_START: MerkleTree_Low_init_path */

LowStar_Vector_vector_str___uint8_t_ *MerkleTree_Low_init_path(uint32_t hsz);

/* SNIPPET_END: MerkleTree_Low_init_path */

/* SNIPPET_START: MerkleTree_Low_clear_path */

void MerkleTree_Low_clear_path(uint32_t uu____3151, LowStar_Vector_vector_str___uint8_t_ *p1);

/* SNIPPET_END: MerkleTree_Low_clear_path */

/* SNIPPET_START: MerkleTree_Low_free_path */

void MerkleTree_Low_free_path(uint32_t uu____3298, LowStar_Vector_vector_str___uint8_t_ *p1);

/* SNIPPET_END: MerkleTree_Low_free_path */

/* SNIPPET_START: MerkleTree_Low_mt_get_root_pre */

bool MerkleTree_Low_mt_get_root_pre(const MerkleTree_Low_merkle_tree *mt, uint8_t *rt);

/* SNIPPET_END: MerkleTree_Low_mt_get_root_pre */

/* SNIPPET_START: MerkleTree_Low_mt_get_root */

void MerkleTree_Low_mt_get_root(const MerkleTree_Low_merkle_tree *mt, uint8_t *rt);

/* SNIPPET_END: MerkleTree_Low_mt_get_root */

/* SNIPPET_START: MerkleTree_Low_path_insert */

void
MerkleTree_Low_path_insert(uint32_t hsz, LowStar_Vector_vector_str___uint8_t_ *p1, uint8_t *hp);

/* SNIPPET_END: MerkleTree_Low_path_insert */

/* SNIPPET_START: MerkleTree_Low_mt_get_path_pre */

bool
MerkleTree_Low_mt_get_path_pre(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t idx,
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *root
);

/* SNIPPET_END: MerkleTree_Low_mt_get_path_pre */

/* SNIPPET_START: MerkleTree_Low_mt_get_path */

uint32_t
MerkleTree_Low_mt_get_path(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t idx,
  LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *root
);

/* SNIPPET_END: MerkleTree_Low_mt_get_path */

/* SNIPPET_START: MerkleTree_Low_mt_flush_to_pre */

bool MerkleTree_Low_mt_flush_to_pre(const MerkleTree_Low_merkle_tree *mt, uint64_t idx);

/* SNIPPET_END: MerkleTree_Low_mt_flush_to_pre */

/* SNIPPET_START: MerkleTree_Low_mt_flush_to */

void MerkleTree_Low_mt_flush_to(MerkleTree_Low_merkle_tree *mt, uint64_t idx);

/* SNIPPET_END: MerkleTree_Low_mt_flush_to */

/* SNIPPET_START: MerkleTree_Low_mt_flush_pre */

bool MerkleTree_Low_mt_flush_pre(const MerkleTree_Low_merkle_tree *mt);

/* SNIPPET_END: MerkleTree_Low_mt_flush_pre */

/* SNIPPET_START: MerkleTree_Low_mt_flush */

void MerkleTree_Low_mt_flush(MerkleTree_Low_merkle_tree *mt);

/* SNIPPET_END: MerkleTree_Low_mt_flush */

/* SNIPPET_START: MerkleTree_Low_mt_retract_to_pre */

bool MerkleTree_Low_mt_retract_to_pre(const MerkleTree_Low_merkle_tree *mt, uint64_t r);

/* SNIPPET_END: MerkleTree_Low_mt_retract_to_pre */

/* SNIPPET_START: MerkleTree_Low_mt_retract_to */

void MerkleTree_Low_mt_retract_to(MerkleTree_Low_merkle_tree *mt, uint64_t r);

/* SNIPPET_END: MerkleTree_Low_mt_retract_to */

/* SNIPPET_START: MerkleTree_Low_mt_verify_pre */

bool
MerkleTree_Low_mt_verify_pre(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t k1,
  uint64_t j1,
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *rt
);

/* SNIPPET_END: MerkleTree_Low_mt_verify_pre */

/* SNIPPET_START: MerkleTree_Low_mt_verify */

bool
MerkleTree_Low_mt_verify(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t k1,
  uint64_t j1,
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *rt
);

/* SNIPPET_END: MerkleTree_Low_mt_verify */

/* SNIPPET_START: MerkleTree_Low_Serialization_uint8_t */

typedef uint8_t MerkleTree_Low_Serialization_uint8_t;

/* SNIPPET_END: MerkleTree_Low_Serialization_uint8_t */

/* SNIPPET_START: MerkleTree_Low_Serialization_uint16_t */

typedef uint16_t MerkleTree_Low_Serialization_uint16_t;

/* SNIPPET_END: MerkleTree_Low_Serialization_uint16_t */

/* SNIPPET_START: MerkleTree_Low_Serialization_uint32_t */

typedef uint32_t MerkleTree_Low_Serialization_uint32_t;

/* SNIPPET_END: MerkleTree_Low_Serialization_uint32_t */

/* SNIPPET_START: MerkleTree_Low_Serialization_uint64_t */

typedef uint64_t MerkleTree_Low_Serialization_uint64_t;

/* SNIPPET_END: MerkleTree_Low_Serialization_uint64_t */

/* SNIPPET_START: MerkleTree_Low_Serialization_uint8_p */

typedef uint8_t *MerkleTree_Low_Serialization_uint8_p;

/* SNIPPET_END: MerkleTree_Low_Serialization_uint8_p */

/* SNIPPET_START: MerkleTree_Low_Serialization_const_uint8_p */

typedef const uint8_t *MerkleTree_Low_Serialization_const_uint8_p;

/* SNIPPET_END: MerkleTree_Low_Serialization_const_uint8_p */

/* SNIPPET_START: MerkleTree_Low_Serialization_mt_serialize_size */

uint64_t MerkleTree_Low_Serialization_mt_serialize_size(const MerkleTree_Low_merkle_tree *mt);

/* SNIPPET_END: MerkleTree_Low_Serialization_mt_serialize_size */

/* SNIPPET_START: MerkleTree_Low_Serialization_mt_serialize */

uint64_t
MerkleTree_Low_Serialization_mt_serialize(
  const MerkleTree_Low_merkle_tree *mt,
  uint8_t *output,
  uint64_t sz
);

/* SNIPPET_END: MerkleTree_Low_Serialization_mt_serialize */

/* SNIPPET_START: MerkleTree_Low_Serialization_mt_deserialize */

MerkleTree_Low_merkle_tree
*MerkleTree_Low_Serialization_mt_deserialize(
  uint32_t hash_size,
  const uint8_t *input,
  uint64_t sz,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
);

/* SNIPPET_END: MerkleTree_Low_Serialization_mt_deserialize */

/* SNIPPET_START: MerkleTree_Low_Serialization_mt_serialize_path */

uint64_t
MerkleTree_Low_Serialization_mt_serialize_path(
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  const MerkleTree_Low_merkle_tree *mt,
  uint8_t *output,
  uint64_t sz
);

/* SNIPPET_END: MerkleTree_Low_Serialization_mt_serialize_path */

/* SNIPPET_START: MerkleTree_Low_Serialization_mt_deserialize_path */

LowStar_Vector_vector_str___uint8_t_
*MerkleTree_Low_Serialization_mt_deserialize_path(
  uint32_t hsz,
  const uint8_t *input,
  uint64_t sz
);

/* SNIPPET_END: MerkleTree_Low_Serialization_mt_deserialize_path */

/* SNIPPET_START: MerkleTree_Low_Hashfunctions_init_hash */

uint8_t *MerkleTree_Low_Hashfunctions_init_hash(uint32_t hsz);

/* SNIPPET_END: MerkleTree_Low_Hashfunctions_init_hash */

/* SNIPPET_START: MerkleTree_Low_Hashfunctions_free_hash */

void MerkleTree_Low_Hashfunctions_free_hash(uint32_t hsz, uint8_t *h1);

/* SNIPPET_END: MerkleTree_Low_Hashfunctions_free_hash */

/* SNIPPET_START: MerkleTree_Low_Hashfunctions_sha256_compress */

void MerkleTree_Low_Hashfunctions_sha256_compress(uint8_t *src1, uint8_t *src2, uint8_t *dst);

/* SNIPPET_END: MerkleTree_Low_Hashfunctions_sha256_compress */

#define __MerkleTree_H_DEFINED
#endif
