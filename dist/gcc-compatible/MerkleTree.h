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


typedef uint32_t hash_size_t;

typedef uint64_t offset_t;

typedef uint32_t index_t;

typedef struct LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t__s
{
  uint32_t sz;
  uint32_t cap;
  LowStar_Vector_vector_str___uint8_t_ *vs;
}
LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_;

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

typedef MerkleTree_Low_merkle_tree merkle_tree;

typedef MerkleTree_Low_merkle_tree *mt_p;

typedef const MerkleTree_Low_merkle_tree *const_mt_p;

/*
  Constructors and destructors for hashes
*/
uint8_t *mt_init_hash(uint32_t hash_size);

void mt_free_hash(uint32_t hash_size, uint8_t *h1);

/*
  Constructors and destructors for paths
*/
LowStar_Vector_vector_str___uint8_t_ *mt_init_path(uint32_t hash_size);

void mt_clear_path(uint32_t hash_size, LowStar_Vector_vector_str___uint8_t_ *p1);

void mt_free_path(uint32_t hash_size, LowStar_Vector_vector_str___uint8_t_ *p1);

/*
  Construction

  @param[in]  i   The initial hash
*/
MerkleTree_Low_merkle_tree *mt_create(uint8_t *init1);

/*
  Construction with custom hash functions

  @param[in]  hash_size Hash size (in bytes)
  @param[in]  i   The initial hash
*/
MerkleTree_Low_merkle_tree
*mt_create_custom(
  uint32_t hash_size,
  uint8_t *i1,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
);

/*
    Destruction

    @param[in]  mt  The Merkle tree
*/
void mt_free(MerkleTree_Low_merkle_tree *mt);

/*
  Insertion

  param[in]  mt  The Merkle tree
  param[in]  v   The tree does not take ownership of the hash, it makes a copy of its content.

 Note: The content of the hash will be overwritten with an arbitrary value.
*/
void mt_insert(MerkleTree_Low_merkle_tree *mt, uint8_t *v1);

/*
  Precondition predicate for mt_insert
*/
bool mt_insert_pre(const MerkleTree_Low_merkle_tree *mt, uint8_t *v1);

/*
  Getting the Merkle root

  param[in]  mt   The Merkle tree
  param[out] root The Merkle root returned as a hash pointer
*/
void mt_get_root(const MerkleTree_Low_merkle_tree *mt, uint8_t *rt);

/*
  Precondition predicate for mt_get_root
*/
bool mt_get_root_pre(const MerkleTree_Low_merkle_tree *mt, uint8_t *rt);

/*
  Getting a Merkle path

  param[in]  mt   The Merkle tree
  param[in]  idx  The index of the target hash
  param[out] root The Merkle root
  param[out] path A resulting Merkle path that contains the leaf hash.

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
  LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *root
);

/*
  Precondition predicate for mt_get_path
*/
bool
mt_get_path_pre(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t idx,
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *root
);

/*
  Flush the Merkle tree

  param[in]  mt   The Merkle tree
*/
void mt_flush(MerkleTree_Low_merkle_tree *mt);

/*
  Precondition predicate for mt_flush
*/
bool mt_flush_pre(const MerkleTree_Low_merkle_tree *mt);

/*
  Flush the Merkle tree up to a given index
 
  param[in]  mt   The Merkle tree
  param[in]  idx  The index up to which to flush the tree
*/
void mt_flush_to(MerkleTree_Low_merkle_tree *mt, uint64_t idx);

/*
  Precondition predicate for mt_flush_to
*/
bool mt_flush_to_pre(const MerkleTree_Low_merkle_tree *mt, uint64_t idx);

/*
  Retract the Merkle tree down to a given index

  param[in]  mt   The Merkle tree
  param[in]  idx  The index to retract the tree to

 Note: The element and idx will remain in the tree.
*/
void mt_retract_to(MerkleTree_Low_merkle_tree *mt, uint64_t r);

/*
  Precondition predicate for mt_retract_to
*/
bool mt_retract_to_pre(const MerkleTree_Low_merkle_tree *mt, uint64_t r);

/*
  Client-side verification

  param[in]  mt   The Merkle tree
  param[in]  tgt  The index of the target hash
  param[in]  max  The maximum index + 1 of the tree when the path was generated
  param[in]  path The Merkle path to verify
  param[in]  root

  return true if the verification succeeded, false otherwise
  
  Note: max - tgt must be less than 2^32.
*/
bool
mt_verify(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t k1,
  uint64_t j1,
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *rt
);

/*
  Precondition predicate for mt_verify
*/
bool
mt_verify_pre(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t k1,
  uint64_t j1,
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *rt
);

/*
  Serialization size

  param[in]  mt   The Merkle tree

  return the number of bytes required to serialize the tree
*/
uint64_t mt_serialize_size(const MerkleTree_Low_merkle_tree *mt);

/*
  Merkle tree serialization

  param[in]  mt   The Merkle tree
  param[out] buf  The buffer to serialize the tree into
  param[in]  len  Length of buf

  return the number of bytes written

  Note: buf must be a buffer of size mt_serialize_size(mt) or larger, but
  smaller than 2^32 (larger buffers are currently not supported).
*/
uint64_t mt_serialize(const MerkleTree_Low_merkle_tree *mt, uint8_t *output, uint64_t sz);

/*
  Merkle tree deserialization

  param[in]  buf  The buffer to deserialize the tree from
  param[in]  len  Length of buf

  return pointer to the new tree if successful, NULL otherwise

  Note: buf must point to an allocated buffer.
*/
MerkleTree_Low_merkle_tree
*mt_deserialize(
  uint32_t hash_size,
  const uint8_t *input,
  uint64_t sz,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
);

/*
  Path serialization

  param[in]  path The path
  param[in]  mt   The Merkle tree the path belongs to
  param[out] buf  The buffer to serialize the path into
  param[in]  len  Length of buf

  return the number of bytes written
*/
uint64_t
mt_serialize_path(
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  const MerkleTree_Low_merkle_tree *mt,
  uint8_t *output,
  uint64_t sz
);

/*
  Path deserialization

  param[in]  buf  The buffer to deserialize the path from
  param[in]  len  Length of buf

  return pointer to the new path if successful, NULL otherwise
  
 Note: buf must point to an allocated buffer.
*/
LowStar_Vector_vector_str___uint8_t_
*mt_deserialize_path(uint32_t hash_size, const uint8_t *input, uint64_t sz);

typedef uint32_t MerkleTree_Low_index_t;

extern uint32_t MerkleTree_Low_uint32_32_max;

extern uint64_t MerkleTree_Low_uint32_max;

extern uint64_t MerkleTree_Low_uint64_max;

extern uint64_t MerkleTree_Low_offset_range_limit;

typedef uint64_t MerkleTree_Low_offset_t;

extern uint32_t MerkleTree_Low_merkle_tree_size_lg;

bool MerkleTree_Low_uu___is_MT(MerkleTree_Low_merkle_tree projectee);

uint32_t MerkleTree_Low___proj__MT__item__hash_size(MerkleTree_Low_merkle_tree projectee);

uint64_t MerkleTree_Low___proj__MT__item__offset(MerkleTree_Low_merkle_tree projectee);

uint32_t MerkleTree_Low___proj__MT__item__i(MerkleTree_Low_merkle_tree projectee);

uint32_t MerkleTree_Low___proj__MT__item__j(MerkleTree_Low_merkle_tree projectee);

LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_
MerkleTree_Low___proj__MT__item__hs(MerkleTree_Low_merkle_tree projectee);

bool MerkleTree_Low___proj__MT__item__rhs_ok(MerkleTree_Low_merkle_tree projectee);

LowStar_Vector_vector_str___uint8_t_
MerkleTree_Low___proj__MT__item__rhs(MerkleTree_Low_merkle_tree projectee);

uint8_t *MerkleTree_Low___proj__MT__item__mroot(MerkleTree_Low_merkle_tree projectee);

void
(*MerkleTree_Low___proj__MT__item__hash_fun(MerkleTree_Low_merkle_tree projectee))(
  uint8_t *x0,
  uint8_t *x1,
  uint8_t *x2
);

typedef MerkleTree_Low_merkle_tree *MerkleTree_Low_mt_p;

typedef const MerkleTree_Low_merkle_tree *MerkleTree_Low_const_mt_p;

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

uint32_t MerkleTree_Low_offset_of(uint32_t i1);

void MerkleTree_Low_mt_free(MerkleTree_Low_merkle_tree *mt);

bool MerkleTree_Low_mt_insert_pre(const MerkleTree_Low_merkle_tree *mt, uint8_t *v1);

void MerkleTree_Low_mt_insert(MerkleTree_Low_merkle_tree *mt, uint8_t *v1);

MerkleTree_Low_merkle_tree
*MerkleTree_Low_mt_create_custom(
  uint32_t hsz,
  uint8_t *init1,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
);

MerkleTree_Low_merkle_tree *MerkleTree_Low_mt_create(uint8_t *init1);

LowStar_Vector_vector_str___uint8_t_ *MerkleTree_Low_init_path(uint32_t hsz);

void MerkleTree_Low_clear_path(uint32_t uu____3215, LowStar_Vector_vector_str___uint8_t_ *p1);

void MerkleTree_Low_free_path(uint32_t uu____3362, LowStar_Vector_vector_str___uint8_t_ *p1);

bool MerkleTree_Low_mt_get_root_pre(const MerkleTree_Low_merkle_tree *mt, uint8_t *rt);

void MerkleTree_Low_mt_get_root(const MerkleTree_Low_merkle_tree *mt, uint8_t *rt);

void
MerkleTree_Low_path_insert(uint32_t hsz, LowStar_Vector_vector_str___uint8_t_ *p1, uint8_t *hp);

bool
MerkleTree_Low_mt_get_path_pre(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t idx,
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *root
);

uint32_t
MerkleTree_Low_mt_get_path(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t idx,
  LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *root
);

void
MerkleTree_Low_VectorExtras_move_left___uint8_t_(
  uint8_t **b,
  uint32_t dst,
  uint32_t src,
  uint32_t l
);

bool MerkleTree_Low_mt_flush_to_pre(const MerkleTree_Low_merkle_tree *mt, uint64_t idx);

void MerkleTree_Low_mt_flush_to(MerkleTree_Low_merkle_tree *mt, uint64_t idx);

bool MerkleTree_Low_mt_flush_pre(const MerkleTree_Low_merkle_tree *mt);

void MerkleTree_Low_mt_flush(MerkleTree_Low_merkle_tree *mt);

bool MerkleTree_Low_mt_retract_to_pre(const MerkleTree_Low_merkle_tree *mt, uint64_t r);

void MerkleTree_Low_mt_retract_to(MerkleTree_Low_merkle_tree *mt, uint64_t r);

bool
MerkleTree_Low_mt_verify_pre(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t k1,
  uint64_t j1,
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *rt
);

bool
MerkleTree_Low_mt_verify(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t k1,
  uint64_t j1,
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  uint8_t *rt
);

typedef uint8_t MerkleTree_Low_Serialization_uint8_t;

typedef uint16_t MerkleTree_Low_Serialization_uint16_t;

typedef uint32_t MerkleTree_Low_Serialization_uint32_t;

typedef uint64_t MerkleTree_Low_Serialization_uint64_t;

typedef uint8_t *MerkleTree_Low_Serialization_uint8_p;

typedef const uint8_t *MerkleTree_Low_Serialization_const_uint8_p;

uint64_t MerkleTree_Low_Serialization_mt_serialize_size(const MerkleTree_Low_merkle_tree *mt);

uint64_t
MerkleTree_Low_Serialization_mt_serialize(
  const MerkleTree_Low_merkle_tree *mt,
  uint8_t *output,
  uint64_t sz
);

MerkleTree_Low_merkle_tree
*MerkleTree_Low_Serialization_mt_deserialize(
  uint32_t hash_size,
  const uint8_t *input,
  uint64_t sz,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
);

uint64_t
MerkleTree_Low_Serialization_mt_serialize_path(
  const LowStar_Vector_vector_str___uint8_t_ *p1,
  const MerkleTree_Low_merkle_tree *mt,
  uint8_t *output,
  uint64_t sz
);

LowStar_Vector_vector_str___uint8_t_
*MerkleTree_Low_Serialization_mt_deserialize_path(
  uint32_t hsz,
  const uint8_t *input,
  uint64_t sz
);

uint8_t *MerkleTree_Low_Hashfunctions_init_hash(uint32_t hsz);

void MerkleTree_Low_Hashfunctions_free_hash(uint32_t hsz, uint8_t *h1);

void MerkleTree_Low_Hashfunctions_sha256_compress(uint8_t *src1, uint8_t *src2, uint8_t *dst);

#define __MerkleTree_H_DEFINED
#endif
