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


#ifndef __MerkleTree_H
#define __MerkleTree_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_Spec.h"
#include "EverCrypt_Hash.h"

typedef struct LowStar_Vector_vector_str___uint8_t__s
{
  uint32_t sz;
  uint32_t cap;
  uint8_t **vs;
}
LowStar_Vector_vector_str___uint8_t_;

typedef uint32_t hash_size_t;

typedef uint64_t offset_t;

typedef uint32_t index_t;

typedef struct MerkleTree_Low_path_s
{
  uint32_t hash_size;
  LowStar_Vector_vector_str___uint8_t_ hashes;
}
MerkleTree_Low_path;

typedef MerkleTree_Low_path path;

typedef MerkleTree_Low_path *path_p;

typedef const MerkleTree_Low_path *const_path_p;

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
  Constructor for hashes
*/
uint8_t *mt_init_hash(uint32_t hash_size);

/*
  Destructor for hashes
*/
void mt_free_hash(uint8_t *h);

/*
  Constructor for paths
*/
MerkleTree_Low_path *mt_init_path(uint32_t hash_size);

/*
  Destructor for paths
*/
void mt_free_path(MerkleTree_Low_path *path1);

/*
  Length of a path

  @param[in] p Path

  return The length of the path
*/
uint32_t mt_get_path_length(const MerkleTree_Low_path *path1);

/*
  Insert hash into path

  @param[in] p Path
  @param[in] hash Hash to insert
*/
void mt_path_insert(MerkleTree_Low_path *path1, uint8_t *hash1);

/*
  Get step on a path

  @param[in] p Path
  @param[in] i Path step index

  return The hash at step i of p
*/
uint8_t *mt_get_path_step(const MerkleTree_Low_path *path1, uint32_t i);

/*
  Precondition predicate for mt_get_path_step
*/
bool mt_get_path_step_pre(const MerkleTree_Low_path *path1, uint32_t i);

/*
  Construction with custom hash functions

  @param[in]  hash_size Hash size (in bytes)
  @param[in]  i         The initial hash

  return The new Merkle tree
*/
MerkleTree_Low_merkle_tree
*mt_create_custom(
  uint32_t hash_size,
  uint8_t *i,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
);

/*
  Destruction

  @param[in]  mt  The Merkle tree
*/
void mt_free(MerkleTree_Low_merkle_tree *mt);

/*
  Insertion

  @param[in]  mt  The Merkle tree
  @param[in]  v   The tree does not take ownership of the hash, it makes a copy of its content.

 Note: The content of the hash will be overwritten with an arbitrary value.
*/
void mt_insert(MerkleTree_Low_merkle_tree *mt, uint8_t *v);

/*
  Precondition predicate for mt_insert
*/
bool mt_insert_pre(const MerkleTree_Low_merkle_tree *mt, uint8_t *v);

/*
  Getting the Merkle root

  @param[in]  mt   The Merkle tree
  @param[out] root The Merkle root
*/
void mt_get_root(const MerkleTree_Low_merkle_tree *mt, uint8_t *root);

/*
  Precondition predicate for mt_get_root
*/
bool mt_get_root_pre(const MerkleTree_Low_merkle_tree *mt, uint8_t *root);

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
  MerkleTree_Low_path *path1,
  uint8_t *root
);

/*
  Precondition predicate for mt_get_path
*/
bool
mt_get_path_pre(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t idx,
  const MerkleTree_Low_path *path1,
  uint8_t *root
);

/*
  Flush the Merkle tree

  @param[in]  mt   The Merkle tree
*/
void mt_flush(MerkleTree_Low_merkle_tree *mt);

/*
  Precondition predicate for mt_flush
*/
bool mt_flush_pre(const MerkleTree_Low_merkle_tree *mt);

/*
  Flush the Merkle tree up to a given index

  @param[in]  mt   The Merkle tree
  @param[in]  idx  The index up to which to flush the tree
*/
void mt_flush_to(MerkleTree_Low_merkle_tree *mt, uint64_t idx);

/*
  Precondition predicate for mt_flush_to
*/
bool mt_flush_to_pre(const MerkleTree_Low_merkle_tree *mt, uint64_t idx);

/*
  Retract the Merkle tree down to a given index

  @param[in]  mt   The Merkle tree
  @param[in]  idx  The index to retract the tree to

 Note: The element and idx will remain in the tree.
*/
void mt_retract_to(MerkleTree_Low_merkle_tree *mt, uint64_t idx);

/*
  Precondition predicate for mt_retract_to
*/
bool mt_retract_to_pre(const MerkleTree_Low_merkle_tree *mt, uint64_t idx);

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
  uint64_t max,
  const MerkleTree_Low_path *path1,
  uint8_t *root
);

/*
  Precondition predicate for mt_verify
*/
bool
mt_verify_pre(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t tgt,
  uint64_t max,
  const MerkleTree_Low_path *path1,
  uint8_t *root
);

/*
  Serialization size

  @param[in]  mt   The Merkle tree

  return the number of bytes required to serialize the tree
*/
uint64_t mt_serialize_size(const MerkleTree_Low_merkle_tree *mt);

/*
  Merkle tree serialization

  @param[in]  mt   The Merkle tree
  @param[out] buf  The buffer to serialize the tree into
  @param[in]  len  Length of buf

  return the number of bytes written

  Note: buf must be a buffer of size mt_serialize_size(mt) or larger, but
  smaller than 2^32 (larger buffers are currently not supported).
*/
uint64_t mt_serialize(const MerkleTree_Low_merkle_tree *mt, uint8_t *buf, uint64_t len);

/*
  Merkle tree deserialization

  @param[in]  expected_hash_size Expected hash size to match hash_fun
  @param[in]  buf  The buffer to deserialize the tree from
  @param[in]  len  Length of buf
  @param[in]  hash_fun Hash function

  return pointer to the new tree if successful, NULL otherwise

  Note: buf must point to an allocated buffer.
*/
MerkleTree_Low_merkle_tree
*mt_deserialize(
  const uint8_t *buf,
  uint64_t len,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
);

/*
  Path serialization

  @param[in]  path The path
  @param[out] buf  The buffer to serialize the path into
  @param[in]  len  Length of buf

  return the number of bytes written
*/
uint64_t mt_serialize_path(const MerkleTree_Low_path *path1, uint8_t *buf, uint64_t len);

/*
  Path deserialization

  @param[in]  buf  The buffer to deserialize the path from
  @param[in]  len  Length of buf

  return pointer to the new path if successful, NULL otherwise

 Note: buf must point to an allocated buffer.
*/
MerkleTree_Low_path *mt_deserialize_path(const uint8_t *buf, uint64_t len);

typedef MerkleTree_Low_merkle_tree *mt_p0;

/*
  Default hash function
*/
void mt_sha256_compress(uint8_t *src1, uint8_t *src2, uint8_t *dst);

/*
  Construction wired to sha256 from EverCrypt

  @param[in]  init   The initial hash
*/
MerkleTree_Low_merkle_tree *mt_create(uint8_t *init);

typedef uint32_t MerkleTree_Low_index_t;

extern uint32_t MerkleTree_Low_uint32_32_max;

extern uint64_t MerkleTree_Low_uint32_max;

extern uint64_t MerkleTree_Low_uint64_max;

extern uint64_t MerkleTree_Low_offset_range_limit;

typedef uint64_t MerkleTree_Low_offset_t;

extern uint32_t MerkleTree_Low_merkle_tree_size_lg;

bool MerkleTree_Low_uu___is_MT(MerkleTree_Low_merkle_tree projectee);

typedef MerkleTree_Low_merkle_tree *MerkleTree_Low_mt_p;

typedef const MerkleTree_Low_merkle_tree *MerkleTree_Low_const_mt_p;

bool
MerkleTree_Low_merkle_tree_conditions(
  uint64_t offset,
  uint32_t i,
  uint32_t j,
  LowStar_Vector_vector_str__LowStar_Vector_vector_str___uint8_t_ hs,
  bool rhs_ok,
  LowStar_Vector_vector_str___uint8_t_ rhs,
  uint8_t *mroot
);

uint32_t MerkleTree_Low_offset_of(uint32_t i);

void MerkleTree_Low_mt_free(MerkleTree_Low_merkle_tree *mt);

bool MerkleTree_Low_mt_insert_pre(const MerkleTree_Low_merkle_tree *mt, uint8_t *v);

void MerkleTree_Low_mt_insert(MerkleTree_Low_merkle_tree *mt, uint8_t *v);

MerkleTree_Low_merkle_tree
*MerkleTree_Low_mt_create_custom(
  uint32_t hsz,
  uint8_t *init,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
);

bool MerkleTree_Low_uu___is_Path(MerkleTree_Low_path projectee);

typedef MerkleTree_Low_path *MerkleTree_Low_path_p;

typedef const MerkleTree_Low_path *MerkleTree_Low_const_path_p;

MerkleTree_Low_path *MerkleTree_Low_init_path(uint32_t hsz);

void MerkleTree_Low_clear_path(MerkleTree_Low_path *p);

void MerkleTree_Low_free_path(MerkleTree_Low_path *p);

bool MerkleTree_Low_mt_get_root_pre(const MerkleTree_Low_merkle_tree *mt, uint8_t *rt);

void MerkleTree_Low_mt_get_root(const MerkleTree_Low_merkle_tree *mt, uint8_t *rt);

void MerkleTree_Low_mt_path_insert(uint32_t hsz, MerkleTree_Low_path *p, uint8_t *hp);

uint32_t MerkleTree_Low_mt_get_path_length(const MerkleTree_Low_path *p);

bool MerkleTree_Low_mt_get_path_step_pre(const MerkleTree_Low_path *p, uint32_t i);

uint8_t *MerkleTree_Low_mt_get_path_step(const MerkleTree_Low_path *p, uint32_t i);

bool
MerkleTree_Low_mt_get_path_pre(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t idx,
  const MerkleTree_Low_path *p,
  uint8_t *root
);

uint32_t
MerkleTree_Low_mt_get_path(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t idx,
  MerkleTree_Low_path *p,
  uint8_t *root
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
  uint64_t k,
  uint64_t j,
  const MerkleTree_Low_path *p,
  uint8_t *rt
);

bool
MerkleTree_Low_mt_verify(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t k,
  uint64_t j,
  const MerkleTree_Low_path *p,
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
  const uint8_t *input,
  uint64_t sz,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
);

uint64_t
MerkleTree_Low_Serialization_mt_serialize_path(
  const MerkleTree_Low_path *p,
  uint8_t *output,
  uint64_t sz
);

MerkleTree_Low_path
*MerkleTree_Low_Serialization_mt_deserialize_path(const uint8_t *input, uint64_t sz);

uint8_t *MerkleTree_Low_Hashfunctions_init_hash(uint32_t hsz);

void MerkleTree_Low_Hashfunctions_free_hash(uint8_t *h);

#if defined(__cplusplus)
}
#endif

#define __MerkleTree_H_DEFINED
#endif
