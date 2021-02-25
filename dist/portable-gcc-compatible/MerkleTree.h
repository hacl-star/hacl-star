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


#include "Hacl_Kremlib.h"
#include "Hacl_Spec.h"
#include "EverCrypt_Hash.h"

/* SNIPPET_START: MerkleTree_Low_Datastructures_hash_vec */

typedef struct MerkleTree_Low_Datastructures_hash_vec_s
{
  uint32_t sz;
  uint32_t cap;
  uint8_t **vs;
}
MerkleTree_Low_Datastructures_hash_vec;

/* SNIPPET_END: MerkleTree_Low_Datastructures_hash_vec */

/* SNIPPET_START: hash_size_t */

typedef uint32_t hash_size_t;

/* SNIPPET_END: hash_size_t */

/* SNIPPET_START: offset_t */

typedef uint64_t offset_t;

/* SNIPPET_END: offset_t */

/* SNIPPET_START: index_t */

typedef uint32_t index_t;

/* SNIPPET_END: index_t */

/* SNIPPET_START: MerkleTree_Low_path */

typedef struct MerkleTree_Low_path_s
{
  uint32_t hash_size;
  MerkleTree_Low_Datastructures_hash_vec hashes;
}
MerkleTree_Low_path;

/* SNIPPET_END: MerkleTree_Low_path */

/* SNIPPET_START: path */

typedef MerkleTree_Low_path path;

/* SNIPPET_END: path */

/* SNIPPET_START: path_p */

typedef MerkleTree_Low_path *path_p;

/* SNIPPET_END: path_p */

/* SNIPPET_START: const_path_p */

typedef const MerkleTree_Low_path *const_path_p;

/* SNIPPET_END: const_path_p */

/* SNIPPET_START: MerkleTree_Low_Datastructures_hash_vv */

typedef struct MerkleTree_Low_Datastructures_hash_vv_s
{
  uint32_t sz;
  uint32_t cap;
  MerkleTree_Low_Datastructures_hash_vec *vs;
}
MerkleTree_Low_Datastructures_hash_vv;

/* SNIPPET_END: MerkleTree_Low_Datastructures_hash_vv */

/* SNIPPET_START: MerkleTree_Low_merkle_tree */

typedef struct MerkleTree_Low_merkle_tree_s
{
  uint32_t hash_size;
  uint64_t offset;
  uint32_t i;
  uint32_t j;
  MerkleTree_Low_Datastructures_hash_vv hs;
  bool rhs_ok;
  MerkleTree_Low_Datastructures_hash_vec rhs;
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
  Constructor for hashes
*/
uint8_t *mt_init_hash(uint32_t hash_size);

/* SNIPPET_END: mt_init_hash */

/* SNIPPET_START: mt_free_hash */

/*
  Destructor for hashes
*/
void mt_free_hash(uint8_t *h);

/* SNIPPET_END: mt_free_hash */

/* SNIPPET_START: mt_init_path */

/*
  Constructor for paths
*/
MerkleTree_Low_path *mt_init_path(uint32_t hash_size);

/* SNIPPET_END: mt_init_path */

/* SNIPPET_START: mt_free_path */

/*
  Destructor for paths
*/
void mt_free_path(MerkleTree_Low_path *path1);

/* SNIPPET_END: mt_free_path */

/* SNIPPET_START: mt_get_path_length */

/*
  Length of a path

  @param[in] p Path

  return The length of the path
*/
uint32_t mt_get_path_length(const MerkleTree_Low_path *path1);

/* SNIPPET_END: mt_get_path_length */

/* SNIPPET_START: mt_path_insert */

/*
  Insert hash into path

  @param[in] p Path
  @param[in] hash Hash to insert
*/
void mt_path_insert(MerkleTree_Low_path *path1, uint8_t *hash1);

/* SNIPPET_END: mt_path_insert */

/* SNIPPET_START: mt_get_path_step */

/*
  Get step on a path

  @param[in] p Path
  @param[in] i Path step index

  return The hash at step i of p
*/
uint8_t *mt_get_path_step(const MerkleTree_Low_path *path1, uint32_t i);

/* SNIPPET_END: mt_get_path_step */

/* SNIPPET_START: mt_get_path_step_pre */

/*
  Precondition predicate for mt_get_path_step
*/
bool mt_get_path_step_pre(const MerkleTree_Low_path *path1, uint32_t i);

/* SNIPPET_END: mt_get_path_step_pre */

/* SNIPPET_START: mt_create_custom */

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
void mt_insert(MerkleTree_Low_merkle_tree *mt, uint8_t *v);

/* SNIPPET_END: mt_insert */

/* SNIPPET_START: mt_insert_pre */

/*
  Precondition predicate for mt_insert
*/
bool mt_insert_pre(const MerkleTree_Low_merkle_tree *mt, uint8_t *v);

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
  MerkleTree_Low_path *path1,
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
  const MerkleTree_Low_path *path1,
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
  uint64_t max,
  const MerkleTree_Low_path *path1,
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
  uint64_t max,
  const MerkleTree_Low_path *path1,
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
uint64_t mt_serialize(const MerkleTree_Low_merkle_tree *mt, uint8_t *buf, uint64_t len);

/* SNIPPET_END: mt_serialize */

/* SNIPPET_START: mt_deserialize */

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

/* SNIPPET_END: mt_deserialize */

/* SNIPPET_START: mt_serialize_path */

/*
  Path serialization

  @param[in]  path The path
  @param[out] buf  The buffer to serialize the path into
  @param[in]  len  Length of buf

  return the number of bytes written
*/
uint64_t mt_serialize_path(const MerkleTree_Low_path *path1, uint8_t *buf, uint64_t len);

/* SNIPPET_END: mt_serialize_path */

/* SNIPPET_START: mt_deserialize_path */

/*
  Path deserialization

  @param[in]  buf  The buffer to deserialize the path from
  @param[in]  len  Length of buf

  return pointer to the new path if successful, NULL otherwise

 Note: buf must point to an allocated buffer.
*/
MerkleTree_Low_path *mt_deserialize_path(const uint8_t *buf, uint64_t len);

/* SNIPPET_END: mt_deserialize_path */

/* SNIPPET_START: mt_p0 */

typedef MerkleTree_Low_merkle_tree *mt_p0;

/* SNIPPET_END: mt_p0 */

/* SNIPPET_START: mt_sha256_compress */

/*
  Default hash function
*/
void mt_sha256_compress(uint8_t *src1, uint8_t *src2, uint8_t *dst);

/* SNIPPET_END: mt_sha256_compress */

/* SNIPPET_START: mt_create */

/*
  Construction wired to sha256 from EverCrypt

  @param[in]  init   The initial hash
*/
MerkleTree_Low_merkle_tree *mt_create(uint8_t *init);

/* SNIPPET_END: mt_create */

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

MerkleTree_Low_Datastructures_hash_vv
MerkleTree_Low___proj__MT__item__hs(MerkleTree_Low_merkle_tree projectee);

/* SNIPPET_END: MerkleTree_Low___proj__MT__item__hs */

/* SNIPPET_START: MerkleTree_Low___proj__MT__item__rhs_ok */

bool MerkleTree_Low___proj__MT__item__rhs_ok(MerkleTree_Low_merkle_tree projectee);

/* SNIPPET_END: MerkleTree_Low___proj__MT__item__rhs_ok */

/* SNIPPET_START: MerkleTree_Low___proj__MT__item__rhs */

MerkleTree_Low_Datastructures_hash_vec
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
  uint64_t offset,
  uint32_t i,
  uint32_t j,
  MerkleTree_Low_Datastructures_hash_vv hs,
  bool rhs_ok,
  MerkleTree_Low_Datastructures_hash_vec rhs,
  uint8_t *mroot
);

/* SNIPPET_END: MerkleTree_Low_merkle_tree_conditions */

/* SNIPPET_START: MerkleTree_Low_offset_of */

uint32_t MerkleTree_Low_offset_of(uint32_t i);

/* SNIPPET_END: MerkleTree_Low_offset_of */

/* SNIPPET_START: MerkleTree_Low_mt_free */

void MerkleTree_Low_mt_free(MerkleTree_Low_merkle_tree *mt);

/* SNIPPET_END: MerkleTree_Low_mt_free */

/* SNIPPET_START: MerkleTree_Low_mt_insert_pre */

bool MerkleTree_Low_mt_insert_pre(const MerkleTree_Low_merkle_tree *mt, uint8_t *v);

/* SNIPPET_END: MerkleTree_Low_mt_insert_pre */

/* SNIPPET_START: MerkleTree_Low_mt_insert */

void MerkleTree_Low_mt_insert(MerkleTree_Low_merkle_tree *mt, uint8_t *v);

/* SNIPPET_END: MerkleTree_Low_mt_insert */

/* SNIPPET_START: MerkleTree_Low_mt_create_custom */

MerkleTree_Low_merkle_tree
*MerkleTree_Low_mt_create_custom(
  uint32_t hsz,
  uint8_t *init,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
);

/* SNIPPET_END: MerkleTree_Low_mt_create_custom */

/* SNIPPET_START: MerkleTree_Low_uu___is_Path */

bool MerkleTree_Low_uu___is_Path(MerkleTree_Low_path projectee);

/* SNIPPET_END: MerkleTree_Low_uu___is_Path */

/* SNIPPET_START: MerkleTree_Low___proj__Path__item__hash_size */

uint32_t MerkleTree_Low___proj__Path__item__hash_size(MerkleTree_Low_path projectee);

/* SNIPPET_END: MerkleTree_Low___proj__Path__item__hash_size */

/* SNIPPET_START: MerkleTree_Low___proj__Path__item__hashes */

MerkleTree_Low_Datastructures_hash_vec
MerkleTree_Low___proj__Path__item__hashes(MerkleTree_Low_path projectee);

/* SNIPPET_END: MerkleTree_Low___proj__Path__item__hashes */

/* SNIPPET_START: MerkleTree_Low_path_p */

typedef MerkleTree_Low_path *MerkleTree_Low_path_p;

/* SNIPPET_END: MerkleTree_Low_path_p */

/* SNIPPET_START: MerkleTree_Low_const_path_p */

typedef const MerkleTree_Low_path *MerkleTree_Low_const_path_p;

/* SNIPPET_END: MerkleTree_Low_const_path_p */

/* SNIPPET_START: MerkleTree_Low_init_path */

MerkleTree_Low_path *MerkleTree_Low_init_path(uint32_t hsz);

/* SNIPPET_END: MerkleTree_Low_init_path */

/* SNIPPET_START: MerkleTree_Low_clear_path */

void MerkleTree_Low_clear_path(MerkleTree_Low_path *p);

/* SNIPPET_END: MerkleTree_Low_clear_path */

/* SNIPPET_START: MerkleTree_Low_free_path */

void MerkleTree_Low_free_path(MerkleTree_Low_path *p);

/* SNIPPET_END: MerkleTree_Low_free_path */

/* SNIPPET_START: MerkleTree_Low_mt_get_root_pre */

bool MerkleTree_Low_mt_get_root_pre(const MerkleTree_Low_merkle_tree *mt, uint8_t *rt);

/* SNIPPET_END: MerkleTree_Low_mt_get_root_pre */

/* SNIPPET_START: MerkleTree_Low_mt_get_root */

void MerkleTree_Low_mt_get_root(const MerkleTree_Low_merkle_tree *mt, uint8_t *rt);

/* SNIPPET_END: MerkleTree_Low_mt_get_root */

/* SNIPPET_START: MerkleTree_Low_mt_path_insert */

void MerkleTree_Low_mt_path_insert(uint32_t hsz, MerkleTree_Low_path *p, uint8_t *hp);

/* SNIPPET_END: MerkleTree_Low_mt_path_insert */

/* SNIPPET_START: MerkleTree_Low_mt_get_path_length */

uint32_t MerkleTree_Low_mt_get_path_length(const MerkleTree_Low_path *p);

/* SNIPPET_END: MerkleTree_Low_mt_get_path_length */

/* SNIPPET_START: MerkleTree_Low_mt_get_path_step_pre */

bool MerkleTree_Low_mt_get_path_step_pre(const MerkleTree_Low_path *p, uint32_t i);

/* SNIPPET_END: MerkleTree_Low_mt_get_path_step_pre */

/* SNIPPET_START: MerkleTree_Low_mt_get_path_step */

uint8_t *MerkleTree_Low_mt_get_path_step(const MerkleTree_Low_path *p, uint32_t i);

/* SNIPPET_END: MerkleTree_Low_mt_get_path_step */

/* SNIPPET_START: MerkleTree_Low_mt_get_path_pre */

bool
MerkleTree_Low_mt_get_path_pre(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t idx,
  const MerkleTree_Low_path *p,
  uint8_t *root
);

/* SNIPPET_END: MerkleTree_Low_mt_get_path_pre */

/* SNIPPET_START: MerkleTree_Low_mt_get_path */

uint32_t
MerkleTree_Low_mt_get_path(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t idx,
  MerkleTree_Low_path *p,
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
  uint64_t k,
  uint64_t j,
  const MerkleTree_Low_path *p,
  uint8_t *rt
);

/* SNIPPET_END: MerkleTree_Low_mt_verify_pre */

/* SNIPPET_START: MerkleTree_Low_mt_verify */

bool
MerkleTree_Low_mt_verify(
  const MerkleTree_Low_merkle_tree *mt,
  uint64_t k,
  uint64_t j,
  const MerkleTree_Low_path *p,
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
  const uint8_t *input,
  uint64_t sz,
  void (*hash_fun)(uint8_t *x0, uint8_t *x1, uint8_t *x2)
);

/* SNIPPET_END: MerkleTree_Low_Serialization_mt_deserialize */

/* SNIPPET_START: MerkleTree_Low_Serialization_mt_serialize_path */

uint64_t
MerkleTree_Low_Serialization_mt_serialize_path(
  const MerkleTree_Low_path *p,
  uint8_t *output,
  uint64_t sz
);

/* SNIPPET_END: MerkleTree_Low_Serialization_mt_serialize_path */

/* SNIPPET_START: MerkleTree_Low_Serialization_mt_deserialize_path */

MerkleTree_Low_path
*MerkleTree_Low_Serialization_mt_deserialize_path(const uint8_t *input, uint64_t sz);

/* SNIPPET_END: MerkleTree_Low_Serialization_mt_deserialize_path */

/* SNIPPET_START: MerkleTree_Low_Hashfunctions_init_hash */

uint8_t *MerkleTree_Low_Hashfunctions_init_hash(uint32_t hsz);

/* SNIPPET_END: MerkleTree_Low_Hashfunctions_init_hash */

/* SNIPPET_START: MerkleTree_Low_Hashfunctions_free_hash */

void MerkleTree_Low_Hashfunctions_free_hash(uint8_t *h);

/* SNIPPET_END: MerkleTree_Low_Hashfunctions_free_hash */

#if defined(__cplusplus)
}
#endif

#define __MerkleTree_H_DEFINED
#endif
