/* Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
   Licensed under the Apache 2.0 License. */

#ifndef _MERKLE_TREE_H_
#define _MERKLE_TREE_H_

#ifdef __cplusplus
extern "C" {
#endif

#include "stdint.h"

#include "MerkleTree_New_Low.h"


/* Utilities */

extern hash (*init_hash)();
extern void (*free_hash)(hash x0);

extern path init_path();
extern void free_path(path p);
extern void clear_path(path p);

/** Construction */
extern merkle_tree *mt_create(uint8_t *init1);

/** Destruction */
extern void mt_free(merkle_tree *mt);

/* Insertion
 *
 * @param[in]  mt  The Merkle tree
 * @param[in]  v   The tree does not take ownership of the hash, it makes a copy
 *                 of its content.
 *
 * Note: The content of the hash will be overwritten with an arbitrary value.
 */
extern void mt_insert(merkle_tree *mt, hash v);

/** Precondition predicate for mt_insert */
extern bool mt_insert_pre(merkle_tree *mt, hash v);


/** Getting the Merkle root
 *
 * @param[in]  mt   The Merkle tree
 * @param[out] root The Merkle root returned as a hash pointer
 */
extern void mt_get_root(merkle_tree *mt, hash root);

/** Precondition predicate for mt_get_root */
extern bool mt_get_root_pre(merkle_tree *mt, hash root);


/** Getting a Merkle path
 *
 * @param[in]  mt   The Merkle tree
 * @param[in]  idx  The index of the target hash
 * @param[out] root The Merkle root
 * @param[out] path A resulting Merkle path that contains the leaf hash.
 *
 * @return The number of elements in the tree
 *
 * Notes:
 * - The resulting path contains pointers to hashes in the tree, not copies of
 *   the hash values.
 * - idx must be within the currently held indices in the tree (past the
 *   last flush index).
 */
extern uint32_t mt_get_path(merkle_tree *mt, uint64_t idx, path p, hash root);

/** Precondition predicate for mt_get_path */
extern bool mt_get_path_pre(merkle_tree *mt, uint64_t idx, path p, hash root);


/** Flush the Merkle tree
 *
 * @param[in]  mt   The Merkle tree
 */
extern void mt_flush(merkle_tree *mt);

/** Precondition predicate for mt_flush */
extern bool mt_flush_pre(merkle_tree *mt);


/** Flush the Merkle tree up to a given index
 *
 * @param[in]  mt   The Merkle tree
 * @param[in]  idx  The index up to which to flush the tree
 */
extern void mt_flush_to(merkle_tree *mt, uint64_t idx);

/** Precondition predicate for mt_flush_to */
extern bool mt_flush_to_pre(merkle_tree *mt, uint64_t idx);


/** Retract the Merkle tree down to a given index
 *
 * @param[in]  mt   The Merkle tree
 * @param[in]  idx  The index to retract the tree to
 *
 * Note: The element and idx will remain in the tree.
 */
extern void mt_retract_to(merkle_tree *mt, uint64_t idx);

/** Precondition predicate for mt_retract_to */
extern bool mt_retract_to_pre(merkle_tree *mt, uint64_t idx);


/** Client-side verification
 *
 * @param[in]  mt   The Merkle tree
 * @param[in]  tgt  The index of the target hash
 * @param[in]  max  The maximum index + 1 of the tree when the path was generated
 * @param[in]  path The Merkle path to verify
 * @param[in]  root
 *
 * @return true if the verification succeeded, false otherwise
 *
 * Note: max - tgt must be less than 2^32.
 */
extern bool mt_verify(merkle_tree *mt, uint64_t tgt, uint64_t max, path path, hash root);

/** Precondition predicate for mt_verify */
extern bool mt_verify_pre(merkle_tree *mt, uint64_t tgt, uint64_t max, path path, hash root);


/** Serialization size
 *
 * @param[in]  mt   The Merkle tree
 *
 * @return the number of bytes required to serialize the tree
 */
extern uint64_t mt_serialize_size(merkle_tree *mt);


/** Serialization
 *
 * @param[in]  mt   The Merkle tree
 * @param[out] buf  The buffer to serialize the tree into
 * #param[in]  len  Length of buf
 *
 * @return the number of bytes written
 *
 * Note: buf must be a buffer of size mt_serialize_size(mt) or larger, but
 * smaller than 2^32 (larger buffers are currently not supported).
 */
extern uint32_t mt_serialize(merkle_tree *mt, char *buf, uint64_t len);


/** Deserialization
 *
 * @param[in]  buf  The buffer to deserialize the tree from
 * @param[in]  len  Length of buf
 *
 * @return pointer to the new tree if successful, NULL otherwise
 *
 * Note: buf must point to an allocated buffer.
 */
extern merkle_tree *mt_deserialize(const char *buf, uint64_t len);

#ifdef __cplusplus
}
#endif

#endif /* _MERKLE_TREE_H_ */
