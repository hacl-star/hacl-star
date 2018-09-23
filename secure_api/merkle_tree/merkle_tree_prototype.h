#include "stdint.h"

extern hash_vec;
extern merkle_tree;

typedef uint8_t *hash;
typedef merkle_tree *mt_p;
typedef hash_vec *path;

/// Utilities

hash init_hash();
void free_hash(hash h);

path init_path();
void free_path(path p);
void clear_path(path p);

/// Construction and destruction (free)
mt_p create_mt(hash init);
void free_mt(mt_p mt);

/* Insertion
* @param[in] v The tree does not take ownership of the hash, it makes a copy of
*              its content. Note that the content of the hash will be 
*              overwritten with an arbitrary value by the call.
*/
void mt_insert(mt_p mt, hash v);

/** Getting the Merkle root
 * @param[out] root The merkle root returned as a hash pointer
 */
void mt_get_root(mt_p mt, hash root);

/** Getting the Merkle path
 * @param idx The index of the target hash
 * @param[out] root The Merkle root
 * @param[out] path A resulting Merkle path that contains the leaf hash.
 *                  Note that the path contains pointers to hashes in the tree,
 *                  not the actual hash values.
 * @return The number of elements in the tree
 */
uint32_t mt_get_path(mt_p mt, uint32_t idx, hash root, hash *path);

void mt_flush(mt_p mt);
void mt_flush_to(mt_p mt, uint32_t idx);

/** Client-side verification
 * @param k The index of the target hash
 * @param j The maximum index + 1 of the tree when the path is generated
 */
bool mt_verify(uint32_t k, uint32_t j, hash *path, hash root);
