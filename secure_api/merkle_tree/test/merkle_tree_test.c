#include <stdint.h>
#include "merkle_tree_test.h"
#include "MerkleTree_New_Low.h"

int main () {
  kremlinit_globals();

  // Creation
  uint8_t *init_hash = hash_r_init();
  mt_p mt = create_mt(init_hash);

  // Insertion
  uint32_t num_elts = 7;
  for (uint32_t i = 0; i < num_elts; i++) {
    uint8_t *hash = hash_r_init();
    insert(mt, hash);
  }

  // Getting the Merkle path and verify it
  uint8_t *khash = hash_r_init();
  uint8_t *root = hash_r_init();
  for (uint32_t k = 0; k <= num_elts; k++) {
    hash_vec path = hash_vec_r_init();
    int j = mt_get_path(mt, k, khash, &path, root);
    
    bool verified = mt_verify(k, j, khash, path, root);
    printf("Verification with k(%d), j(%d): %d\n", k, j, verified);

    free(path.vs);
  }
  
  // Free
  free_mt(mt);
  hash_r_free(khash);
  hash_r_free(root);

  return 0;
}
