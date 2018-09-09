#include <stdint.h>
#include <sys/time.h>
#include "merkle_tree_test.h"
#include "MerkleTree_New_Low.h"

static struct timeval timer;

void timer_start() {
  gettimeofday(&timer, NULL);
}

int timer_tick() {
  int time_cur_usec = timer.tv_usec;
  int time_cur_sec = timer.tv_sec;
  gettimeofday(&timer, NULL);
  
  return (timer.tv_sec * 1000000 + timer.tv_usec -
	  time_cur_sec * 1000000 - time_cur_usec);
}

int main() {

  kremlinit_globals();
  hash_cfg(EverCrypt_AutoConfig_Vale);

  timer_start();

  // Creation
  uint8_t *ih = hash_r_init();
  mt_p mt = create_mt(ih);

  printf("A Merkle tree has been created!\n");

  // Insertion
  uint32_t num_elts = 9;
  for (uint32_t i = 0; i < num_elts; i++) {
    uint8_t *hash = hash_r_init();
    insert(mt, hash);
  }

  printf("All values are inserted: %d\n", timer_tick());
  
  // Getting the Merkle path and verify it
  uint8_t *khash = hash_r_init();
  uint8_t *root = hash_r_init();
  hash_vec path = hash_vec_r_init();

  for (uint32_t k = 0; k <= num_elts; k++) {
    int j = mt_get_path(mt, k, khash, &path, root);

    bool verified = mt_verify(k, j, khash, path, root);
    printf("Verification with k(%d), j(%d): %d\n", k, j, verified);

    path.sz = 0; // This is a bit arbitrary
  }

  int flush_to = 5;
  mt_flush_to(mt, flush_to);
  printf("Flushed until: %d\n", flush_to);

  for (uint32_t k = flush_to; k <= num_elts; k++) {
    int j = mt_get_path(mt, k, khash, &path, root);

    bool verified = mt_verify(k, j, khash, path, root);
    printf("Verification (after flushing) with k(%d), j(%d): %d\n", k, j, verified);

    path.sz = 0; // This is a bit arbitrary
  }

  printf("All merkle paths are verified: %d\n", timer_tick());

  // Free
  free_mt(mt);
  free(path.vs);
  hash_r_free(khash);
  hash_r_free(root);

  printf("The Merkle tree is freed: %d\n", timer_tick());
  
  return 0;
}
