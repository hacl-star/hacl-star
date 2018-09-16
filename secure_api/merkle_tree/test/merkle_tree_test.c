#include <stdlib.h>
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

int main(int argc, char *argv[]) {

  uint32_t num_elts = 1;
  if (argc > 1)
    num_elts = atoi(argv[1]);

  // Should call below two functions in the beginning of `main`.
  kremlinit_globals();
  hash_cfg(EverCrypt_AutoConfig_Vale);

  timer_start();

  // Hash test
  /* uint8_t *h1 = init_hash(); */
  /* uint8_t *h2 = init_hash(); */
  /* uint8_t *hh = init_hash(); */
  /* hash_2(h1, h2, hh); */
  /* for (uint32_t i = 0; i < hash_size; ++i) { */
  /*   printf("Hash(%d): %d\n", i, hh[i]); */
  /* } */

  // Creation
  uint8_t *ih = init_hash();
  mt_p mt = create_mt(ih);
  free_hash(ih);

  printf("A Merkle tree has been created!\n");

  // Insertion
  for (uint32_t i = 0; i < num_elts; i++) {
    uint8_t *hash = init_hash();
    hash[0] = (uint8_t) (i + 1);
    mt_insert(mt, hash);
    free_hash(hash);
  }

  /* uint8_t *hh = init_hash(); */
  /* hash_2(mt->hs.vs[2].vs[0], mt->hs.vs[0].vs[4], hh); */
  /* printf("Root: %d\n", hh[0]); */

  // printf("All values are inserted: %d\n", timer_tick());
  printf("All values are inserted!\n");

  /* for (uint32_t lv = 0; lv < 3; lv++) { */
  /*   printf("Hashes at the level %d:\n", lv); */
  /*   uint32_t lth = mt->hs.vs[lv].sz; */
  /*   for (uint32_t i = 0; i < lth; i++) { */
  /*     printf("Hash(%d): %d ", i, mt->hs.vs[lv].vs[i][0]); */
  /*   } */
  /*   printf("\n"); */
  /* } */

  // Getting the Merkle path and verify it
  uint8_t *root = init_hash();
  hash_vec *path = init_path();

  for (uint32_t k = 0; k <= num_elts; k++) {
    int j = mt_get_path(mt, k, path, root);

    /* printf("Path(%d): ", k); */
    /* for (uint32_t l = 0; l < path->sz; l++) { */
    /*   printf("%d ", path->vs[l][0]); */
    /* } */
    /* printf("\n"); */

    /* printf("Root: %d\n", root[0]); */
    
    bool verified = mt_verify(k, j, path, root);
    printf("Verification with k(%d), j(%d): %d\n", k, j, verified);

    clear_path(path);
  }

  int flush_to = num_elts / 3;
  mt_flush_to(mt, flush_to);
  printf("Leaves flushed until: %d\n", flush_to);

  for (uint32_t k = flush_to; k <= num_elts; k++) {
    int j = mt_get_path(mt, k, path, root);

    bool verified = mt_verify(k, j, path, root);
    printf("Verification (after flushing) with k(%d), j(%d): %d\n", k, j, verified);

    clear_path(path);
  }

  flush_to = num_elts / 2;
  mt_flush_to(mt, flush_to);
  printf("Leaves flushed until: %d\n", flush_to);

  for (uint32_t k = flush_to; k <= num_elts; k++) {
    int j = mt_get_path(mt, k, path, root);

    bool verified = mt_verify(k, j, path, root);
    printf("Verification (after flushing) with k(%d), j(%d): %d\n", k, j, verified);

    clear_path(path);
  }

  flush_to = num_elts;
  mt_flush_to(mt, flush_to);
  printf("Leaves flushed until: %d\n", flush_to);

  for (uint32_t k = flush_to; k <= num_elts; k++) {
    int j = mt_get_path(mt, k, path, root);

    bool verified = mt_verify(k, j, path, root);
    printf("Verification (after flushing) with k(%d), j(%d): %d\n", k, j, verified);

    clear_path(path);
  }

  // printf("All merkle paths are verified: %d\n", timer_tick());
  printf("All merkle paths are verified!\n");

  // Free
  free_mt(mt);
  free_path(path);
  free_hash(root);

  // printf("The Merkle tree is freed: %d\n", timer_tick());
  printf("The Merkle tree is freed\n");
  
  return 0;
}
