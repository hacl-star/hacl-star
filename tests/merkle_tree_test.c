#include <stdlib.h>
#include <stdint.h>
#include <sys/time.h>
#include "merkle_tree_test.h"
#include "MerkleTree.h"
#include "EverCrypt_AutoConfig2.h"

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

  uint64_t num_elts = 1;
  if (argc > 1)
    num_elts = atoi(argv[1]);

  EverCrypt_AutoConfig2_init();

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
  mt_p mt = mt_create(ih);
  free_hash(ih);

  printf("A Merkle tree has been created!\n");

  // Insertion
  for (uint64_t i = 0; i < num_elts; i++) {
    uint8_t *hash = init_hash();
    hash[0] = (uint8_t) (i + 1);
    mt_insert(mt, hash);
    free_hash(hash);
  }

  printf("Tree holds [%ld,%ld]\n", 0UL, num_elts);

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

  for (uint64_t k = 0; k <= num_elts; k++) {
    uint32_t j = mt_get_path(mt, k, path, root);

    /* printf("Path(%d): ", k); */
    /* for (uint32_t l = 0; l < path->sz; l++) { */
    /*   printf("%d ", path->vs[l][0]); */
    /* } */
    /* printf("\n"); */

    /* printf("Root: %d\n", root[0]); */

    bool verified = mt_verify(mt, k, j, path, root);
    printf("Verification with k(%ld), j(%d): %d\n", k, j, verified);

    clear_path(path);
  }

  uint64_t flush_to = num_elts / 3;
  mt_flush_to(mt, flush_to);
  printf("Flushed tree to [%ld,%ld]\n", flush_to, num_elts);

  for (uint64_t k = flush_to; k <= num_elts; k++) {
    uint32_t j = mt_get_path(mt, k, path, root);

    bool verified = mt_verify(mt, k, j, path, root);
    printf("Verification (after flushing) with k(%ld), j(%d): %d\n", k, j, verified);

    clear_path(path);
  }

  flush_to = num_elts / 2;
  mt_flush_to(mt, flush_to);
  printf("Flushed tree to [%ld,%ld]\n", flush_to, num_elts);

  for (uint64_t k = flush_to; k <= num_elts; k++) {
    uint32_t j = mt_get_path(mt, k, path, root);

    bool verified = mt_verify(mt, k, j, path, root);
    printf("Verification (after flushing) with k(%ld), j(%d): %d\n", k, j, verified);

    clear_path(path);
  }

  // printf("All merkle paths are verified: %d\n", timer_tick());
  printf("All merkle paths are verified!\n");

  {
    printf("Testing (de)serialization...\n");
    size_t num_bytes = mt_serialize_size(mt) * sizeof(uint8_t);
    uint8_t *buf = malloc(num_bytes);
    uint32_t written = mt_serialize(mt, buf, num_bytes);

    if (written != num_bytes) {
      printf("Serialization failed!\n");
      return 1;
    }

    merkle_tree *mtd = mt_deserialize(buf, written);

    if (mtd == NULL) {
      printf("Deserialization failed!\n");
      return 1;
    }

    free(buf);

    printf("Re-verifying paths on deserialized tree...\n");
    for (uint64_t k = flush_to; k <= num_elts; k++) {
      uint32_t j = mt_get_path(mtd, k, path, root);

      bool verified = mt_verify(mtd, k, j, path, root);
      printf("Verification with k(%ld), j(%d): %d\n", k, j, verified);

      clear_path(path);
    }

    mt_free(mtd);
  }

  uint64_t retract_to = flush_to + (num_elts - flush_to)/2;
  if (!mt_retract_to_pre(mt, retract_to)) {
    printf("ERROR: Precondition for mt_retract_to does not hold; exiting.\n");
    exit(1);
  }

  mt_retract_to(mt, retract_to);
  printf("Retracted tree to [%ld,%ld]\n", flush_to, retract_to);

  printf("Re-verifying paths on retracted tree...\n");
  for (uint64_t k = flush_to; k <= retract_to; k++) {
    if (!mt_get_path_pre(mt, k, path, root)) {
      printf("ERROR: Precondition for mt_get_path does not hold; exiting.\n");
      exit(1);
    }
    uint32_t j = mt_get_path(mt, k, path, root);

    bool verified = mt_verify(mt, k, j, path, root);
    printf("Verification with k(%ld), j(%d): %d\n", k, j, verified);

    clear_path(path);
  }

  flush_to = retract_to;
  mt_flush_to(mt, flush_to);
  printf("Flushed tree to [%ld,%ld]\n", flush_to, retract_to);
  {
    uint64_t k = flush_to;
    uint32_t j = mt_get_path(mt, k, path, root);
    bool verified = mt_verify(mt, k, j, path, root);
    printf("Final verification with k(%ld), j(%d): %d\n", k, j, verified);
    clear_path(path);
  }

  // Free
  mt_free(mt);
  free_path(path);
  free_hash(root);

  // printf("The Merkle tree is freed: %d\n", timer_tick());
  printf("The Merkle tree is freed\n");

  return 0;
}
