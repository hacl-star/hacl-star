#include <stdlib.h>
#include <stdint.h>
#include <assert.h>

#include "EverCrypt_AutoConfig2.h"
#include "MerkleTree.Nice.h"
#include "merkle_tree_test.h"

char hs[32U+1];
const char* hash_to_string(const uint8_t *h) {
  for (uint32_t i = 0; i < 32U; i++)
    sprintf(&hs[2*i], "%02x", h[i]);
  return hs;
}

void print_hash(const char *name, const uint8_t *h) {
  const char* hs = hash_to_string(h);
  printf("%s: %s\n", name, hs);
}

void print_tree(const mt_p mt, size_t num_elts) {
  printf("Tree:\n");
  for (size_t lv = 0; lv < num_elts; lv++) {
    printf("%02lu:", lv);
    uint32_t lvsz = mt->hs.vs[lv].sz;
    for (size_t i = 0; i < lvsz; i++)
      printf(" %lu=%s", i, hash_to_string(mt->hs.vs[lv].vs[i]));
    printf("\n");
  }
}

int main(int argc, char *argv[]) {

  uint64_t num_elts = 1;
  if (argc > 1)
    num_elts = atoi(argv[1]);

  EverCrypt_AutoConfig2_init();

  // Creation
  uint8_t *ih = init_hash();
  mt_p mt = mt_create(ih);
  print_hash("root", ih);
  free_hash(ih);

  printf("Merkle tree created.\n");

  // Insertion
  for (size_t i = 1; i < num_elts; i++) {
    uint8_t *hash = init_hash();
    hash[hash_size-1] = (uint8_t)i;
    print_hash("elem", hash);
    mt_insert(mt, hash);
    free_hash(hash);
  }


  printf("Tree holds [%ld,%ld]\n", 0UL, num_elts-1);
  uint8_t *rh = init_hash();
  mt_get_root(mt, rh);
  print_hash("root", rh);
  free_hash(rh);

  printf("All values are inserted!\n");

  print_tree(mt, num_elts);

  // Getting the Merkle path and verify it
  uint8_t *root = init_hash();
  hash_vec *cur_path = init_path();

  for (uint64_t k = 0; k < num_elts; k++) {
    uint32_t sz = mt_get_path(mt, k, cur_path, root);

    printf("path from k=%lu:\n", k);
    uint8_t *tmp = init_hash();
    memcpy(tmp, cur_path->vs[0], hash_size);
    for (uint32_t l = 0; l < cur_path->sz; l++) {
      print_hash("  elem", cur_path->vs[l]);
      if (l > 0) {
        hash_2(tmp, cur_path->vs[l], tmp);
        print_hash("  tmp ", tmp);
      }
    }
    free_hash(tmp);
    print_hash("  root", root);

    bool verified = mt_verify(mt, k, sz, cur_path, root);
    printf("Verification with k=%ld, sz=%d: %d\n", k, sz, verified);

    clear_path(cur_path);
  }

  uint64_t flush_to = num_elts / 3;
  mt_flush_to(mt, flush_to);
  printf("Flushed tree to [%ld,%ld]\n", flush_to, num_elts);

  for (uint64_t k = flush_to; k < num_elts; k++) {
    uint32_t j = mt_get_path(mt, k, cur_path, root);

    bool verified = mt_verify(mt, k, j, cur_path, root);
    printf("Verification (after flushing) with k(%ld), j(%d): %d\n", k, j, verified);

    clear_path(cur_path);
  }

  flush_to = num_elts / 2;
  mt_flush_to(mt, flush_to);
  printf("Flushed tree to [%ld,%ld]\n", flush_to, num_elts);

  for (uint64_t k = flush_to; k < num_elts; k++) {
    uint32_t j = mt_get_path(mt, k, cur_path, root);

    bool verified = mt_verify(mt, k, j, cur_path, root);
    printf("Verification (after flushing) with k(%ld), j(%d): %d\n", k, j, verified);

    clear_path(cur_path);
  }

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
    for (uint64_t k = flush_to; k < num_elts; k++) {
      uint32_t j = mt_get_path(mtd, k, cur_path, root);

      bool verified = mt_verify(mtd, k, j, cur_path, root);

      uint8_t buffer[2048];
      uint32_t spsz = mt_serialize_path(cur_path, mt, buffer, 2048);
      assert(spsz > 0);
      path *dpath = mt_deserialize_path(buffer, 2048);
      assert(dpath != NULL);

      bool dverified = mt_verify(mtd, k, j, dpath, root);
      printf("Verification with k(%ld), j(%d): %d, deserialized (sz=%d): %d\n", k, j, verified, spsz, dverified);


      clear_path(dpath);
      clear_path(cur_path);
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
    if (!mt_get_path_pre(mt, k, cur_path, root)) {
      printf("ERROR: Precondition for mt_get_path does not hold; exiting.\n");
      exit(1);
    }
    uint32_t j = mt_get_path(mt, k, cur_path, root);

    bool verified = mt_verify(mt, k, j, cur_path, root);
    printf("Verification with k(%ld), j(%d): %d\n", k, j, verified);

    clear_path(cur_path);
  }

  flush_to = retract_to;
  mt_flush_to(mt, flush_to);
  printf("Flushed tree to [%ld,%ld]\n", flush_to, retract_to);
  {
    uint64_t k = flush_to;
    uint32_t j = mt_get_path(mt, k, cur_path, root);
    bool verified = mt_verify(mt, k, j, cur_path, root);
    printf("Final verification with k(%ld), j(%d): %d\n", k, j, verified);
    clear_path(cur_path);
  }

  // Free
  mt_free(mt);
  free_path(cur_path);
  free_hash(root);

  printf("The Merkle tree is freed\n");

  return 0;
}
