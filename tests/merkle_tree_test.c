#include <stdlib.h>
#include <stdint.h>
#include <assert.h>

#include "EverCrypt_AutoConfig2.h"
#include "MerkleTree.h"
#include "merkle_tree_test.h"

static char hs[32U+1];

static const uint32_t hash_size = 32;

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
  uint8_t *ih = mt_init_hash(hash_size);
  mt_p mt = mt_create(ih);
  print_hash("root", ih);
  mt_free_hash(ih);

  printf("Merkle tree created.\n");

  // Insertion
  for (size_t i = 1; i < num_elts; i++) {
    uint8_t *hash = mt_init_hash(hash_size);
    hash[hash_size-1] = (uint8_t)i;
    print_hash("elem", hash);
    mt_insert(mt, hash);
    mt_free_hash(hash);
  }


  printf("Tree holds [%ld,%ld]\n", 0UL, num_elts-1);
  uint8_t *rh = mt_init_hash(hash_size);
  mt_get_root(mt, rh);
  print_hash("root", rh);
  mt_free_hash(rh);

  printf("All values are inserted!\n");

  print_tree(mt, num_elts);

  // Getting the Merkle path and verify it
  uint8_t *root = mt_init_hash(hash_size);
  for (uint64_t k = 0; k < num_elts; k++) {
    MerkleTree_Low_path *cur_path = mt_init_path(hash_size);
    uint32_t sz = mt_get_path(mt, k, cur_path, root);

    printf("path from k=%lu:\n", k);
    uint8_t *tmp = mt_init_hash(hash_size);
    memcpy(tmp, mt_get_path_step(cur_path, 0), hash_size);
    for (uint32_t l = 0; l < mt_get_path_length(cur_path); l++) {
      uint8_t* step = mt_get_path_step(cur_path, l);
      print_hash("  elem", step);
      if (l > 0) {
        mt_sha256_compress(tmp, step, tmp);
        print_hash("  tmp ", tmp);
      }
    }
    mt_free_hash(tmp);
    print_hash("  root", root);

    bool verified = mt_verify(mt, k, sz, cur_path, root);
    printf("Verification with k=%ld, sz=%d: %d\n", k, sz, verified);

    mt_free_path(cur_path);
  }

  uint64_t flush_to = num_elts / 3;
  mt_flush_to(mt, flush_to);
  printf("Flushed tree to [%ld,%ld]\n", flush_to, num_elts);

  for (uint64_t k = flush_to; k < num_elts; k++) {
    MerkleTree_Low_path *cur_path = mt_init_path(hash_size);
    uint32_t j = mt_get_path(mt, k, cur_path, root);

    bool verified = mt_verify(mt, k, j, cur_path, root);
    printf("Verification (after flushing) with k(%ld), j(%d): %d\n", k, j, verified);

    mt_free_path(cur_path);
  }

  flush_to = num_elts / 2;
  mt_flush_to(mt, flush_to);
  printf("Flushed tree to [%ld,%ld]\n", flush_to, num_elts);

  for (uint64_t k = flush_to; k < num_elts; k++) {
    MerkleTree_Low_path *cur_path = mt_init_path(hash_size);
    uint32_t j = mt_get_path(mt, k, cur_path, root);

    bool verified = mt_verify(mt, k, j, cur_path, root);
    printf("Verification (after flushing) with k(%ld), j(%d): %d\n", k, j, verified);

    mt_free_path(cur_path);
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

    merkle_tree *mtd = mt_deserialize(buf, written, mt_sha256_compress);

    if (mtd == NULL) {
      printf("Deserialization failed!\n");
      return 1;
    }

    free(buf);

    printf("Re-verifying paths on deserialized tree...\n");
    for (uint64_t k = flush_to; k < num_elts; k++) {
      MerkleTree_Low_path *cur_path = mt_init_path(hash_size);
      uint32_t j = mt_get_path(mtd, k, cur_path, root);

      bool verified = mt_verify(mtd, k, j, cur_path, root);

      uint8_t buffer[2048];
      uint32_t spsz = mt_serialize_path(cur_path, buffer, 2048);
      assert(spsz > 0);
      MerkleTree_Low_path *dpath = mt_deserialize_path(hash_size, buffer, 2048);
      assert(dpath != NULL);

      bool dverified = mt_verify(mtd, k, j, dpath, root);
      printf("Verification with k(%ld), j(%d): %d, deserialized (sz=%d): %d\n", k, j, verified, spsz, dverified);

      mt_free_path(dpath);
      mt_free_path(cur_path);
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
    MerkleTree_Low_path *cur_path = mt_init_path(hash_size);
    if (!mt_get_path_pre(mt, k, cur_path, root)) {
      printf("ERROR: Precondition for mt_get_path does not hold; exiting.\n");
      exit(1);
    }
    uint32_t j = mt_get_path(mt, k, cur_path, root);

    bool verified = mt_verify(mt, k, j, cur_path, root);
    printf("Verification with k(%ld), j(%d): %d\n", k, j, verified);

    mt_free_path(cur_path);
  }

  flush_to = retract_to;
  mt_flush_to(mt, flush_to);
  printf("Flushed tree to [%ld,%ld]\n", flush_to, retract_to);
  {
    uint64_t k = flush_to;
    MerkleTree_Low_path *cur_path = mt_init_path(hash_size);
    uint32_t j = mt_get_path(mt, k, cur_path, root);
    bool verified = mt_verify(mt, k, j, cur_path, root);
    printf("Final verification with k(%ld), j(%d): %d\n", k, j, verified);
    mt_free_path(cur_path);
  }

  // Free
  mt_free(mt);
  mt_free_hash(root);

  printf("The Merkle tree is freed\n");

  return 0;
}
