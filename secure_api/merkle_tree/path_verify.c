/* Compile with: gcc -g path_verify.c -o path_verify */
/* For OpenSSL add -DUSE_OPENSSL -lcrypto */

#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <stdint.h>
#include <endian.h> // for be32toh, htobe32

/** @file
 * Examples of Merkle path verification
 */

/**
 * The size of hashes in bytes
 */
#define HASH_SIZE 32

/**
 * Parse a hash string
 *
 * @param input a string to parse
 * @return byte array of length @link HASH_SIZE
 */
uint8_t *parse_hash(const char *input)
{
  uint8_t *r = (uint8_t *)malloc(sizeof(uint8_t) * HASH_SIZE);
  for (int i = 0; i < HASH_SIZE; i++) {
    unsigned tmp;
    if (sscanf(input + 2 * i, "%02x", &tmp) != 1) {
      printf("hash parsing error\n");
      return NULL;
    }
    r[i] = tmp & 0xff;
  }
  return r;
}

/**
 * Print a hash to stdout
 *
 * @param hash hash to print
 */
void print_hash(const uint8_t *hash)
{
  for (int i = 0; i < HASH_SIZE; i++)
    printf("%02x", hash[i] & 0xff);
}

#ifdef USE_OPENSSL
#include <openssl/sha.h>

/**
 * SHA256 compression function (based on OpenSSL)
 *
 * @param h1 left block
 * @param h2 right block
 * @param out compressed block
 */
void compress(const uint8_t *h1, const uint8_t *h2, uint8_t *out)
{
  unsigned char block[HASH_SIZE * 2];
  memcpy(&block[0], h1, HASH_SIZE);
  memcpy(&block[HASH_SIZE], h2, HASH_SIZE);

  SHA256_CTX ctx;
  if (SHA256_Init(&ctx) != 1)
    printf("SHA256_Init error");
  SHA256_Transform(&ctx, &block[0]);

  for (int i = 0; i < 8; i++)
    ((uint32_t *)out)[i] = htobe32(((uint32_t *)ctx.h)[i]);
}
#else
uint32_t constants[] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2};

/**
 * SHA256 compression function (custom)
 *
 * @param h1 left block
 * @param h2 right block
 * @param out compressed block
 */
void compress(const uint8_t *h1, const uint8_t *h2, uint8_t *out)
{
  uint8_t block[HASH_SIZE * 2];
  memcpy(&block[0], h1, HASH_SIZE);
  memcpy(&block[HASH_SIZE], h2, HASH_SIZE);

  uint32_t s[8] = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                   0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};

  uint32_t cws[64];
  memset(cws, 0, 64);

  for (int i = 0; i < 16; i++)
    cws[i] = be32toh(((int32_t *)block)[i]);

  for (int i = 16; i < 64; i++) {
    uint32_t t16 = cws[i - 16];
    uint32_t t15 = cws[i - 15];
    uint32_t t7 = cws[i - 7];
    uint32_t t2 = cws[i - 2];
    uint32_t s1 = (t2 >> 17 | t2 << 15) ^ ((t2 >> 19 | t2 << 13) ^ t2 >> 10);
    uint32_t s0 = (t15 >> 7 | t15 << 25) ^ ((t15 >> 18 | t15 << 14) ^ t15 >> 3);
    cws[i] = (s1 + t7 + s0 + t16);
  }

  uint32_t h[8];
  for (int i = 0; i < 8; i++)
    h[i] = s[i];

  for (int i = 0; i < 64; i++) {
    uint32_t a0 = h[0];
    uint32_t b0 = h[1];
    uint32_t c0 = h[2];
    uint32_t d0 = h[3];
    uint32_t e0 = h[4];
    uint32_t f0 = h[5];
    uint32_t g0 = h[6];
    uint32_t h03 = h[7];
    uint32_t w = cws[i];
    uint32_t t1 = h03 + ((e0 >> 6 | e0 << 26) ^ ((e0 >> 11 | e0 << 21) ^ (e0 >> 25 | e0 << 7))) + ((e0 & f0) ^ (~e0 & g0)) + constants[i] + w;
    uint32_t t2 = ((a0 >> 2 | a0 << 30) ^ ((a0 >> 13 | a0 << 19) ^ (a0 >> 22 | a0 << 10))) + ((a0 & b0) ^ ((a0 & c0) ^ (b0 & c0)));
    h[0] = t1 + t2;
    h[1] = a0;
    h[2] = b0;
    h[3] = c0;
    h[4] = d0 + t1;
    h[5] = e0;
    h[6] = f0;
    h[7] = g0;
  }

  uint32_t *r = (uint32_t *)out;
  for (int i = 0; i < 8; i++)
    r[i] = htobe32(s[i] + h[i]);
}
#endif

/**
 * Recursive implementation of path recomputation
 *
 * @param i index to recompute
 * @param n size of the tree
 * @param path neighbouring hashes along branches
 * @param path_len length of path
 * @param pi current path index
 * @param tag current tag
 * @param actd flag
 * @return 0 for success, non-zero otherwise
 */
int recompute_rec(uint32_t i, uint32_t n, uint8_t *const *path, size_t path_len, size_t pi, uint8_t *tag, int actd)
{
  /* printf("%u %u %lu ", i, n, pi); print_hash(tag); printf("\n"); */
  if (n < 0 || i > n || path_len == 0 || pi < 0 || pi > path_len)
    return 1;

  if (n != 0) {
    int nactd = actd || n % 2 == 1;
    if (i % 2 == 0) {
      if (n == i || ((n == i + 1) && !actd))
        return recompute_rec(i / 2, n / 2, path, path_len, pi, tag, nactd);
      const uint8_t *phash = path[pi];
      compress(tag, phash, tag);
      return recompute_rec(i / 2, n / 2, path, path_len, pi + 1, tag, nactd);
    }
    else {
      const uint8_t *phash = path[pi];
      compress(phash, tag, tag);
    }
    return recompute_rec(i / 2, n / 2, path, path_len, pi + 1, tag, nactd);
  }

  return 0;
}

/**
 * Iterative implementation of path recomputation
 *
 * @param i index to recompute
 * @param n size of the tree
 * @param path neighbouring hashes along branches
 * @param path_len length of path
 * @param tag current tag
 * @return 0 for success, non-zero otherwise
 */
int recompute(uint32_t i, uint32_t n, uint8_t *const *path, size_t path_len, uint8_t *tag)
{
  if (n < 0 || i > n || path_len == 0)
    return 1;

  memcpy(tag, path[0], HASH_SIZE);
  size_t pi = 1;
  int inside = 1;
  while (n > 0) {
    /* printf("%u %u %lu ", i, n, pi); print_hash(tag); printf("\n"); */
    int left = i % 2 == 1; /* going up to the left */
    int skip = i == n || (i + 1 == n && inside); /* no more hashes to the right */

    if (left || !skip) {
      assert(pi < path_len);
      if (left)
          compress(path[pi], tag, tag);
      else
          compress(tag, path[pi], tag);
      pi++;
    }

    inside &= n % 2 == 0;
    i /= 2;
    n /= 2;
  }

  return 0;
}

/**
 * Merkle path verification
 *
 * @param offset 64-bit offset of the internal 32-bit tree
 * @param i index to recompute
 * @param n size of the tree
 * @param path neighbouring hashes along branches
 * @param root root of the tree
 * @return 0 for success, non-zero otherwise.
 */
int verify(uint32_t offset, uint32_t i, uint32_t n, uint8_t *const *path, size_t path_len, const uint8_t *root)
{
  uint8_t acc_rec[HASH_SIZE], acc_itr[HASH_SIZE];
  memcpy(acc_rec, path[0], HASH_SIZE);
  int r1 = recompute_rec(i - offset, n - offset, path, path_len, 1, acc_rec, 0);
  int r2 = recompute(i - offset, n - offset, path, path_len, acc_itr);
  if (r1 != 0 || r2 != 0) {
    printf("Recomputation error\n");
    return 1;
  }
  assert(memcmp(acc_rec, acc_itr, HASH_SIZE) == 0);
  return memcmp(acc_itr, root, HASH_SIZE) != 0;
}

/**
 * Various Merkle path verification tests
 */
int main(int argc, char **argv)
{
  uint8_t *root = parse_hash("50b2a21d29533d9ab25cbde1776c76db2c4eef059ad300e20335605942edb4a9");

  uint8_t *paths[4][3] = {
    {
      parse_hash("0000000000000000000000000000000000000000000000000000000000000000"),
      parse_hash("0000000000000000000000000000000000000000000000000000000000000001"),
      parse_hash("0fff9b7f003a6cffbe9db48e026410191e893f0e8519cc39262df228cde1f5d2")
    },
    {
      parse_hash("0000000000000000000000000000000000000000000000000000000000000001"),
      parse_hash("0000000000000000000000000000000000000000000000000000000000000000"),
      parse_hash("0fff9b7f003a6cffbe9db48e026410191e893f0e8519cc39262df228cde1f5d2")
    },
    {
      parse_hash("0000000000000000000000000000000000000000000000000000000000000002"),
      parse_hash("0000000000000000000000000000000000000000000000000000000000000003"),
      parse_hash("b40f7ca600e9693557a6a01a2a9288c200d14c5e76329d4d0d069cae776a096d")
    },
    {
      parse_hash("0000000000000000000000000000000000000000000000000000000000000003"),
      parse_hash("0000000000000000000000000000000000000000000000000000000000000002"),
      parse_hash("b40f7ca600e9693557a6a01a2a9288c200d14c5e76329d4d0d069cae776a096d")
    }
  };

  for (int i = 0; i < 4; i++) {
    if (verify(0, i, 4, paths[i], 3, root) != 0) {
      printf("Verification failure\n");
      exit(2);
    }
  }

  printf("All ok.\n");

  free(root);
  for (int i = 0; i < 4; i++)
    for (int j = 0; j < 3; j++)
      free(paths[i][j]);

  return 0;
}
