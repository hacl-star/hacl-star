#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdbool.h>
#include <time.h>

#include "Hacl_K256_ECDSA.h"

#include "test_helpers.h"
#include "k256-ecdsa_vectors.h"

bool print_test(
  uint8_t *pk_x, // 32 bytes
  uint8_t *pk_y, // 32 bytes
  size_t msg_len,
  uint8_t *msg,
  uint8_t *sgnt_r, // 32 bytes
  uint8_t *sgnt_s, // 32 bytes
  int id,
  bool valid
){
  uint8_t pk_raw[64];
  memcpy(pk_raw, pk_x, (uint32_t)32U * sizeof (uint8_t));
  memcpy(pk_raw + (uint32_t)32U, pk_y, (uint32_t)32U * sizeof (uint8_t));

  printf("K256 ECDSA verify Result: ");
  bool ver = Hacl_K256_ECDSA_ecdsa_verify_sha256(msg_len, msg, pk_raw, sgnt_r, sgnt_s);
  if (ver == valid) printf("Success! %d \n", id);
  else printf("Failed %d \n", id);
  return (ver == valid);
}


bool test_public_key_compressed(
  uint8_t *pk_x, // 32 bytes
  uint8_t *pk_y, // 32 bytes
  int id)
{
  uint8_t pk_raw[64];
  memcpy(pk_raw, pk_x, (uint32_t)32U * sizeof (uint8_t));
  memcpy(pk_raw + (uint32_t)32U, pk_y, (uint32_t)32U * sizeof (uint8_t));

  uint8_t pk_c[33U] = { 0U };
  uint8_t pk_raw_c[64U] = { 0U };
  Hacl_K256_ECDSA_public_key_compressed_from_raw(pk_c, pk_raw);
  bool b = Hacl_K256_ECDSA_public_key_compressed_to_raw(pk_raw_c, pk_c);

  printf("K256 public-key-compressed Result %d : ", id);
  if (!b) {
    printf("Failed (None)! \n");
    return false;
  }

  bool ver = compare(64U, pk_raw, pk_raw_c);
  return ver;
}


bool test_public_key_uncompressed(
  uint8_t *pk_x, // 32 bytes
  uint8_t *pk_y, // 32 bytes
  int id)
{
  uint8_t pk_raw[64];
  memcpy(pk_raw, pk_x, (uint32_t)32U * sizeof (uint8_t));
  memcpy(pk_raw + (uint32_t)32U, pk_y, (uint32_t)32U * sizeof (uint8_t));

  uint8_t pk_u[65U] = { 0U };
  uint8_t pk_raw_u[64U] = { 0U };
  Hacl_K256_ECDSA_public_key_uncompressed_from_raw(pk_u, pk_raw);
  bool b = Hacl_K256_ECDSA_public_key_uncompressed_to_raw(pk_raw_u, pk_u);

  printf("K256 public-key-uncompressed Result %d : ", id);
  if (!b) {
    printf("Failed (None)! \n");
    return false;
  }

  bool ver = compare(64U, pk_raw, pk_raw_u);
  return ver;
}


int main() {
  bool ok = true;
  for (int i = 0; i < sizeof(vectors)/sizeof(k256ecdsa_verify_test_vector); ++i) {
    ok &= print_test(vectors[i].pk_x,vectors[i].pk_y,vectors[i].msg_len,vectors[i].msg,
                     vectors[i].sgnt_r,vectors[i].sgnt_s,vectors[i].id,vectors[i].valid);
    ok &= test_public_key_uncompressed(vectors[i].pk_x,vectors[i].pk_y,vectors[i].id);
    ok &= test_public_key_compressed(vectors[i].pk_x,vectors[i].pk_y,vectors[i].id);
    printf("\n");
  }

  if (ok)
    printf ("\n Success :) \n");
  else
    printf ("\n Failed :( \n");

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
