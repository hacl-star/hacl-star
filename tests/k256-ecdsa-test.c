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
  printf("K256 ECDSA verify Result:\n");
  bool ver = Hacl_K256_ECDSA_ecdsa_verify_sha256(msg_len, msg, pk_x, pk_y, sgnt_r, sgnt_s);
  if (ver == valid) printf("Success! %d \n", id);
  else printf("Failed %d \n", id);
  return (ver == valid);
}


int main() {
  bool ok = true;
  for (int i = 0; i < sizeof(vectors)/sizeof(k256ecdsa_verify_test_vector); ++i) {
    ok &= print_test(vectors[i].pk_x,vectors[i].pk_y,vectors[i].msg_len,vectors[i].msg,
                     vectors[i].sgnt_r,vectors[i].sgnt_s,vectors[i].id,vectors[i].valid);
  }

  if (ok)
    printf ("\n Success :) \n");
  else
    printf ("\n Failed :( \n");

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
