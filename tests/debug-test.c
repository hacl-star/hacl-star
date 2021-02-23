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

#include "test_helpers.h"

#include "Hacl_Poly1305_32.h"
#include "Hacl_Poly1305_128.h"
#include "EverCrypt_AutoConfig2.h"

#include "poly1305_vectors.h"

#define ROUNDS 100000
#define SIZE   16384

bool print_result(uint8_t* comp, uint8_t* exp) {
  return compare_and_print(16, comp, exp);
}

bool print_test(int in_len, uint8_t* in, uint8_t* key, uint8_t* exp){
  uint8_t comp[16] = {0};

  Hacl_Poly1305_32_poly1305_mac(comp,in_len,in,key);
  printf("Poly1305 (32-bit) Result:\n");
  bool ok = print_result(comp, exp);

  Hacl_Poly1305_128_poly1305_mac(comp,in_len,in,key);
  printf("Poly1305 (128-bit) Result:\n");
  ok = ok && print_result(comp, exp);

  return ok;
}

int main() {
  EverCrypt_AutoConfig2_init();

  bool ok = true;
  for (int i = 0; i < sizeof(vectors)/sizeof(poly1305_test_vector); ++i) {
    ok &= print_test(vectors[i].input_len,vectors[i].input,vectors[i].key,vectors[i].tag);
  }

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
