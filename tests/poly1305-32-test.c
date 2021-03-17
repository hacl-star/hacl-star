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
//#include <openssl/poly1305.h>
#include <sodium.h>

#include "test_helpers.h"

#include "Hacl_Poly1305_32.h"

#include "EverCrypt_AutoConfig2.h"

#include "poly1305_vectors.h"

#define ROUNDS 100000
#define SIZE   16384

void sodium_poly1305_mac(uint8_t *tag, uint32_t len, uint8_t *text, uint8_t *key){
    crypto_onetimeauth_poly1305_state ctx;
    crypto_onetimeauth_poly1305_init(&ctx, key);
    crypto_onetimeauth_poly1305_update(&ctx, text, len);
    crypto_onetimeauth_poly1305_final(&ctx, tag);
}

/*void ossl_poly1305(uint8_t *tag, uint32_t len, uint8_t *text, uint8_t *key){
    POLY1305 ctx;
    Poly1305_Init(&ctx, key);
    Poly1305_Update(&ctx, text, len);
    Poly1305_Final(&ctx, &tag);
    }*/

bool print_result(uint8_t* comp, uint8_t* exp) {
  return compare_and_print(16, comp, exp);
}

bool print_test(int in_len, uint8_t* in, uint8_t* key, uint8_t* exp){
  uint8_t comp[16] = {0};

  Hacl_Poly1305_32_poly1305_mac(comp,in_len,in,key);
  printf("Poly1305 (32-bit) Result:\n");
  bool ok = print_result(comp, exp);

  sodium_poly1305_mac(comp,in_len,in,key);
  printf("Libsodium Poly1305 Result:\n");
  ok = print_result(comp, exp);

  return ok;
}

int main() {
  EverCrypt_AutoConfig2_init();

  bool ok = true;
  for (int i = 0; i < sizeof(vectors)/sizeof(poly1305_test_vector); ++i) {
    ok &= print_test(vectors[i].input_len,vectors[i].input,vectors[i].key,vectors[i].tag);
  }

  uint8_t plain[SIZE];
  uint8_t key[32];
  uint64_t res = 0;
  uint8_t tag[16];
  cycles a,b;
  clock_t t1,t2;

  memset(plain,'P',SIZE);
  memset(key,'K',16);
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Poly1305_32_poly1305_mac(plain,SIZE,plain,key);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Poly1305_32_poly1305_mac(tag,SIZE,plain,key);
    res ^= tag[0] ^ tag[15];
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff1 = t2 - t1;
  cycles cdiff1 = b - a;

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    sodium_poly1305_mac(tag,SIZE,plain,key);
    res ^= tag[0] ^ tag[15];
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff2 = t2 - t1;
  cycles cdiff2 = b - a;


  uint64_t count = ROUNDS * SIZE;
  printf("Poly1305 (32-bit) PERF: %d\n",(int)res); print_time(count,tdiff1,cdiff1);
  printf("Libsodium Poly1305 PERF: %d\n",(int)res); print_time(count,tdiff2,cdiff2);

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
