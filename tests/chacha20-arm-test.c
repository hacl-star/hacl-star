#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <time.h>
#include <stdbool.h>

#include "Hacl_Chacha20.h"
#include "Hacl_Chacha20_Vec128.h"

#include "test_helpers.h"
#include "chacha20_vectors.h"

#define ROUNDS 100000
#define SIZE   8192


bool print_result(int in_len, uint8_t* comp, uint8_t* exp) {
  return compare_and_print(in_len, comp, exp);
}


bool print_test(int in_len, uint8_t* in, uint8_t* key, uint8_t* nonce, uint8_t* exp){
  uint8_t comp[in_len];
  memset(comp, 0, in_len);

  Hacl_Chacha20_chacha20_encrypt(in_len,comp,in,key,nonce,1);
  printf("Chacha20 (32-bit) Result:\n");
  bool ok = print_result(in_len,comp,exp);

  Hacl_Chacha20_Vec128_chacha20_encrypt_128(in_len,comp,in,key,nonce,1);
  printf("Chacha20 (128-bit) Result:\n");
  ok = ok && print_result(in_len,comp,exp);

  return ok;
}


int main() {
  int in_len = vectors[0].input_len;
  uint8_t *in = vectors[0].input;
  uint8_t *k = vectors[0].key;
  uint8_t *n = vectors[0].nonce;
  uint8_t *exp = vectors[0].cipher;

  bool ok = print_test(in_len,in,k,n,exp);

  uint64_t len = SIZE;
  uint8_t plain[SIZE];
  uint8_t key[16];
  uint8_t nonce[12];
  clock_t t1,t2;

  memset(plain,'P',SIZE);
  memset(key,'K',16);
  memset(nonce,'N',12);

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20_chacha20_encrypt(SIZE,plain,plain,key,nonce,1);
  }

  t1 = clock();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20_chacha20_encrypt(SIZE,plain,plain,key,nonce,1);
  }
  t2 = clock();
  double diff1 = t2 - t1;


  memset(plain,'P',SIZE);
  memset(key,'K',16);
  memset(nonce,'N',12);

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20_Vec128_chacha20_encrypt_128(SIZE,plain,plain,key,nonce,1);
  }

  t1 = clock();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20_Vec128_chacha20_encrypt_128(SIZE,plain,plain,key,nonce,1);
  }
  t2 = clock();
  double diff2 = t2 - t1;

  uint64_t count = ROUNDS * SIZE;
  printf("32-bit Chacha20\n"); print_time(count,diff1,0);
  printf("128-bit Chacha20\n"); print_time(count,diff2,0);

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;

}
