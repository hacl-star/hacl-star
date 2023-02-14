#include <fcntl.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

#include "test_helpers.h"

#include "Hacl_Chacha20Poly1305_128.h"

#include "EverCrypt_AutoConfig2.h"

#include "chacha20poly1305_vectors.h"

#define ROUNDS 100000
#define SIZE 16384

bool
print_result(int in_len, uint8_t* comp, uint8_t* exp)
{
  return compare_and_print(in_len, comp, exp);
}

bool
print_test(int in_len,
           uint8_t* in,
           uint8_t* key,
           uint8_t* nonce,
           int aad_len,
           uint8_t* aad,
           uint8_t* exp_mac,
           uint8_t* exp_cipher)
{
  uint8_t plaintext[in_len];
  memset(plaintext, 0, in_len * sizeof plaintext[0]);
  uint8_t ciphertext[in_len];
  memset(ciphertext, 0, in_len * sizeof ciphertext[0]);
  uint8_t mac[16] = { 0 };
  bool ok = true;
  int res = 0;

  Hacl_Chacha20Poly1305_128_aead_encrypt(
    key, nonce, aad_len, aad, in_len, in, ciphertext, mac);
  printf("Chacha20Poly1305 (128-bit) Result (chacha20):\n");
  ok = print_result(in_len, ciphertext, exp_cipher);
  printf("(poly1305):\n");
  ok = ok && print_result(16, mac, exp_mac);

  res = Hacl_Chacha20Poly1305_128_aead_decrypt(
    key, nonce, aad_len, aad, in_len, plaintext, exp_cipher, exp_mac);
  if (res != 0)
    printf("AEAD Decrypt (Chacha20/Poly1305) failed \n.");
  ok = ok && (res == 0);
  ok = ok && print_result(in_len, plaintext, in);

  return ok;
}

int
main()
{
  EverCrypt_AutoConfig2_init();

  bool ok = true;
  for (int i = 0; i < sizeof(vectors) / sizeof(chacha20poly1305_test_vector);
       ++i) {
    ok &= print_test(vectors[i].input_len,
                     vectors[i].input,
                     vectors[i].key,
                     vectors[i].nonce,
                     vectors[i].aad_len,
                     vectors[i].aad,
                     vectors[i].tag,
                     vectors[i].cipher);
  }

  uint8_t plain[SIZE];
  uint8_t cipher[SIZE];
  uint8_t aead_key[32];
  uint8_t aead_nonce[12];
  int aad_len = 12;
  uint8_t aead_aad[aad_len];

  int res = 0;
  uint8_t tag[16];
  cycles a, b;
  clock_t t1, t2;

  memset(plain, 'P', SIZE);
  memset(aead_key, 'K', 32);
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20Poly1305_128_aead_encrypt(
      aead_key, aead_nonce, aad_len, aead_aad, SIZE, plain, cipher, tag);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20Poly1305_128_aead_encrypt(
      aead_key, aead_nonce, aad_len, aead_aad, SIZE, plain, cipher, tag);
    res ^= tag[0] ^ tag[15];
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff1 = t2 - t1;
  cycles cdiff1 = b - a;

  int res1 = 0;
  for (int j = 0; j < ROUNDS; j++) {
    res1 = Hacl_Chacha20Poly1305_128_aead_decrypt(
      aead_key, aead_nonce, aad_len, aead_aad, SIZE, plain, cipher, tag);
    res1 ^= res1;
  }

  res1 = 0;
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20Poly1305_128_aead_decrypt(
      aead_key, aead_nonce, aad_len, aead_aad, SIZE, plain, cipher, tag);
    res1 ^= res1;
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff2 = t2 - t1;
  cycles cdiff2 = b - a;

  // JP: I don't understand what this does since this variable is almost always
  // zeroed-out.
  printf("\n res1: %i \n", res1);

  uint64_t count = ROUNDS * SIZE;
  printf("Chacha20Poly1305 Encrypt (128-bit) PERF:\n");
  print_time(count, tdiff1, cdiff1);
  printf("Chacha20Poly1305 Decrypt (128-bit) PERF:\n");
  print_time(count, tdiff2, cdiff2);

  if (ok)
    return EXIT_SUCCESS;
  else
    return EXIT_FAILURE;
}
