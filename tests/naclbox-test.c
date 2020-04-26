#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#include "Hacl_NaCl.h"

#include "test_helpers.h"
#include "naclbox_vectors.h"


bool print_result(int in_len, uint8_t* comp, uint8_t* exp) {
  return compare_and_print(in_len, comp, exp);
}

bool print_test(int in_len, uint8_t* in, uint8_t* nonce, uint8_t* sk1, uint8_t* sk2, uint8_t* cipher, uint8_t* mac_exp) {
  uint8_t ciphertext[in_len];
  uint8_t mac[MACBYTES];
  uint8_t ciphertext1[in_len+MACBYTES];
  uint8_t decrypted[in_len];
  uint8_t pk1[KEYBYTES];
  uint8_t pk2[KEYBYTES];
  uint8_t k[KEYBYTES];
  uint8_t k1[KEYBYTES];

  uint32_t res;
  int i;

  /* Creating public/private key couples */
  Hacl_Curve25519_51_secret_to_public(pk1, sk1);
  Hacl_Curve25519_51_secret_to_public(pk2, sk2);

  /* Testing the detach mode */
  i = Hacl_NaCl_crypto_box_detached(ciphertext, mac, in, in_len, nonce, pk1, sk2);
  bool ok = print_result(in_len, ciphertext, cipher);
  ok = ok && print_result(MACBYTES, mac, mac_exp);
  res = Hacl_NaCl_crypto_box_open_detached(decrypted, ciphertext, mac, in_len, nonce, pk2, sk1);
  printf("Decryption of HACL box was a %s.\n", res == 0 ? "success" : "failure");
  ok = (res == 0) && print_result(in_len, in, decrypted);
  memset(decrypted,0,in_len);

  /* Testing the combined mode */
  i = Hacl_NaCl_crypto_box_easy(ciphertext1, in, in_len, nonce, pk1, sk2);
  res = Hacl_NaCl_crypto_box_open_easy(decrypted, ciphertext1, in_len+MACBYTES, nonce, pk2, sk1);
  printf("Decryption of HACL box_easy was a %s.\n", res == 0 ? "success" : "failure");
  ok = (res == 0) && ok && print_result(in_len, in, decrypted);
  memset(decrypted,0,in_len);

  /* Testing the precomputed interface */
  printf("Shared Secret computed by crypto_box_beforenm:\n");
  res = Hacl_NaCl_crypto_box_beforenm(k, pk1, sk2);
  res = Hacl_NaCl_crypto_box_beforenm(k1, pk2, sk1);
  ok = ok && print_result(KEYBYTES, k, k1);

  i = Hacl_NaCl_crypto_box_detached_afternm(ciphertext, mac, in, in_len, nonce, k);
  res = Hacl_NaCl_crypto_box_open_detached_afternm(decrypted, ciphertext, mac, in_len, nonce, k);
  printf("Decryption of HACL box_afternm was a %s.\n", res == 0 ? "success" : "failure");
  ok = (res == 0) && ok && print_result(in_len, in, decrypted);
  memset(decrypted,0,in_len);


  i = Hacl_NaCl_crypto_box_easy_afternm(ciphertext1, in, in_len, nonce, k);
  res = Hacl_NaCl_crypto_box_open_easy_afternm(decrypted, ciphertext1, in_len+MACBYTES, nonce, k);
  printf("Decryption of HACL box_easy_afternm was a %s.\n", res == 0 ? "success" : "failure");
  ok = (res == 0) && ok && print_result(in_len, in, decrypted);
  memset(decrypted,0,in_len);

  return ok;
}

int main()
{
  int in_len = vectors[0].input_len;
  uint8_t *in = vectors[0].input;
  uint8_t *nonce = vectors[0].nonce;
  uint8_t *sk1 = vectors[0].secretkey1;
  uint8_t *sk2 = vectors[0].secretkey2;
  uint8_t *cipher = vectors[0].cipher;
  uint8_t *mac = vectors[0].mac;

  bool ok = print_test(in_len,in,nonce,sk1,sk2,cipher,mac);

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
