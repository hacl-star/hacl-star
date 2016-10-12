#include "testlib.h"
#include "Hacl_Box.h"
#include <sodium.h>

#define MESSAGE_LEN 4
#define secretbox_MACBYTES   16
#define CIPHERTEXT_LEN (secretbox_MACBYTES + MESSAGE_LEN)
#define secretbox_NONCEBYTES 24
#define secretbox_KEYBYTES   32
#define box_MACBYTES         16
#define box_PUBLICKEYBYTES   32
#define box_SECRETKEYBYTES   32
#define box_NONCEBYTES       24

uint8_t *msg = (uint8_t*) "test";

uint8_t nonce[secretbox_NONCEBYTES] = {
  0x00, 0x01, 0x02, 0x03,
  0x04, 0x05, 0x06, 0x07,
  0x08, 0x09, 0x10, 0x11,
  0x12, 0x13, 0x14, 0x15,
  0x16, 0x17, 0x18, 0x19,
  0x20, 0x21, 0x22, 0x23,
};

uint8_t key[secretbox_KEYBYTES] = {
  0x85, 0xd6, 0xbe, 0x78,
  0x57, 0x55, 0x6d, 0x33,
  0x7f, 0x44, 0x52, 0xfe,
  0x42, 0xd5, 0x06, 0xa8,
  0x01, 0x03, 0x80, 0x8a,
  0xfb, 0x0d, 0xb2, 0xfd,
  0x4a, 0xbf, 0xf6, 0xaf,
  0x41, 0x49, 0xf5, 0x1b
};

uint8_t sk[secretbox_KEYBYTES] = {
  0x85, 0xd6, 0xbe, 0x78,
  0x57, 0x55, 0x6d, 0x33,
  0x7f, 0x44, 0x52, 0xfe,
  0x42, 0xd5, 0x06, 0xa8,
  0x01, 0x03, 0x80, 0x8a,
  0xfb, 0x0d, 0xb2, 0xfd,
  0x4a, 0xbf, 0xf6, 0xaf,
  0x41, 0x49, 0xf5, 0x1c
};

int main(){
  if (sodium_init() == -1) {
    return EXIT_FAILURE;
  }
  uint8_t ciphertext[CIPHERTEXT_LEN], ciphertext2[CIPHERTEXT_LEN],
    mac[16],mac2[16],
    decrypted[MESSAGE_LEN], decrypted2[MESSAGE_LEN],
    pk[box_PUBLICKEYBYTES], pk2[box_PUBLICKEYBYTES],
    test[32], test2[32],
    basepoint[box_SECRETKEYBYTES] = {9};
  uint32_t res;
  int i;
  /* Testing the secret box primitives */  
  Hacl_SecretBox_crypto_secretbox_detached(ciphertext, mac, msg, MESSAGE_LEN, nonce, key);
  crypto_secretbox_detached(ciphertext2, mac2, msg, MESSAGE_LEN, nonce, key);

  res = crypto_secretbox_open_detached(decrypted, ciphertext, mac, MESSAGE_LEN, nonce, key);
  printf("SecretBox decryption with libsodium was a %s.\n", res == 0 ? "success" : "failure");
  compare_and_print("Secret box", msg, decrypted, MESSAGE_LEN);

  for(i = 0; i < MESSAGE_LEN; i++) decrypted[i] = 0;
  for(i = 0; i < CIPHERTEXT_LEN; i++) ciphertext[i] = 0;
  
  /* Public key initialization */
  Hacl_EC_Curve25519_exp(pk , basepoint, key);
  Hacl_EC_Curve25519_exp(pk2, basepoint, sk);
  Hacl_EC_Curve25519_exp(test, pk2, key);
  Hacl_EC_Curve25519_exp(test2, pk, sk);
  uint8_t empty[16] = {0};
  Hacl_Symmetric_XSalsa20_hsalsa_init(test, test2, empty);
  i = crypto_box_beforenm(test2, pk2, key);
  compare_and_print("Beforenm", test2, test, 32);

  /* Testing the box primitives */
  Hacl_Box_crypto_box_detached(ciphertext, mac, msg, MESSAGE_LEN, nonce, pk, sk);  
  res = crypto_box_open_detached(decrypted, ciphertext, mac, MESSAGE_LEN, nonce, pk2, key);
  printf("Box decryption with libsodium was a %s.\n", res == 0 ? "success" : "failure");
  
  compare_and_print("Box", msg, decrypted, MESSAGE_LEN);
  return EXIT_SUCCESS;
}
