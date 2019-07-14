#include "kremlib.h"
#include "TestLib.h"
#include "Hacl_NaCl.h"
#include "sodium.h"

#define MESSAGE_LEN 72
#define secretbox_MACBYTES   16
#define CIPHERTEXT_LEN       MESSAGE_LEN
#define secretbox_NONCEBYTES 24
#define secretbox_KEYBYTES   32
#define box_MACBYTES         16
#define box_PUBLICKEYBYTES   32
#define box_SECRETKEYBYTES   32
#define box_NONCEBYTES       24

uint8_t msg[MESSAGE_LEN] = {
  0x00, 0x01, 0x02, 0x03,  0x04, 0x05, 0x06, 0x07,
  0x08, 0x09, 0x10, 0x11,  0x12, 0x13, 0x14, 0x15,
  0x16, 0x17, 0x18, 0x19,  0x20, 0x21, 0x22, 0x23,
  0x00, 0x01, 0x02, 0x03,  0x04, 0x05, 0x06, 0x07,
  0x08, 0x09, 0x10, 0x11,  0x12, 0x13, 0x14, 0x15,
  0x16, 0x17, 0x18, 0x19,  0x20, 0x21, 0x22, 0x23,
  0x00, 0x01, 0x02, 0x03,  0x04, 0x05, 0x06, 0x07,
  0x08, 0x09, 0x10, 0x11,  0x12, 0x13, 0x14, 0x15,
  0x16, 0x17, 0x18, 0x19,  0x20, 0x21, 0x22, 0x23,
};

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


uint8_t sk1[secretbox_KEYBYTES] = {
  0x85, 0xd6, 0xbe, 0x78,
  0x57, 0x55, 0x6d, 0x33,
  0x7f, 0x44, 0x52, 0xfe,
  0x42, 0xd5, 0x06, 0xa8,
  0x01, 0x03, 0x80, 0x8a,
  0xfb, 0x0d, 0xb2, 0xfd,
  0x4a, 0xbf, 0xf6, 0xaf,
  0x41, 0x49, 0xf5, 0x1b
};
uint8_t sk2[secretbox_KEYBYTES] = {
  0x85, 0xd6, 0xbe, 0x78,
  0x57, 0x55, 0x6d, 0x33,
  0x7f, 0x44, 0x52, 0xfe,
  0x42, 0xd5, 0x06, 0xa8,
  0x01, 0x03, 0x80, 0x8a,
  0xfb, 0x0d, 0xb2, 0xfd,
  0x4a, 0xbf, 0xf6, 0xaf,
  0x41, 0x49, 0xf5, 0x1c
};


#define PLAINLEN (16*1024)
#define ROUNDS 1000

int32_t test_api()
{
  uint8_t ciphertext[CIPHERTEXT_LEN+16], mac[16], decrypted[MESSAGE_LEN],
          test1[box_PUBLICKEYBYTES], test2[box_PUBLICKEYBYTES],
          pk1[box_PUBLICKEYBYTES], pk2[box_PUBLICKEYBYTES],
          basepoint[box_PUBLICKEYBYTES] = {9};
  uint32_t res;
  int i;

  // Creating public/private key couples
  Hacl_Curve25519_51_secret_to_public(pk1, sk1);
  Hacl_Curve25519_51_secret_to_public(pk2, sk2);

  /* Testing the box primitives */
  i = Hacl_NaCl_crypto_box_detached(ciphertext+16, mac, msg, MESSAGE_LEN, nonce, pk1, sk2);
  res = crypto_box_open_detached(decrypted, ciphertext+16, mac, MESSAGE_LEN, nonce, pk2, sk1);
  printf("Libsodium decryption of HACL box was a %s.\n", res == 0 ? "success" : "failure");
  TestLib_compare_and_print("Box", msg, decrypted, MESSAGE_LEN);
  memset(decrypted,0,MESSAGE_LEN);

  i = crypto_box_detached(ciphertext+16, mac, msg, MESSAGE_LEN, nonce, pk1, sk2);
  res = Hacl_NaCl_crypto_box_open_detached(decrypted, ciphertext+16, mac, MESSAGE_LEN, nonce, pk2, sk1);
  printf("HACL decryption of Libsodium box was a %s.\n", res == 0 ? "success" : "failure");
  TestLib_compare_and_print("Box", msg, decrypted, MESSAGE_LEN);
  memset(decrypted,0,MESSAGE_LEN);

  i = Hacl_NaCl_crypto_box_easy(ciphertext, msg, MESSAGE_LEN, nonce, pk1, sk2);
  res = crypto_box_open_easy(decrypted, ciphertext, MESSAGE_LEN+16, nonce, pk2, sk1);
  printf("Libsodium decryption of HACL box_easy was a %s.\n", res == 0 ? "success" : "failure");
  TestLib_compare_and_print("Box", msg, decrypted, MESSAGE_LEN);
  memset(decrypted,0,MESSAGE_LEN);

  i = crypto_box_easy(ciphertext, msg, MESSAGE_LEN, nonce, pk1, sk2);
  res = Hacl_NaCl_crypto_box_open_easy(decrypted, ciphertext, MESSAGE_LEN+16, nonce, pk2, sk1);
  printf("Box decryption of libsodium box easy was a %s.\n", res == 0 ? "success" : "failure");
  TestLib_compare_and_print("Box", msg, decrypted, MESSAGE_LEN);
  memset(decrypted,0,MESSAGE_LEN);

  return EXIT_SUCCESS;
}

int32_t main(int argc, char *argv[])
{
    return test_api();
}
