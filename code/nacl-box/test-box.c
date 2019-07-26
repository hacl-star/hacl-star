#include "kremlib.h"
#include "TestLib.h"
#include "Hacl_NaCl.h"

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

uint8_t small_order_p[box_PUBLICKEYBYTES] = {
  0xe0, 0xeb, 0x7a, 0x7c,
  0x3b, 0x41, 0xb8, 0xae,
  0x16, 0x56, 0xe3, 0xfa,
  0xf1, 0x9f, 0xc4, 0x6a,
  0xda, 0x09, 0x8d, 0xeb,
  0x9c, 0x32, 0xb1, 0xfd,
  0x86, 0x62, 0x05, 0x16,
  0x5f, 0x49, 0xb8, 0x00
};

#define PLAINLEN (16*1024)
#define ROUNDS 1000

int32_t test_api()
{
  uint8_t ciphertext[CIPHERTEXT_LEN], ciphertext1[CIPHERTEXT_LEN+16], mac[16], decrypted[MESSAGE_LEN],
          pk1[box_PUBLICKEYBYTES], pk2[box_PUBLICKEYBYTES],
	  k[box_PUBLICKEYBYTES], k1[box_PUBLICKEYBYTES];
  uint32_t res;
  int i;

  // Creating public/private key couples
  Hacl_Curve25519_51_secret_to_public(pk1, sk1);
  Hacl_Curve25519_51_secret_to_public(pk2, sk2);

  /* Testing the detach mode */
  i = Hacl_NaCl_crypto_box_detached(ciphertext, mac, msg, MESSAGE_LEN, nonce, pk1, sk2);
  res = Hacl_NaCl_crypto_box_open_detached(decrypted, ciphertext, mac, MESSAGE_LEN, nonce, pk2, sk1);
  printf("Decryption of HACL box was a %s.\n", res == 0 ? "success" : "failure");
  TestLib_compare_and_print("Box", msg, decrypted, MESSAGE_LEN);
  memset(decrypted,0,MESSAGE_LEN);

  /* Testing the combined mode */
  i = Hacl_NaCl_crypto_box_easy(ciphertext1, msg, MESSAGE_LEN, nonce, pk1, sk2);
  res = Hacl_NaCl_crypto_box_open_easy(decrypted, ciphertext1, CIPHERTEXT_LEN+16, nonce, pk2, sk1);
  printf("Decryption of HACL box_easy was a %s.\n", res == 0 ? "success" : "failure");
  TestLib_compare_and_print("Box", msg, decrypted, MESSAGE_LEN);
  memset(decrypted,0,MESSAGE_LEN);

  /* Testing the precomputed interface */
  printf("Shared Secret computed by crypto_box_beforenm:\n");
  res = Hacl_NaCl_crypto_box_beforenm(k, pk1, sk2);
  res = Hacl_NaCl_crypto_box_beforenm(k1, pk2, sk1);
  TestLib_compare_and_print("Shared Secret", k, k1, box_PUBLICKEYBYTES);

  i = Hacl_NaCl_crypto_box_detached_afternm(ciphertext, mac, msg, MESSAGE_LEN, nonce, k);
  res = Hacl_NaCl_crypto_box_open_detached_afternm(decrypted, ciphertext, mac, MESSAGE_LEN, nonce, k);
  printf("Decryption of HACL box_afternm was a %s.\n", res == 0 ? "success" : "failure");
  TestLib_compare_and_print("Box", msg, decrypted, MESSAGE_LEN);
  memset(decrypted,0,MESSAGE_LEN);


  i = Hacl_NaCl_crypto_box_easy_afternm(ciphertext1, msg, MESSAGE_LEN, nonce, k);
  res = Hacl_NaCl_crypto_box_open_easy_afternm(decrypted, ciphertext1, CIPHERTEXT_LEN+16, nonce, k);
  printf("Decryption of HACL box_easy_afternm was a %s.\n", res == 0 ? "success" : "failure");
  TestLib_compare_and_print("Box", msg, decrypted, MESSAGE_LEN);
  memset(decrypted,0,MESSAGE_LEN);

  /* This should fail */
  res = Hacl_NaCl_crypto_box_beforenm(k, small_order_p, sk2);
  printf("HACL box_beforenm was a %s.\n", res == 0 ? "failure" : "success");

  return EXIT_SUCCESS;
}

int32_t main(int argc, char *argv[])
{
    return test_api();
}
