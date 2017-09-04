#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <time.h>

#include "haclnacl.h"
#include "tweetnacl.h"
#include "hacl_test_utils.h"

#define HACL_UNIT_TESTS_SIZE (1 * 1024)
#define POLY_MACSIZE 16
#define POLY_BLOCKSIZE 16
#define POLY_KEYSIZE 32
#define CHACHA_BLOCKSIZE 64
#define CHACHA_KEYSIZE 32
#define SALSA_BLOCK_SIZE 64

/* Try to read bytes, return if fails */
#define READ_RANDOM_BYTES(len, buf) \
  if (! (read_random_bytes((len), (buf)))) return false


uint8_t
chacha_plaintext[114] =
    {
      0x4c,      0x61,      0x64,      0x69,      0x65,      0x73,      0x20,      0x61,
      0x6e,      0x64,      0x20,      0x47,      0x65,      0x6e,      0x74,      0x6c,
      0x65,      0x6d,      0x65,      0x6e,      0x20,      0x6f,      0x66,      0x20,
      0x74,      0x68,      0x65,      0x20,      0x63,      0x6c,      0x61,      0x73,
      0x73,      0x20,      0x6f,      0x66,      0x20,      0x27,      0x39,      0x39,
      0x3a,      0x20,      0x49,      0x66,      0x20,      0x49,      0x20,      0x63,
      0x6f,      0x75,      0x6c,      0x64,      0x20,      0x6f,      0x66,      0x66,
      0x65,      0x72,      0x20,      0x79,      0x6f,      0x75,      0x20,      0x6f,
      0x6e,      0x6c,      0x79,      0x20,      0x6f,      0x6e,      0x65,      0x20,
      0x74,      0x69,      0x70,      0x20,      0x66,      0x6f,      0x72,      0x20,
      0x74,      0x68,      0x65,      0x20,      0x66,      0x75,      0x74,      0x75,
      0x72,      0x65,      0x2c,      0x20,      0x73,      0x75,      0x6e,      0x73,
      0x63,      0x72,      0x65,      0x65,      0x6e,      0x20,      0x77,      0x6f,
      0x75,      0x6c,      0x64,      0x20,      0x62,      0x65,      0x20,      0x69,
      0x74,      0x2e
    };
uint8_t
chacha_ciphertext[114] =
    {
      0x6e,      0x2e,      0x35,      0x9a,      0x25,      0x68,      0xf9,      0x80,
      0x41,      0xba,      0x07,      0x28,      0xdd,      0x0d,      0x69,      0x81,
      0xe9,      0x7e,      0x7a,      0xec,      0x1d,      0x43,      0x60,      0xc2,
      0x0a,      0x27,      0xaf,      0xcc,      0xfd,      0x9f,      0xae,      0x0b,
      0xf9,      0x1b,      0x65,      0xc5,      0x52,      0x47,      0x33,      0xab,
      0x8f,      0x59,      0x3d,      0xab,      0xcd,      0x62,      0xb3,      0x57,
      0x16,      0x39,      0xd6,      0x24,      0xe6,      0x51,      0x52,      0xab,
      0x8f,      0x53,      0x0c,      0x35,      0x9f,      0x08,      0x61,      0xd8,
      0x07,      0xca,      0x0d,      0xbf,      0x50,      0x0d,      0x6a,      0x61,
      0x56,      0xa3,      0x8e,      0x08,      0x8a,      0x22,      0xb6,      0x5e,
      0x52,      0xbc,      0x51,      0x4d,      0x16,      0xcc,      0xf8,      0x06,
      0x81,      0x8c,      0xe9,      0x1a,      0xb7,      0x79,      0x37,      0x36,
      0x5a,      0xf9,      0x0b,      0xbf,      0x74,      0xa3,      0x5b,      0xe6,
      0xb4,      0x0b,      0x8e,      0xed,      0xf2,      0x78,      0x5e,      0x42,
      0x87,      0x4d
    };
uint8_t
chacha_key[32] =
    {
      0,      1,      2,      3,      4,      5,      6,      7,
      8,      9,     10,     11,     12,     13,     14,     15,
      16,    17,     18,     19,     20,     21,     22,     23,
      24,    25,     26,     27,     28,     29,     30,     31
    };
uint8_t
chacha_nonce[12] =
    {
      0,      0,      0,      0,      0,      0,      0,      0x4a,
      0,      0,      0,      0    
    };



uint8_t aead_nonce[12] = {0x07,0x00,0x00,0x00,0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47};

uint8_t aead_key[32] = {
    	0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,0x88,0x89,0x8a,0x8b,0x8c,0x8d,0x8e,0x8f,
	0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,0x98,0x99,0x9a,0x9b,0x9c,0x9d,0x9e,0x9f
};

uint8_t aead_aad[12] = {
        0x50,0x51,0x52,0x53,0xc0,0xc1,0xc2,0xc3,0xc4,0xc5,0xc6,0xc7
};

uint8_t aead_ciphertext[114] = {
        0xd3,0x1a,0x8d,0x34,0x64,0x8e,0x60,0xdb,0x7b,0x86,0xaf,0xbc,0x53,0xef,0x7e,0xc2,
	0xa4,0xad,0xed,0x51,0x29,0x6e,0x08,0xfe,0xa9,0xe2,0xb5,0xa7,0x36,0xee,0x62,0xd6,
	0x3d,0xbe,0xa4,0x5e,0x8c,0xa9,0x67,0x12,0x82,0xfa,0xfb,0x69,0xda,0x92,0x72,0x8b,
	0x1a,0x71,0xde,0x0a,0x9e,0x06,0x0b,0x29,0x05,0xd6,0xa5,0xb6,0x7e,0xcd,0x3b,0x36,
	0x92,0xdd,0xbd,0x7f,0x2d,0x77,0x8b,0x8c,0x98,0x03,0xae,0xe3,0x28,0x09,0x1b,0x58,
	0xfa,0xb3,0x24,0xe4,0xfa,0xd6,0x75,0x94,0x55,0x85,0x80,0x8b,0x48,0x31,0xd7,0xbc,
	0x3f,0xf4,0xde,0xf0,0x8e,0x4b,0x7a,0x9d,0xe5,0x76,0xd2,0x65,0x86,0xce,0xc6,0x4b,
	0x61,0x16
};

uint8_t aead_mac[16] = {
        0x1a,0xe1,0x0b,0x59,0x4f,0x09,0xe2,0x6a,0x7e,0x90,0x2e,0xcb,0xd0,0x60,0x06,0x91

};

bool unit_test_chacha20(){
  int a;
  bool pass = true;

  uint8_t ciphertext[114];
  memset(ciphertext, 0, 114 * sizeof ciphertext[0]);
  uint32_t counter = (uint32_t )1;
  chacha20(ciphertext,chacha_plaintext,114, chacha_key, chacha_nonce, counter);

    a = memcmp(ciphertext, chacha_ciphertext, 114 * sizeof (uint8_t));
    if (a != 0){
      pass = false;
      printf("Chacha20 failed on RFC test of size 114\n.");
    }
  return pass;
}

bool unit_test_aead(){
  int a;
  bool pass = true;

  uint8_t plaintext[114];
  memset(plaintext, 0, 114 * sizeof plaintext[0]);
  uint8_t ciphertext[114];
  memset(ciphertext, 0, 114 * sizeof ciphertext[0]);
  uint8_t mac[16];
  memset(mac, 0, 16 * sizeof mac[0]);

  a = aead_chacha20_poly1305_encrypt(ciphertext,mac,chacha_plaintext,114, aead_aad,12, aead_key, aead_nonce);
  if (a != 0){
    pass = false;
    printf("AEAD (Chacha20/Poly1305) failed on RFC test of size 114\n.");
    goto result;
  }
  a = memcmp(ciphertext, aead_ciphertext, 114 * sizeof (uint8_t));
  if (a != 0){
    pass = false;
    printf("AEAD (Chacha20) failed on RFC test of size 114\n.");
    goto result;
  }
  a = memcmp(mac, aead_mac, 16 * sizeof (uint8_t));
  if (a != 0){
    pass = false;
    printf("AEAD (Poly1305) failed on RFC test of size 114\n.");
    goto result;
  }
  
  a = aead_chacha20_poly1305_decrypt(plaintext,aead_ciphertext, 114, aead_mac, aead_aad, 12, aead_key, aead_nonce);
  if (a != 0){
    pass = false;
    printf("AEAD Decrypt (Chacha20/Poly1305) failed on RFC test of size 114\n.");
    goto result;
  }
  a = memcmp(plaintext, chacha_plaintext, 114 * sizeof (uint8_t));
  if (a != 0){
    pass = false;
    printf("AEAD Decrypt (Chacha20/Poly1305) failed on RFC test of size 114\n.");
    goto result;
  }

result:
  return pass;
}


bool unit_test_onetimeauth(){
  // Global length
  uint64_t len = HACL_UNIT_TESTS_SIZE * sizeof(uint8_t);
  // Scratch buffers
  uint8_t hacl_mac[POLY_MACSIZE], expected_mac[POLY_MACSIZE], key[POLY_KEYSIZE];
  uint8_t *plaintext = malloc(HACL_UNIT_TESTS_SIZE * sizeof (uint8_t));
  // Initializing random plaintext
  READ_RANDOM_BYTES(HACL_UNIT_TESTS_SIZE, plaintext);
  // Tests
  int a;
  bool pass = true;
  for (int i = 0; i < 3 * POLY_BLOCKSIZE; i++){
    // Testing crypto_onetimeauth on different length
    tweet_crypto_onetimeauth(expected_mac, plaintext, i, key);
    crypto_onetimeauth(hacl_mac, plaintext, i, key);
    a = memcmp(hacl_mac, expected_mac, 16 * sizeof (uint8_t));
    if (a != 0){
      pass = false;
      printf("Poly1305 failed on input of size %d\n.", i);
      break;
    }
    // Testing crypto_onetimeauth verify on different length
    a = crypto_onetimeauth_verify(hacl_mac, plaintext, i, key);
    if (a != 0){
      pass = false;
      printf("Poly1305 verify failed on input of size %d\n.", i);
      break;
    }
    hacl_mac[i%16] = ~(hacl_mac[i%16]);
    // Testing crypto_onetimeauth proper failure on different length
    a = crypto_onetimeauth_verify(hacl_mac, plaintext, i, key);
    if (a == 0){
      pass = false;
      printf("Poly1305 verify fail failed on input of size %d\n.", i);
      break;
    }
  }
  tweet_crypto_onetimeauth(expected_mac, plaintext, HACL_UNIT_TESTS_SIZE, key);
  crypto_onetimeauth(hacl_mac, plaintext, HACL_UNIT_TESTS_SIZE, key);
  a = memcmp(hacl_mac, expected_mac, 16 * sizeof (uint8_t));
  if (a != 0){
    pass = false;
    printf("Poly1305 failed on input of size %d\n.", HACL_UNIT_TESTS_SIZE);
  }

  free(plaintext);

  return pass;
}

#define crypto_box_ZEROBYTES 32
#define crypto_box_BOXZEROBYTES 16

bool unit_test_crypto_box(){
  // Global length
  uint64_t len = HACL_UNIT_TESTS_SIZE * sizeof(uint8_t);
  // Scratch buffers
  uint8_t hacl_cipher[HACL_UNIT_TESTS_SIZE + 32], expected_cipher[HACL_UNIT_TESTS_SIZE + 32];
  // Generation of the public/secret key couple
  uint8_t sk1[32], pk1[32];
  uint8_t sk2[32], pk2[32];
  tweet_crypto_box_keypair(pk1, sk1);
  tweet_crypto_box_keypair(pk2, sk2);
  // Random plaintext
  uint8_t *plaintext = malloc((HACL_UNIT_TESTS_SIZE + crypto_box_ZEROBYTES) * sizeof (uint8_t));
  READ_RANDOM_BYTES(len, plaintext + crypto_box_ZEROBYTES);
  for (int i = 0; i < crypto_box_ZEROBYTES; i++) plaintext[i] = 0;
  // Random plaintext
  uint8_t nonce[24];
  READ_RANDOM_BYTES(24, nonce);
  // Test 1
  int a;
  bool pass = true;
  for (int i = 0; i < 3 * CHACHA_BLOCKSIZE; i++){
    tweet_crypto_box(expected_cipher, plaintext, crypto_box_ZEROBYTES + i, nonce, pk1, sk2);
    crypto_box(hacl_cipher, plaintext, crypto_box_ZEROBYTES + i, nonce, pk1, sk2);
    a = memcmp(hacl_cipher, expected_cipher, (crypto_box_ZEROBYTES + i) * sizeof (uint8_t));
    if (a != 0){
      pass = false;
      printf("BOX failed on input of size %d\n.", i);
      break;
    }
    a = crypto_box_open(hacl_cipher, expected_cipher, i + crypto_box_ZEROBYTES, nonce, pk2, sk1);
    if (a != 0) {
      pass = false;
      printf("BOX OPEN failed to verify on input of size %d\n", i);
      break;
    }
    a = memcmp(hacl_cipher, plaintext, (crypto_box_ZEROBYTES + i) * sizeof (uint8_t));
    if (a != 0) {
      pass = false;
      printf("BOX OPEN failed on input of size %d\n", i);
      break;
    }
  }
  if (!pass) return pass;

  // Test 2
  tweet_crypto_box(expected_cipher, plaintext, crypto_box_ZEROBYTES + HACL_UNIT_TESTS_SIZE, nonce, pk1, sk2);
  crypto_box(hacl_cipher, plaintext, crypto_box_ZEROBYTES + HACL_UNIT_TESTS_SIZE, nonce, pk1, sk2);
  a = memcmp(hacl_cipher, expected_cipher, (crypto_box_ZEROBYTES + HACL_UNIT_TESTS_SIZE) * sizeof (uint8_t));
  if (a != 0){
    pass = false;
    printf("BOX failed on input of size %d\n.", HACL_UNIT_TESTS_SIZE);
  }
  a = crypto_box_open(hacl_cipher, expected_cipher, HACL_UNIT_TESTS_SIZE + crypto_box_ZEROBYTES, nonce, pk2, sk1);
  if (a != 0) {
    pass = false;
    printf("BOX OPEN failed to verify on input of size %d\n", HACL_UNIT_TESTS_SIZE);
  }
  a = memcmp(hacl_cipher, plaintext, (crypto_box_ZEROBYTES + HACL_UNIT_TESTS_SIZE) * sizeof (uint8_t));
  if (a != 0) {
    pass = false;
    printf("BOX OPEN failed on input of size %d\n", HACL_UNIT_TESTS_SIZE);
  }

  free(plaintext);

  return pass;
}

#define NUM_SCALARMULT 1000

bool unit_test_scalarmult(){
  // Random key values
  uint8_t *random_bytes = malloc(32 * NUM_SCALARMULT * sizeof(uint8_t));
  READ_RANDOM_BYTES(32 * NUM_SCALARMULT, random_bytes);
  // Storage buffers
  uint8_t expected_bytes[32], hacl_bytes[32];
  int a, b;
  bool pass = true;
  for (int i = 0; i < NUM_SCALARMULT; i++){
    b = tweet_crypto_scalarmult_base(expected_bytes, random_bytes + 32 * i);
    b =crypto_scalarmult_base(hacl_bytes, random_bytes + 32 * i);
    a = memcmp(hacl_bytes, expected_bytes, 16 * sizeof (uint8_t));
    if (a != 0){
      pass = false;
      printf("Scalarmult base failed\n");
      break;
    }
  }
  for (int i = 0; i < NUM_SCALARMULT / 2; i++){
    b = tweet_crypto_scalarmult(expected_bytes, random_bytes + 32 * 2 * i, random_bytes + 32 * (2 * i + 1));
    b = crypto_scalarmult(hacl_bytes, random_bytes + 32 * 2 * i, random_bytes + 32 * (2 * i + 1));
    a = memcmp(hacl_bytes, expected_bytes, 16 * sizeof (uint8_t));
    if (a != 0){
      pass = false;
      printf("crypto_scalarmult failed\n");
      break;
    }
  }

  free(random_bytes);

  return pass;
}

#define NUM_KEYPAIR 1000

bool unit_test_crypto_keypair(){
  // Random key values
  uint8_t sk_bytes[64 * NUM_KEYPAIR];
  uint8_t expected_pk_bytes[32 * NUM_KEYPAIR];
  uint8_t hacl_pk_bytes[32 * NUM_KEYPAIR];
  for (int i = 0; i < NUM_KEYPAIR; i++){
    tweet_crypto_sign_keypair(expected_pk_bytes + 32 * i, sk_bytes + 64 * i);
    crypto_sign_secret_to_public(hacl_pk_bytes + 32 * i, sk_bytes + 64 * i);
  }
  int a = memcmp(hacl_pk_bytes, expected_pk_bytes, 32 * NUM_KEYPAIR * sizeof(uint8_t));
  bool pass = true;
  if (a != 0){
    pass = false;
    printf("Crypto keypair failed\n");
  }
  return pass;
}

bool unit_test_crypto_sign(){
  uint64_t len = HACL_UNIT_TESTS_SIZE * sizeof(uint8_t);
  uint8_t *plaintext = malloc(HACL_UNIT_TESTS_SIZE * sizeof (uint8_t));
  uint8_t *expected_signed_msg = malloc((HACL_UNIT_TESTS_SIZE+64) * sizeof (uint8_t));
  uint8_t *hacl_signed_msg = malloc((HACL_UNIT_TESTS_SIZE+64) * sizeof (uint8_t));
  uint8_t sk[64], pk[32];
  crypto_sign_keypair(pk, sk);
  READ_RANDOM_BYTES(len, plaintext);
  int a;
  bool pass = true;
  long long unsigned int smlen;
  for (int i = 0; i < 256; i++){
    tweet_crypto_sign(expected_signed_msg, &smlen, plaintext, i, sk);
    crypto_sign(hacl_signed_msg, &smlen, plaintext, i, sk);
    a = memcmp(hacl_signed_msg, expected_signed_msg, (i+64) * sizeof(uint8_t));
    if (a != 0){
      pass = false;
      printf("crypto_sign failed on input of size %d\n", i);
      break;
    }
    pass = crypto_sign_open(hacl_signed_msg, &smlen, expected_signed_msg, i + 64, pk);
    if (pass == false) {
      printf("crypto_sign_open returned value failed on input of size %d\n", i);
      break;
    }
    a = memcmp(hacl_signed_msg, plaintext, i * sizeof(uint8_t));
    if (a != 0){
      pass = false;
      printf("crypto_sign_open failed on input of size %d\n", i);
      break;
    }
  }
  if (!pass) return pass;
  tweet_crypto_sign(expected_signed_msg, &smlen, plaintext, HACL_UNIT_TESTS_SIZE, sk);
  crypto_sign(hacl_signed_msg, &smlen, plaintext, HACL_UNIT_TESTS_SIZE, sk);
  a = memcmp(hacl_signed_msg, expected_signed_msg, (HACL_UNIT_TESTS_SIZE+64) * sizeof (uint8_t));
  if (a != 0){
    pass = false;
    printf("crypto_sign failed on input of size %d\n.", HACL_UNIT_TESTS_SIZE);
  }
  pass = crypto_sign_open(hacl_signed_msg, &smlen, expected_signed_msg, HACL_UNIT_TESTS_SIZE + 64, pk);
  if (pass == false) {
    printf("crypto_sign_open returned value failed on input of size %d\n", HACL_UNIT_TESTS_SIZE);
  }
  a = memcmp(hacl_signed_msg, plaintext, HACL_UNIT_TESTS_SIZE * sizeof(uint8_t));
  if (a != 0){
    pass = false;
    printf("crypto_sign_open failed on input of size %d\n", HACL_UNIT_TESTS_SIZE);
  }

  free(plaintext);
  free(hacl_signed_msg);
  free(expected_signed_msg);

  return pass;
}

#define crypto_secretbox_ZEROBYTES 32
#define crypto_secretbox_BOXZEROBYTES 16

bool unit_test_crypto_secretbox(){
  // Global length
  uint64_t len = HACL_UNIT_TESTS_SIZE * sizeof(uint8_t);
  // Scratch buffers
  uint8_t hacl_cipher[HACL_UNIT_TESTS_SIZE + 32], expected_cipher[HACL_UNIT_TESTS_SIZE + 32];
  // Shared key
  uint8_t key[32];
  // Random plaintext
  uint8_t *plaintext = malloc((HACL_UNIT_TESTS_SIZE + crypto_secretbox_ZEROBYTES) * sizeof (uint8_t));
  READ_RANDOM_BYTES(len, plaintext + crypto_secretbox_ZEROBYTES);
  for (int i = 0; i < crypto_secretbox_ZEROBYTES; i++) plaintext[i] = 0;
  // Random plaintext
  uint8_t nonce[24];
  READ_RANDOM_BYTES(24, nonce);
  // Test 1
  int a;
  bool pass = true;
  for (int i = 0; i < 256; i++){
    tweet_crypto_secretbox(expected_cipher, plaintext, crypto_secretbox_ZEROBYTES + i, nonce, key);
    crypto_secretbox(hacl_cipher, plaintext, crypto_secretbox_ZEROBYTES + i, nonce, key);
    a = memcmp(hacl_cipher, expected_cipher, (crypto_secretbox_ZEROBYTES + i) * sizeof (uint8_t));
    if (a != 0){
      pass = false;
      break;
    }
    /* a = crypto_secretbox_open_detached(hacl_cipher/\* +32 *\/, expected_cipher/\* +32 *\/, expected_cipher + 16, i, nonce, key); */
    a = crypto_secretbox_open(hacl_cipher, expected_cipher, crypto_secretbox_ZEROBYTES + i, nonce, key);
    if (a != 0) {
      pass = false;
      printf("SECRETBOX OPEN ******* failed to verify on input of size %d\n", i);
      break;
    }
    a = memcmp(hacl_cipher, plaintext, (crypto_secretbox_ZEROBYTES + i) * sizeof (uint8_t));
    if (a != 0) {
      pass = false;
      printf("SECRETBOX OPEN failed on input of size %d\n", i);
      break;
    }
  }
  if (!pass) return pass;

  // Test 2
  tweet_crypto_secretbox(expected_cipher, plaintext, crypto_secretbox_ZEROBYTES + HACL_UNIT_TESTS_SIZE, nonce, key);
  crypto_secretbox(hacl_cipher, plaintext, crypto_secretbox_ZEROBYTES + HACL_UNIT_TESTS_SIZE, nonce, key);
  a = memcmp(hacl_cipher, expected_cipher, (crypto_secretbox_ZEROBYTES + HACL_UNIT_TESTS_SIZE) * sizeof (uint8_t));
  if (a != 0){
    pass = false;
    printf("SECRETBOX failed on input of size %d\n.", HACL_UNIT_TESTS_SIZE);
  }
  a = crypto_secretbox_open(hacl_cipher, expected_cipher, HACL_UNIT_TESTS_SIZE + crypto_secretbox_ZEROBYTES, nonce, key);
  if (a != 0) {
    pass = false;
    printf("SECRETBOX OPEN failed to verify on input of size %d\n", HACL_UNIT_TESTS_SIZE);
  }
  a = memcmp(hacl_cipher, plaintext, (crypto_secretbox_ZEROBYTES + HACL_UNIT_TESTS_SIZE) * sizeof (uint8_t));
  if (a != 0) {
    pass = false;
    printf("SECRETBOX OPEN failed on input of size %d\n", HACL_UNIT_TESTS_SIZE);
  }

  free(plaintext);

  return pass;
}

bool unit_test_crypto_stream(){
  // Global length
  uint64_t len = HACL_UNIT_TESTS_SIZE * sizeof(uint8_t);
  // Scratch buffers
  uint8_t hacl_cipher[HACL_UNIT_TESTS_SIZE], expected_cipher[HACL_UNIT_TESTS_SIZE];
  // Shared key
  uint8_t key[32], nonce[24];
  // Random plaintext
  uint8_t *plaintext = malloc(HACL_UNIT_TESTS_SIZE * sizeof (uint8_t));
  READ_RANDOM_BYTES(len, plaintext);
  // Test 1
  int a;
  bool pass = true;
  for (int i = 0; i < 1024; i++){
    tweet_crypto_stream(expected_cipher, i, nonce, key);
    crypto_stream(hacl_cipher, i, nonce, key);
    a = memcmp(hacl_cipher, expected_cipher, i * sizeof(uint8_t));
    if (a != 0){
      pass = false;
      printf("SECRETBOX failed on input of size %d\n.", i);
      break;
    }
  }
  if (!pass) return pass;
  // Test 2
  tweet_crypto_stream_xor(expected_cipher, plaintext, HACL_UNIT_TESTS_SIZE, nonce, key);
  crypto_stream_xor(hacl_cipher, plaintext, HACL_UNIT_TESTS_SIZE, nonce, key);
  a = memcmp(hacl_cipher, expected_cipher, HACL_UNIT_TESTS_SIZE * sizeof(uint8_t));
  if (a != 0){
    pass = false;
    printf("SECRETBOX failed on input of size %d\n.", HACL_UNIT_TESTS_SIZE);
  }

  free(plaintext);

  return pass;
}

int main(){
  bool res;
  res = unit_test_onetimeauth();
  if (res == true) {
    printf("Unit tests for crypto_onetimeauth (Poly1305) succeeded\n");
  } else {
    printf("Unit tests for crypto_onetimeauth (Poly1305) *** FAILED ***\n");
  }
  res = res && unit_test_crypto_stream();
  if (res == true) {
    printf("Unit tests for crypto_stream (Salsa20) succeeded\n");
  } else {
    printf("Unit tests for crypto_stream (Salsa20) *** FAILED ***\n");
  }
  res = res && unit_test_crypto_secretbox();
  if (res == true) {
    printf("Unit tests for crypto_secretbox (Salsa20/Poly1305) succeeded\n");
  } else {
    printf("Unit tests for crypto_secretbox (Salsa20/Poly1305) *** FAILED ***\n");
  } 
  res = res && unit_test_chacha20();
  if (res == true) {
    printf("Unit tests for IETF Chacha20 succeeded\n");
  } else {
    printf("Unit tests for IETF Chacha20 *** FAILED ***\n");
  }
  res = res && unit_test_aead();
  if (res == true) {
    printf("Unit tests for IETF AEAD (Chacha20/Poly1305) succeeded\n");
  } else {
    printf("Unit tests for IETF AEAD (Chacha20/Poly1305) *** FAILED ***\n");
  } 
  res = res && unit_test_crypto_keypair();
  if (res == true) {
    printf("Unit tests for crypto_keypair (Curve25519) succeeded\n");
  } else {
    printf("Unit tests for crypto_keypair (Curve25519) *** FAILED ***\n");
  }
  res = res && unit_test_scalarmult();
  if (res == true) {
    printf("Unit tests for crypto_scalarmult (Curve25519) succeeded\n");
  } else {
    printf("Unit tests for crypto_scalarmult (Curve25519) *** FAILED ***\n");
  }
  res = res && unit_test_crypto_box();
  if (res == true) {
    printf("Unit tests for crypto_box (Curve25519/Salsa20/Poly1305) succeeded\n");
  } else {
    printf("Unit tests for crypto_box (Curve25519/Salsa20/Poly1305) *** FAILED ***\n");
  }
  res = res && unit_test_crypto_sign();
  if (res == true) {
    printf("Unit tests for crypto_sign (Ed25519) succeeded\n");
  } else {
    printf("Unit tests for crypto_sign (Ed25519) *** FAILED ***\n");
  }

  return res == true ? 0 : 255;
}
