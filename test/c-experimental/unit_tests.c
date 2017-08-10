#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#include "haclnacl.h"
#include "tweetnacl.h"

#define SIZE (/* 1024 */ 1 * 1024)
#define POLY_MACSIZE 16
#define POLY_BLOCKSIZE 16
#define POLY_KEYSIZE 32
#define CHACHA_BLOCKSIZE 64
#define CHACHA_KEYSIZE 32
#define SALSA_BLOCK_SIZE 64

bool unit_test_onetimeauth(){
  // Global length
  uint64_t len = SIZE * sizeof(uint8_t);
  // Scratch buffers
  uint8_t hacl_mac[POLY_MACSIZE], expected_mac[POLY_MACSIZE], key[POLY_KEYSIZE];
  uint8_t *plaintext = malloc(SIZE * sizeof (uint8_t));
  // Initializing random plaintext
  int fd = open("/dev/urandom", O_RDONLY);
  uint64_t res = read(fd, plaintext, len);
  if (res != len) {
    printf("Error on reading, got %" PRIu64 " bytes\n", res);
    return 1;
  }
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
      printf("POLY1305 failed on input of size %d\n.", i);
      break;
    }
    // Testing crypto_onetimeauth verify on different length
    a = crypto_onetimeauth_verify(hacl_mac, plaintext, i, key);
    if (a != 0){
      pass = false;
      printf("POLY1305 verify failed on input of size %d\n.", i);
      break;
    }
    hacl_mac[i%16] = ~(hacl_mac[i%16]);
    // Testing crypto_onetimeauth proper failure on different length
    a = crypto_onetimeauth_verify(hacl_mac, plaintext, i, key);
    if (a == 0){
      pass = false;
      printf("POLY1305 verify fail failed on input of size %d\n.", i);
      break;
    }
  }
  tweet_crypto_onetimeauth(expected_mac, plaintext, SIZE, key);
  crypto_onetimeauth(hacl_mac, plaintext, SIZE, key);
  a = memcmp(hacl_mac, expected_mac, 16 * sizeof (uint8_t));
  if (a != 0){
    pass = false;
    printf("POLY1305 failed on input of size %d\n.", SIZE);
  }

  close(fd);
  free(plaintext);

  return pass;
}

#define crypto_box_ZEROBYTES 32
#define crypto_box_BOXZEROBYTES 16

bool unit_test_crypto_box(){
  // Global length
  uint64_t len = SIZE * sizeof(uint8_t);
  // Scratch buffers
  uint8_t hacl_cipher[SIZE + 32], expected_cipher[SIZE + 32];
  // Generation of the public/secret key couple
  uint8_t sk1[32], pk1[32];
  uint8_t sk2[32], pk2[32];
  tweet_crypto_box_keypair(pk1, sk1);
  tweet_crypto_box_keypair(pk2, sk2);
  // Random plaintext
  uint8_t *plaintext = malloc((SIZE + crypto_box_ZEROBYTES) * sizeof (uint8_t));
  int fd = open("/dev/urandom", O_RDONLY);
  uint64_t res = read(fd, plaintext + crypto_box_ZEROBYTES, len);
  if (res != len) {
    printf("Error on reading, got %" PRIu64 " bytes\n", res);
    return false;
  }
  for (int i = 0; i < crypto_box_ZEROBYTES; i++) plaintext[i] = 0;
  // Random plaintext
  uint8_t nonce[24];
  res = read(fd, nonce, 24);
  if (res != 24) {
    printf("Error on reading nonce, got %" PRIu64 " bytes\n", res);
    return false;
  }
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
  tweet_crypto_box(expected_cipher, plaintext, crypto_box_ZEROBYTES + SIZE, nonce, pk1, sk2);
  crypto_box(hacl_cipher, plaintext, crypto_box_ZEROBYTES + SIZE, nonce, pk1, sk2);
  a = memcmp(hacl_cipher, expected_cipher, (crypto_box_ZEROBYTES + SIZE) * sizeof (uint8_t));
  if (a != 0){
    pass = false;
    printf("BOX failed on input of size %d\n.", SIZE);
  }
  a = crypto_box_open(hacl_cipher, expected_cipher, SIZE + crypto_box_ZEROBYTES, nonce, pk2, sk1);
  if (a != 0) {
    pass = false;
    printf("BOX OPEN failed to verify on input of size %d\n", SIZE);
  }
  a = memcmp(hacl_cipher, plaintext, (crypto_box_ZEROBYTES + SIZE) * sizeof (uint8_t));
  if (a != 0) {
    pass = false;
    printf("BOX OPEN failed on input of size %d\n", SIZE);
  }

  close(fd);
  free(plaintext);

  return pass;
}

#define NUM_SCALARMULT 1000

bool unit_test_scalarmult(){
  // Random key values
  uint8_t *random_bytes = malloc(32 * NUM_SCALARMULT * sizeof(uint8_t));
  int fd = open("/dev/urandom", O_RDONLY);
  uint64_t res = read(fd, random_bytes, 32 * NUM_SCALARMULT);
  if (res != 32 * NUM_SCALARMULT) {
    printf("Error on reading, got %" PRIu64 " bytes\n", res);
    return false;
  }
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

  close(fd);
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
  uint64_t len = SIZE * sizeof(uint8_t);
  uint8_t *plaintext = malloc(SIZE * sizeof (uint8_t));
  uint8_t *expected_signed_msg = malloc((SIZE+64) * sizeof (uint8_t));
  uint8_t *hacl_signed_msg = malloc((SIZE+64) * sizeof (uint8_t));
  uint8_t sk[64], pk[32];
  crypto_sign_keypair(pk, sk);
  int fd = open("/dev/urandom", O_RDONLY);
  uint64_t res = read(fd, plaintext, len);
  if (res != len) {
    printf("Error on reading, got %" PRIu64 " bytes\n", res);
    return false;
  }
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
  tweet_crypto_sign(expected_signed_msg, &smlen, plaintext, SIZE, sk);
  crypto_sign(hacl_signed_msg, &smlen, plaintext, SIZE, sk);
  a = memcmp(hacl_signed_msg, expected_signed_msg, (SIZE+64) * sizeof (uint8_t));
  if (a != 0){
    pass = false;
    printf("crypto_sign failed on input of size %d\n.", SIZE);
  }
  pass = crypto_sign_open(hacl_signed_msg, &smlen, expected_signed_msg, SIZE + 64, pk);
  if (pass == false) {
    printf("crypto_sign_open returned value failed on input of size %d\n", SIZE);
  }
  a = memcmp(hacl_signed_msg, plaintext, SIZE * sizeof(uint8_t));
  if (a != 0){
    pass = false;
    printf("crypto_sign_open failed on input of size %d\n", SIZE);
  }

  close(fd);
  free(plaintext);
  free(hacl_signed_msg);
  free(expected_signed_msg);

  return pass;
}

#define crypto_secretbox_ZEROBYTES 32
#define crypto_secretbox_BOXZEROBYTES 16

bool unit_test_crypto_secretbox(){
  // Global length
  uint64_t len = SIZE * sizeof(uint8_t);
  // Scratch buffers
  uint8_t hacl_cipher[SIZE + 32], expected_cipher[SIZE + 32];
  // Shared key
  uint8_t key[32];
  // Random plaintext
  uint8_t *plaintext = malloc((SIZE + crypto_secretbox_ZEROBYTES) * sizeof (uint8_t));
  int fd = open("/dev/urandom", O_RDONLY);
  uint64_t res = read(fd, plaintext + crypto_secretbox_ZEROBYTES, len);
  if (res != len) {
    printf("Error on reading, got %" PRIu64 " bytes\n", res);
    return false;
  }
  for (int i = 0; i < crypto_secretbox_ZEROBYTES; i++) plaintext[i] = 0;
  // Random plaintext
  uint8_t nonce[24];
  res = read(fd, nonce, 24);
  if (res != 24) {
    printf("Error on reading nonce, got %" PRIu64 " bytes\n", res);
    return false;
  }
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
  tweet_crypto_secretbox(expected_cipher, plaintext, crypto_secretbox_ZEROBYTES + SIZE, nonce, key);
  crypto_secretbox(hacl_cipher, plaintext, crypto_secretbox_ZEROBYTES + SIZE, nonce, key);
  a = memcmp(hacl_cipher, expected_cipher, (crypto_secretbox_ZEROBYTES + SIZE) * sizeof (uint8_t));
  if (a != 0){
    pass = false;
    printf("SECRETBOX failed on input of size %d\n.", SIZE);
  }
  a = crypto_secretbox_open(hacl_cipher, expected_cipher, SIZE + crypto_secretbox_ZEROBYTES, nonce, key);
  if (a != 0) {
    pass = false;
    printf("SECRETBOX OPEN failed to verify on input of size %d\n", SIZE);
  }
  a = memcmp(hacl_cipher, plaintext, (crypto_secretbox_ZEROBYTES + SIZE) * sizeof (uint8_t));
  if (a != 0) {
    pass = false;
    printf("SECRETBOX OPEN failed on input of size %d\n", SIZE);
  }

  close(fd);
  free(plaintext);

  return pass;
}

bool unit_test_crypto_stream(){
  // Global length
  uint64_t len = SIZE * sizeof(uint8_t);
  // Scratch buffers
  uint8_t hacl_cipher[SIZE], expected_cipher[SIZE];
  // Shared key
  uint8_t key[32], nonce[24];
  // Random plaintext
  uint8_t *plaintext = malloc(SIZE * sizeof (uint8_t));
  int fd = open("/dev/urandom", O_RDONLY);
  uint64_t res = read(fd, plaintext, len);
  if (res != len) {
    printf("Error on reading, got %" PRIu64 " bytes\n", res);
    return false;
  }
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
  tweet_crypto_stream_xor(expected_cipher, plaintext, SIZE, nonce, key);
  crypto_stream_xor(hacl_cipher, plaintext, SIZE, nonce, key);
  a = memcmp(hacl_cipher, expected_cipher, SIZE * sizeof(uint8_t));
  if (a != 0){
    pass = false;
    printf("SECRETBOX failed on input of size %d\n.", SIZE);
  }

  close(fd);
  free(plaintext);

  return pass;
}

int main(){
  bool res;
  res = unit_test_onetimeauth();
  if (res == true) {
    printf("Unit tests for crypto_onetimeauth succeeded\n");
  } else {
    printf("Unit tests for POLY1305 *** FAILED ***\n");
  }
  res = res && unit_test_crypto_box();
  if (res == true) {
    printf("Unit tests for crypto_box succeeded\n");
  } else {
    printf("Unit tests for crypto_box *** FAILED ***\n");
  }
  res = res && unit_test_scalarmult();
  if (res == true) {
    printf("Unit tests for crypto_scalarmult succeeded\n");
  } else {
    printf("Unit tests for crypto_scalarmult *** FAILED ***\n");
  }
  res = res && unit_test_crypto_keypair();
  if (res == true) {
    printf("Unit tests for crypto_keypair succeeded\n");
  } else {
    printf("Unit tests for crypto_keypair *** FAILED ***\n");
  }
  res = res && unit_test_crypto_sign();
  if (res == true) {
    printf("Unit tests for crypto_sign succeeded\n");
  } else {
    printf("Unit tests for crypto_sign *** FAILED ***\n");
  }
  res = res && unit_test_crypto_secretbox();
  if (res == true) {
    printf("Unit tests for crypto_secretbox succeeded\n");
  } else {
    printf("Unit tests for crypto_secretbox *** FAILED ***\n");
  }
  res = res && unit_test_crypto_stream();
  if (res == true) {
    printf("Unit tests for crypto_stream succeeded\n");
  } else {
    printf("Unit tests for crypto_stream *** FAILED ***\n");
  }
  return res == true ? 0 : 255;
}
