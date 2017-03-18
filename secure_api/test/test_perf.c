#include "testlib.h"
#include <time.h>
#include "testutils.h"
#include "Crypto_AEAD.h"
#include <openssl/evp.h>
#include "stdio.h"
#include "unistd.h"
#include "fcntl.h"

#define PLAINLEN (16*1024)
#define AADLEN (12)
#define NONCELEN 24
#define KEYLEN 32
#define IVLEN 12

uint8_t nonce[NONCELEN] = {
  0x00, 0x01, 0x02, 0x03,
  0x04, 0x05, 0x06, 0x07,
  0x08, 0x09, 0x10, 0x11,
  0x12, 0x13, 0x14, 0x15,
  0x16, 0x17, 0x18, 0x19,
  0x20, 0x21, 0x22, 0x23,
};

uint8_t key[KEYLEN] = {
  0x85, 0xd6, 0xbe, 0x78,
  0x57, 0x55, 0x6d, 0x33,
  0x7f, 0x44, 0x52, 0xfe,
  0x42, 0xd5, 0x06, 0xa8,
  0x01, 0x03, 0x80, 0x8a,
  0xfb, 0x0d, 0xb2, 0xfd,
  0x4a, 0xbf, 0xf6, 0xaf,
  0x41, 0x49, 0xf5, 0x1b
};

uint8_t sk[KEYLEN] = {
  0x85, 0xd6, 0xbe, 0x78,
  0x57, 0x55, 0x6d, 0x33,
  0x7f, 0x44, 0x52, 0xfe,
  0x42, 0xd5, 0x06, 0xa8,
  0x01, 0x03, 0x80, 0x8a,
  0xfb, 0x0d, 0xb2, 0xfd,
  0x4a, 0xbf, 0xf6, 0xaf,
  0x41, 0x49, 0xf5, 0x1c
};

uint8_t aad[AADLEN] = {
  0x50, 0x51, 0x52, 0x53,
  0xc0, 0xc1, 0xc2, 0xc3,
  0xc4, 0xc5, 0xc6, 0xc7
};

uint8_t ivBuffer[IVLEN] = {
  0x07, 0x00, 0x00, 0x00,
  0x40, 0x41, 0x42, 0x43,
  0x44, 0x45, 0x46, 0x47
};

#define ROUNDS 1000
#define AES_ROUNDS 100

#define AES_128_GCM 0
#define AES_256_GCM 1
#define CHACHA_POLY 2

void print_results(char *txt, double t1, unsigned long long d1, int rounds, int plainlen){
  printf("Testing: %s\n", txt);
  printf("Cycles for %d times 2^20 bytes: %llu (%.2fcycles/byte)\n", rounds, d1, (double)d1/plainlen/rounds);
  printf("User time for %d times 2^20 bytes: %2f (%2fus/byte)\n", rounds, t1/CLOCKS_PER_SEC, (double)t1*1000000/CLOCKS_PER_SEC/plainlen/rounds);
}

int openssl_aead_encrypt(unsigned char *plaintext, int plaintext_len, unsigned char *aad,
                         int aad_len, unsigned char *key, unsigned char *iv,
                         unsigned char *ciphertext, unsigned char *tag, int cipher){
  EVP_CIPHER_CTX *ctx;
  int len;
  int ciphertext_len;
  /* Create and initialise the context */
  if(!(ctx = EVP_CIPHER_CTX_new())) return EXIT_FAILURE;
  /* Initialise the encryption operation. */
  if (cipher == AES_256_GCM) {
    if(1 != EVP_EncryptInit_ex(ctx, EVP_aes_256_gcm(), NULL, NULL, NULL))
      return EXIT_FAILURE;
  } else 
  if (cipher == AES_128_GCM) {
    if(1 != EVP_EncryptInit_ex(ctx, EVP_aes_128_gcm(), NULL, NULL, NULL))
      return EXIT_FAILURE;
  } else {
    if(1 != EVP_EncryptInit_ex(ctx, EVP_chacha20_poly1305(), NULL, NULL, NULL))
      return EXIT_FAILURE;
  }

  clock_t c1, c2;
  double t1, t2;
  unsigned long long a,b,d1,d2;
  c1 = clock();
  a = TestLib_cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++){
    /* Set IV length if default 12 bytes (96 bits) is not appropriate */
    if(1 != EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_IVLEN, 16, NULL))
      return EXIT_FAILURE;
    /* Initialise key and IV */
    if(1 != EVP_EncryptInit_ex(ctx, NULL, NULL, key, iv)) return EXIT_FAILURE;
    /* Provide any AAD data. This can be called zero or more times as
     * required
     */
    if(1 != EVP_EncryptUpdate(ctx, NULL, &len, aad, aad_len))
      return EXIT_FAILURE;
    /* Provide the message to be encrypted, and obtain the encrypted output.
     * EVP_EncryptUpdate can be called multiple times if necessary
     */
    if(1 != EVP_EncryptUpdate(ctx, ciphertext, &len, plaintext, plaintext_len))
      return EXIT_FAILURE;
    ciphertext_len = len;
    /* Finalise the encryption. Normally ciphertext bytes may be written at
     * this stage, but this does not occur in GCM mode
     */
    if(1 != EVP_EncryptFinal_ex(ctx, ciphertext + len, &len)) return EXIT_FAILURE;
    ciphertext_len += len;
    /* Get the tag */
    if(1 != EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_GET_TAG, 16, tag))
      return EXIT_FAILURE;
  }
  b = TestLib_cpucycles_end();
  c2 = clock();
  d1 = (double) b - a;
  t1 = (double)c2 - c1;
  print_results(cipher == AES_128_GCM ? "openssl-aes-128-gcm" : (cipher == AES_256_GCM? "openssl-aes-256-gcm" : "openssl-chacha20-poly1305"), t1, d1, ROUNDS, PLAINLEN);
  EVP_CIPHER_CTX_free(ctx);
  return ciphertext_len;
}


void test_kremlin_aead(uint8_t* plain, uint8_t* cipher, int alg){
  clock_t c1, c2;
  double t1, t2;

  FStar_UInt128_t iv = Crypto_Symmetric_Bytes_load_uint128((uint32_t )12, ivBuffer);

  unsigned long long a,b,d1,d2;

  Crypto_Indexing_aeadAlg i = alg == AES_256_GCM ? Crypto_Indexing_testId(Crypto_Indexing_aeadAlg_AES_256_GCM) : (alg == AES_128_GCM ? Crypto_Indexing_testId(Crypto_Indexing_aeadAlg_AES_128_GCM) : Crypto_Indexing_testId(Crypto_Indexing_aeadAlg_CHACHA20_POLY1305));
  Crypto_AEAD_Invariant_aead_state_______ st0 = Crypto_AEAD_coerce(i, FStar_HyperHeap_root, key);

  c1 = clock();
  a = TestLib_cpucycles_begin();
  int rounds = alg == CHACHA_POLY? ROUNDS : AES_ROUNDS;
  for (int j = 0; j < rounds; j++) {
    Crypto_AEAD_Encrypt_encrypt(i, st0, iv, AADLEN, aad, PLAINLEN, plain, cipher);
    plain[0] = cipher[0];
  }
  b = TestLib_cpucycles_end();
  c2 = clock();
  d1 = (double)b - a;
  t1 = (double)c2 - c1;
  print_results(alg == AES_256_GCM ? "Kremlin-C-aes256-gcm" : (alg == AES_128_GCM? "Kremlin-C-aes128-gcm" : "Kremlin-C-chacha20-poly1305"), t1, d1, rounds, PLAINLEN);
  uint64_t res;
  for (int i = 0; i < PLAINLEN; i++) 
    res += (uint64_t) cipher[i];
  printf("Composite result (ignore): %llx\n", res);
}

void test_crypto_aead(){
  uint8_t plain[PLAINLEN];
  uint8_t cipher[PLAINLEN+16];
  uint8_t mac[16];
  int fd = open("/dev/urandom", O_RDONLY);
  uint64_t res = read(fd, plain, PLAINLEN);

  test_kremlin_aead(plain, cipher, AES_128_GCM);
  openssl_aead_encrypt(plain, PLAINLEN, aad, AADLEN, key, ivBuffer, cipher, mac, AES_128_GCM);
  test_kremlin_aead(plain, cipher, AES_256_GCM);
  openssl_aead_encrypt(plain, PLAINLEN, aad, AADLEN, key, ivBuffer, cipher, mac, AES_256_GCM);
  test_kremlin_aead(plain, cipher, CHACHA_POLY);
  openssl_aead_encrypt(plain, PLAINLEN, aad, AADLEN, key, ivBuffer, cipher, mac, CHACHA_POLY);
}


int main(){
  test_crypto_aead();
  return EXIT_SUCCESS;
}
