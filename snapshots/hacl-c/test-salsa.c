#include "kremlib.h"
#include "testlib.h"
#include "Salsa20.h"
#include "sodium.h"

void print_results(char *txt, double t1, unsigned long long d1, int rounds, int plainlen){
  printf("Testing: %s\n", txt);
  printf("Cycles for %d times 2^20 bytes: %llu (%.2fcycles/byte)\n", rounds, d1, (double)d1/plainlen/rounds);
  printf("User time for %d times 2^20 bytes: %f (%fus/byte)\n", rounds, t1/CLOCKS_PER_SEC, (double)t1*1000000/CLOCKS_PER_SEC/plainlen/rounds);
}

#define PLAINLEN (1024*1024)
#define ROUNDS 1000
#define MACSIZE 32

__attribute__ ((aligned (16)))  uint8_t
  expected1[64] =
    {
      (uint8_t )0xE3,
      (uint8_t )0xBE,
      (uint8_t )0x8F,
      (uint8_t )0xDD,
      (uint8_t )0x8B,
      (uint8_t )0xEC,
      (uint8_t )0xA2,
      (uint8_t )0xE3,
      (uint8_t )0xEA,
      (uint8_t )0x8E,
      (uint8_t )0xF9,
      (uint8_t )0x47,
      (uint8_t )0x5B,
      (uint8_t )0x29,
      (uint8_t )0xA6,
      (uint8_t )0xE7,
      (uint8_t )0x00,
      (uint8_t )0x39,
      (uint8_t )0x51,
      (uint8_t )0xE1,
      (uint8_t )0x09,
      (uint8_t )0x7A,
      (uint8_t )0x5C,
      (uint8_t )0x38,
      (uint8_t )0xD2,
      (uint8_t )0x3B,
      (uint8_t )0x7A,
      (uint8_t )0x5F,
      (uint8_t )0xAD,
      (uint8_t )0x9F,
      (uint8_t )0x68,
      (uint8_t )0x44,
      (uint8_t )0xB2,
      (uint8_t )0x2C,
      (uint8_t )0x97,
      (uint8_t )0x55,
      (uint8_t )0x9E,
      (uint8_t )0x27,
      (uint8_t )0x23,
      (uint8_t )0xC7,
      (uint8_t )0xCB,
      (uint8_t )0xBD,
      (uint8_t )0x3F,
      (uint8_t )0xE4,
      (uint8_t )0xFC,
      (uint8_t )0x8D,
      (uint8_t )0x9A,
      (uint8_t )0x07,
      (uint8_t )0x44,
      (uint8_t )0x65,
      (uint8_t )0x2A,
      (uint8_t )0x83,
      (uint8_t )0xE7,
      (uint8_t )0x2A,
      (uint8_t )0x9C,
      (uint8_t )0x46,
      (uint8_t )0x18,
      (uint8_t )0x76,
      (uint8_t )0xAF,
      (uint8_t )0x4D,
      (uint8_t )0x7E,
      (uint8_t )0xF1,
      (uint8_t )0xA1,
      (uint8_t )0x17
    };
__attribute__ ((aligned (16)))  uint8_t
  expected2[64] =
    {
      (uint8_t )0x57,
      (uint8_t )0xBE,
      (uint8_t )0x81,
      (uint8_t )0xF4,
      (uint8_t )0x7B,
      (uint8_t )0x17,
      (uint8_t )0xD9,
      (uint8_t )0xAE,
      (uint8_t )0x7C,
      (uint8_t )0x4F,
      (uint8_t )0xF1,
      (uint8_t )0x54,
      (uint8_t )0x29,
      (uint8_t )0xA7,
      (uint8_t )0x3E,
      (uint8_t )0x10,
      (uint8_t )0xAC,
      (uint8_t )0xF2,
      (uint8_t )0x50,
      (uint8_t )0xED,
      (uint8_t )0x3A,
      (uint8_t )0x90,
      (uint8_t )0xA9,
      (uint8_t )0x3C,
      (uint8_t )0x71,
      (uint8_t )0x13,
      (uint8_t )0x08,
      (uint8_t )0xA7,
      (uint8_t )0x4C,
      (uint8_t )0x62,
      (uint8_t )0x16,
      (uint8_t )0xA9,
      (uint8_t )0xED,
      (uint8_t )0x84,
      (uint8_t )0xCD,
      (uint8_t )0x12,
      (uint8_t )0x6D,
      (uint8_t )0xA7,
      (uint8_t )0xF2,
      (uint8_t )0x8E,
      (uint8_t )0x8A,
      (uint8_t )0xBF,
      (uint8_t )0x8B,
      (uint8_t )0xB6,
      (uint8_t )0x35,
      (uint8_t )0x17,
      (uint8_t )0xE1,
      (uint8_t )0xCA,
      (uint8_t )0x98,
      (uint8_t )0xE7,
      (uint8_t )0x12,
      (uint8_t )0xF4,
      (uint8_t )0xFB,
      (uint8_t )0x2E,
      (uint8_t )0x1A,
      (uint8_t )0x6A,
      (uint8_t )0xED,
      (uint8_t )0x9F,
      (uint8_t )0xDC,
      (uint8_t )0x73,
      (uint8_t )0x29,
      (uint8_t )0x1F,
      (uint8_t )0xAA,
      (uint8_t )0x17
    };
__attribute__ ((aligned (16)))  uint8_t
  expected3[64] =
    {
      (uint8_t )0x95,
      (uint8_t )0x82,
      (uint8_t )0x11,
      (uint8_t )0xC4,
      (uint8_t )0xBA,
      (uint8_t )0x2E,
      (uint8_t )0xBD,
      (uint8_t )0x58,
      (uint8_t )0x38,
      (uint8_t )0xC6,
      (uint8_t )0x35,
      (uint8_t )0xED,
      (uint8_t )0xB8,
      (uint8_t )0x1F,
      (uint8_t )0x51,
      (uint8_t )0x3A,
      (uint8_t )0x91,
      (uint8_t )0xA2,
      (uint8_t )0x94,
      (uint8_t )0xE1,
      (uint8_t )0x94,
      (uint8_t )0xF1,
      (uint8_t )0xC0,
      (uint8_t )0x39,
      (uint8_t )0xAE,
      (uint8_t )0xEC,
      (uint8_t )0x65,
      (uint8_t )0x7D,
      (uint8_t )0xCE,
      (uint8_t )0x40,
      (uint8_t )0xAA,
      (uint8_t )0x7E,
      (uint8_t )0x7C,
      (uint8_t )0x0A,
      (uint8_t )0xF5,
      (uint8_t )0x7C,
      (uint8_t )0xAC,
      (uint8_t )0xEF,
      (uint8_t )0xA4,
      (uint8_t )0x0C,
      (uint8_t )0x9F,
      (uint8_t )0x14,
      (uint8_t )0xB7,
      (uint8_t )0x1A,
      (uint8_t )0x4B,
      (uint8_t )0x34,
      (uint8_t )0x56,
      (uint8_t )0xA6,
      (uint8_t )0x3E,
      (uint8_t )0x16,
      (uint8_t )0x2E,
      (uint8_t )0xC7,
      (uint8_t )0xD8,
      (uint8_t )0xD1,
      (uint8_t )0x0B,
      (uint8_t )0x8F,
      (uint8_t )0xFB,
      (uint8_t )0x18,
      (uint8_t )0x10,
      (uint8_t )0xD7,
      (uint8_t )0x10,
      (uint8_t )0x01,
      (uint8_t )0xB6,
      (uint8_t )0x18
    };
__attribute__ ((aligned (16)))  uint8_t
  expected4[64] =
    {
      (uint8_t )0x69,
      (uint8_t )0x6A,
      (uint8_t )0xFC,
      (uint8_t )0xFD,
      (uint8_t )0x0C,
      (uint8_t )0xDD,
      (uint8_t )0xCC,
      (uint8_t )0x83,
      (uint8_t )0xC7,
      (uint8_t )0xE7,
      (uint8_t )0x7F,
      (uint8_t )0x11,
      (uint8_t )0xA6,
      (uint8_t )0x49,
      (uint8_t )0xD7,
      (uint8_t )0x9A,
      (uint8_t )0xCD,
      (uint8_t )0xC3,
      (uint8_t )0x35,
      (uint8_t )0x4E,
      (uint8_t )0x96,
      (uint8_t )0x35,
      (uint8_t )0xFF,
      (uint8_t )0x13,
      (uint8_t )0x7E,
      (uint8_t )0x92,
      (uint8_t )0x99,
      (uint8_t )0x33,
      (uint8_t )0xA0,
      (uint8_t )0xBD,
      (uint8_t )0x6F,
      (uint8_t )0x53,
      (uint8_t )0x77,
      (uint8_t )0xEF,
      (uint8_t )0xA1,
      (uint8_t )0x05,
      (uint8_t )0xA3,
      (uint8_t )0xA4,
      (uint8_t )0x26,
      (uint8_t )0x6B,
      (uint8_t )0x7C,
      (uint8_t )0x0D,
      (uint8_t )0x08,
      (uint8_t )0x9D,
      (uint8_t )0x08,
      (uint8_t )0xF1,
      (uint8_t )0xE8,
      (uint8_t )0x55,
      (uint8_t )0xCC,
      (uint8_t )0x32,
      (uint8_t )0xB1,
      (uint8_t )0x5B,
      (uint8_t )0x93,
      (uint8_t )0x78,
      (uint8_t )0x4A,
      (uint8_t )0x36,
      (uint8_t )0xE5,
      (uint8_t )0x6A,
      (uint8_t )0x76,
      (uint8_t )0xCC,
      (uint8_t )0x64,
      (uint8_t )0xBC,
      (uint8_t )0x84,
      (uint8_t )0x77
    };



int32_t test_salsa()
{
  uint32_t len = (uint32_t )512;
  uint32_t keysize = (uint32_t )32;
  uint32_t noncesize = (uint32_t )8;
  __attribute__ ((aligned (16)))uint8_t ciphertext[len];
  memset(ciphertext, 0, len * sizeof ciphertext[0]);
  __attribute__ ((aligned (16)))uint8_t plaintext[len];
  memset(plaintext, 0, len * sizeof plaintext[0]);
  __attribute__ ((aligned (16)))uint8_t key[keysize];
  memset(key, 0, keysize * sizeof key[0]);
  key[(uint32_t )0] = (uint8_t )0x80;
  __attribute__ ((aligned (16)))uint8_t nonce[noncesize];
  memset(nonce, 0, noncesize * sizeof nonce[0]);


  Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor(ciphertext,
    plaintext,
    (uint64_t )512,
    nonce,
    key);
  TestLib_compare_and_print("HACL Salsa20", expected1, ciphertext + (uint32_t )0, (uint32_t )64);
  TestLib_compare_and_print("HACL Salsa20", expected2, ciphertext + (uint32_t )192, (uint32_t )64);
  TestLib_compare_and_print("HACL Salsa20", expected3, ciphertext + (uint32_t )256, (uint32_t )64);
  TestLib_compare_and_print("HACL Salsa20", expected4, ciphertext + (uint32_t )448, (uint32_t )64);

  crypto_stream_salsa20_xor(ciphertext,plaintext, 512, nonce, key);
  TestLib_compare_and_print("Sodium Salsa20", expected1, ciphertext + (uint32_t )0, (uint32_t )64);
  TestLib_compare_and_print("Sodium Salsa20", expected2, ciphertext + (uint32_t )192, (uint32_t )64);
  TestLib_compare_and_print("Sodium Salsa20", expected3, ciphertext + (uint32_t )256, (uint32_t )64);
  TestLib_compare_and_print("Sodium Salsa20", expected4, ciphertext + (uint32_t )448, (uint32_t )64);


  return exit_success;
}

int32_t perf_salsa() {
  uint32_t len = PLAINLEN * sizeof(char);
  __attribute__ ((aligned (16)))uint8_t plain[len];
  __attribute__ ((aligned (16)))uint8_t cipher[len];
  int fd = open("/dev/urandom", O_RDONLY);
  uint64_t res = read(fd, plain, len);
  if (res != len) {
    printf("Error on reading, got %llu bytes\n", res);
    return 1;
  }

  uint32_t keysize = (uint32_t )32;
  uint32_t noncesize = (uint32_t )8;
  __attribute__ ((aligned (16)))uint8_t key[keysize];
  memset(key, 0, keysize * sizeof key[0]);
  key[(uint32_t )0] = (uint8_t )0x80;
  __attribute__ ((aligned (16)))uint8_t nonce[noncesize];
  memset(nonce, 0, noncesize * sizeof nonce[0]);

  cycles a,b;
  clock_t t1,t2;
  t1 = clock();

  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor(plain, plain, len, nonce, key);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  print_results("HACL Salsa20 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < PLAINLEN; i++) 
    res += (uint64_t) plain[i];
  printf("Composite result (ignore): %llx\n", res);

  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    crypto_stream_salsa20_xor(plain,plain, len, nonce, key);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  print_results("Sodium Salsa20 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < PLAINLEN; i++) 
    res += (uint64_t) plain[i];
  printf("Composite result (ignore): %llx\n", res);
  
  return exit_success;
}

int32_t main()
{
  int32_t res = exit_success;
  //  res = test_salsa();
  if (res == exit_success) {
    res = perf_salsa();
  }
  return res;
}
  
