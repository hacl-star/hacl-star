#include "kremlib.h"
#include "testlib.h"
#include "Chacha20.h"
#include "sodium.h"

void print_results(char *txt, double t1, unsigned long long d1, int rounds, int plainlen){
  printf("Testing: %s\n", txt);
  printf("Cycles for %d times 2^20 bytes: %llu (%.2fcycles/byte)\n", rounds, d1, (double)d1/plainlen/rounds);
  printf("User time for %d times 2^20 bytes: %f (%fus/byte)\n", rounds, t1/CLOCKS_PER_SEC, (double)t1*1000000/CLOCKS_PER_SEC/plainlen/rounds);
}

#define PLAINLEN (1024*1024)
#define ROUNDS 1000
#define MACSIZE 32


uint8_t
plaintext[114] =
    {
      (uint8_t )0x4c,
      (uint8_t )0x61,
      (uint8_t )0x64,
      (uint8_t )0x69,
      (uint8_t )0x65,
      (uint8_t )0x73,
      (uint8_t )0x20,
      (uint8_t )0x61,
      (uint8_t )0x6e,
      (uint8_t )0x64,
      (uint8_t )0x20,
      (uint8_t )0x47,
      (uint8_t )0x65,
      (uint8_t )0x6e,
      (uint8_t )0x74,
      (uint8_t )0x6c,
      (uint8_t )0x65,
      (uint8_t )0x6d,
      (uint8_t )0x65,
      (uint8_t )0x6e,
      (uint8_t )0x20,
      (uint8_t )0x6f,
      (uint8_t )0x66,
      (uint8_t )0x20,
      (uint8_t )0x74,
      (uint8_t )0x68,
      (uint8_t )0x65,
      (uint8_t )0x20,
      (uint8_t )0x63,
      (uint8_t )0x6c,
      (uint8_t )0x61,
      (uint8_t )0x73,
      (uint8_t )0x73,
      (uint8_t )0x20,
      (uint8_t )0x6f,
      (uint8_t )0x66,
      (uint8_t )0x20,
      (uint8_t )0x27,
      (uint8_t )0x39,
      (uint8_t )0x39,
      (uint8_t )0x3a,
      (uint8_t )0x20,
      (uint8_t )0x49,
      (uint8_t )0x66,
      (uint8_t )0x20,
      (uint8_t )0x49,
      (uint8_t )0x20,
      (uint8_t )0x63,
      (uint8_t )0x6f,
      (uint8_t )0x75,
      (uint8_t )0x6c,
      (uint8_t )0x64,
      (uint8_t )0x20,
      (uint8_t )0x6f,
      (uint8_t )0x66,
      (uint8_t )0x66,
      (uint8_t )0x65,
      (uint8_t )0x72,
      (uint8_t )0x20,
      (uint8_t )0x79,
      (uint8_t )0x6f,
      (uint8_t )0x75,
      (uint8_t )0x20,
      (uint8_t )0x6f,
      (uint8_t )0x6e,
      (uint8_t )0x6c,
      (uint8_t )0x79,
      (uint8_t )0x20,
      (uint8_t )0x6f,
      (uint8_t )0x6e,
      (uint8_t )0x65,
      (uint8_t )0x20,
      (uint8_t )0x74,
      (uint8_t )0x69,
      (uint8_t )0x70,
      (uint8_t )0x20,
      (uint8_t )0x66,
      (uint8_t )0x6f,
      (uint8_t )0x72,
      (uint8_t )0x20,
      (uint8_t )0x74,
      (uint8_t )0x68,
      (uint8_t )0x65,
      (uint8_t )0x20,
      (uint8_t )0x66,
      (uint8_t )0x75,
      (uint8_t )0x74,
      (uint8_t )0x75,
      (uint8_t )0x72,
      (uint8_t )0x65,
      (uint8_t )0x2c,
      (uint8_t )0x20,
      (uint8_t )0x73,
      (uint8_t )0x75,
      (uint8_t )0x6e,
      (uint8_t )0x73,
      (uint8_t )0x63,
      (uint8_t )0x72,
      (uint8_t )0x65,
      (uint8_t )0x65,
      (uint8_t )0x6e,
      (uint8_t )0x20,
      (uint8_t )0x77,
      (uint8_t )0x6f,
      (uint8_t )0x75,
      (uint8_t )0x6c,
      (uint8_t )0x64,
      (uint8_t )0x20,
      (uint8_t )0x62,
      (uint8_t )0x65,
      (uint8_t )0x20,
      (uint8_t )0x69,
      (uint8_t )0x74,
      (uint8_t )0x2e
    };
uint8_t
expected[114] =
    {
      (uint8_t )0x6e,
      (uint8_t )0x2e,
      (uint8_t )0x35,
      (uint8_t )0x9a,
      (uint8_t )0x25,
      (uint8_t )0x68,
      (uint8_t )0xf9,
      (uint8_t )0x80,
      (uint8_t )0x41,
      (uint8_t )0xba,
      (uint8_t )0x07,
      (uint8_t )0x28,
      (uint8_t )0xdd,
      (uint8_t )0x0d,
      (uint8_t )0x69,
      (uint8_t )0x81,
      (uint8_t )0xe9,
      (uint8_t )0x7e,
      (uint8_t )0x7a,
      (uint8_t )0xec,
      (uint8_t )0x1d,
      (uint8_t )0x43,
      (uint8_t )0x60,
      (uint8_t )0xc2,
      (uint8_t )0x0a,
      (uint8_t )0x27,
      (uint8_t )0xaf,
      (uint8_t )0xcc,
      (uint8_t )0xfd,
      (uint8_t )0x9f,
      (uint8_t )0xae,
      (uint8_t )0x0b,
      (uint8_t )0xf9,
      (uint8_t )0x1b,
      (uint8_t )0x65,
      (uint8_t )0xc5,
      (uint8_t )0x52,
      (uint8_t )0x47,
      (uint8_t )0x33,
      (uint8_t )0xab,
      (uint8_t )0x8f,
      (uint8_t )0x59,
      (uint8_t )0x3d,
      (uint8_t )0xab,
      (uint8_t )0xcd,
      (uint8_t )0x62,
      (uint8_t )0xb3,
      (uint8_t )0x57,
      (uint8_t )0x16,
      (uint8_t )0x39,
      (uint8_t )0xd6,
      (uint8_t )0x24,
      (uint8_t )0xe6,
      (uint8_t )0x51,
      (uint8_t )0x52,
      (uint8_t )0xab,
      (uint8_t )0x8f,
      (uint8_t )0x53,
      (uint8_t )0x0c,
      (uint8_t )0x35,
      (uint8_t )0x9f,
      (uint8_t )0x08,
      (uint8_t )0x61,
      (uint8_t )0xd8,
      (uint8_t )0x07,
      (uint8_t )0xca,
      (uint8_t )0x0d,
      (uint8_t )0xbf,
      (uint8_t )0x50,
      (uint8_t )0x0d,
      (uint8_t )0x6a,
      (uint8_t )0x61,
      (uint8_t )0x56,
      (uint8_t )0xa3,
      (uint8_t )0x8e,
      (uint8_t )0x08,
      (uint8_t )0x8a,
      (uint8_t )0x22,
      (uint8_t )0xb6,
      (uint8_t )0x5e,
      (uint8_t )0x52,
      (uint8_t )0xbc,
      (uint8_t )0x51,
      (uint8_t )0x4d,
      (uint8_t )0x16,
      (uint8_t )0xcc,
      (uint8_t )0xf8,
      (uint8_t )0x06,
      (uint8_t )0x81,
      (uint8_t )0x8c,
      (uint8_t )0xe9,
      (uint8_t )0x1a,
      (uint8_t )0xb7,
      (uint8_t )0x79,
      (uint8_t )0x37,
      (uint8_t )0x36,
      (uint8_t )0x5a,
      (uint8_t )0xf9,
      (uint8_t )0x0b,
      (uint8_t )0xbf,
      (uint8_t )0x74,
      (uint8_t )0xa3,
      (uint8_t )0x5b,
      (uint8_t )0xe6,
      (uint8_t )0xb4,
      (uint8_t )0x0b,
      (uint8_t )0x8e,
      (uint8_t )0xed,
      (uint8_t )0xf2,
      (uint8_t )0x78,
      (uint8_t )0x5e,
      (uint8_t )0x42,
      (uint8_t )0x87,
      (uint8_t )0x4d
    };
uint8_t
key[32] =
    {
      (uint8_t )0,
      (uint8_t )1,
      (uint8_t )2,
      (uint8_t )3,
      (uint8_t )4,
      (uint8_t )5,
      (uint8_t )6,
      (uint8_t )7,
      (uint8_t )8,
      (uint8_t )9,
      (uint8_t )10,
      (uint8_t )11,
      (uint8_t )12,
      (uint8_t )13,
      (uint8_t )14,
      (uint8_t )15,
      (uint8_t )16,
      (uint8_t )17,
      (uint8_t )18,
      (uint8_t )19,
      (uint8_t )20,
      (uint8_t )21,
      (uint8_t )22,
      (uint8_t )23,
      (uint8_t )24,
      (uint8_t )25,
      (uint8_t )26,
      (uint8_t )27,
      (uint8_t )28,
      (uint8_t )29,
      (uint8_t )30,
      (uint8_t )31
    };
uint8_t
nonce[12] =
    {
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0x4a,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0
    };

int32_t test_chacha()
{
  uint32_t len = (uint32_t )114;
  uint8_t ciphertext[len];
  memset(ciphertext, 0, len * sizeof ciphertext[0]); 
  uint32_t counter = (uint32_t )1;
  uint32_t ctx[32] = { 0 };
  Hacl_Symmetric_Chacha20_chacha_keysetup(ctx, key);
  Hacl_Symmetric_Chacha20_chacha_ietf_ivsetup(ctx, nonce, counter);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes(ctx, plaintext, ciphertext, len);
  TestLib_compare_and_print("HACL Chacha20", expected, ciphertext, len);

  //  crypto_stream_chacha20_ietf_xor(ciphertext,plaintext, len, nonce, key);
  // TestLib_compare_and_print("Sodium Chacha20", expected, ciphertext, len);

  return exit_success;
}

int32_t perf_chacha() {
  uint32_t len = PLAINLEN * sizeof(char);
  uint8_t* plain = malloc(len);
  uint8_t* cipher = malloc(len);
  int fd = open("/dev/random", O_RDONLY);
  uint64_t res = read(fd, plain, len);
  if (res != len) {
    printf("Error on reading, got %llu bytes\n", res);
    return 1;
  }

  uint32_t counter = (uint32_t )1;
  uint32_t ctx[32] = { 0 };

  cycles a,b;
  clock_t t1,t2;
  t1 = clock();
  a = TestLib_cpucycles();
  for (int i = 0; i < ROUNDS; i++){
    Hacl_Symmetric_Chacha20_chacha_keysetup(ctx, key);
    Hacl_Symmetric_Chacha20_chacha_ietf_ivsetup(ctx, nonce, counter);
    Hacl_Symmetric_Chacha20_chacha_encrypt_bytes(ctx, plain, plain, len);
  }
  b = TestLib_cpucycles();
  t2 = clock();
  print_results("HACL ChaCha20 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < PLAINLEN; i++) 
    res += (uint64_t) plain[i];
  printf("Composite result (ignore): %llx\n", res);
  t1 = clock();
  a = TestLib_cpucycles();
  for (int i = 0; i < ROUNDS; i++){
    crypto_stream_chacha20_ietf_xor(cipher,plain, len, nonce, key);
  }
  b = TestLib_cpucycles();
  t2 = clock();
  print_results("Sodium ChaCha20 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < PLAINLEN; i++) 
    res += (uint64_t) plain[i];
  printf("Composite result (ignore): %llx\n", res);
  return exit_success;
}

int32_t main()
{
  int32_t res = test_chacha();
  if (res == exit_success) {
    res = perf_chacha();
  }
  return res;
}
  
