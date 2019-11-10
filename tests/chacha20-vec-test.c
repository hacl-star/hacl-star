#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <time.h>
#include <stdbool.h>
//#include "openssl/chacha.h"

//#define ossl_chacha20(cipher,plain,len,nonce,key,ctr) (CRYPTO_chacha_20(cipher,plain,len,nonce,key,ctr))

typedef uint64_t cycles;

static __inline__ cycles cpucycles_begin(void)
{
  uint64_t rax,rdx,aux;
  asm volatile ( "rdtscp\n" : "=a" (rax), "=d" (rdx), "=c" (aux) : : );
  return (rdx << 32) + rax;
  //  unsigned hi, lo;
  //__asm__ __volatile__ ("CPUID\n\t"  "RDTSC\n\t"  "mov %%edx, %0\n\t"  "mov %%eax, %1\n\t": "=r" (hi), "=r" (lo):: "%rax", "%rbx", "%rcx", "%rdx");
  //return ( (uint64_t)lo)|( ((uint64_t)hi)<<32 );
}

static __inline__ cycles cpucycles_end(void)
{
  uint64_t rax,rdx,aux;
  asm volatile ( "rdtscp\n" : "=a" (rax), "=d" (rdx), "=c" (aux) : : );
  return (rdx << 32) + rax;
  //  unsigned hi, lo;
  //__asm__ __volatile__ ("RDTSCP\n\t"  "mov %%edx, %0\n\t"  "mov %%eax, %1\n\t"  "CPUID\n\t": "=r" (hi), "=r" (lo)::     "%rax", "%rbx", "%rcx", "%rdx");
  //return ( (uint64_t)lo)|( ((uint64_t)hi)<<32 );
}

extern void Hacl_Chacha20_Vec32_chacha20_encrypt_32(int in_len, uint8_t* out, uint8_t* in, uint8_t* k, uint8_t* n, uint32_t c);
extern void Hacl_Chacha20_Vec128_chacha20_encrypt_128(int in_len, uint8_t* out, uint8_t* in, uint8_t* k, uint8_t* n, uint32_t c);
extern void Hacl_Chacha20_Vec256_chacha20_encrypt_256(int in_len, uint8_t* out, uint8_t* in, uint8_t* k, uint8_t* n, uint32_t c);


#define ROUNDS 100000
#define SIZE   8192

int main() {
  int in_len = 114;
  uint8_t in[114] = {
    0x4c, 0x61, 0x64, 0x69, 0x65, 0x73, 0x20, 0x61,
    0x6e, 0x64, 0x20, 0x47, 0x65, 0x6e, 0x74, 0x6c,
    0x65, 0x6d, 0x65, 0x6e, 0x20, 0x6f, 0x66, 0x20,
    0x74, 0x68, 0x65, 0x20, 0x63, 0x6c, 0x61, 0x73,
    0x73, 0x20, 0x6f, 0x66, 0x20, 0x27, 0x39, 0x39,
    0x3a, 0x20, 0x49, 0x66, 0x20, 0x49, 0x20, 0x63,
    0x6f, 0x75, 0x6c, 0x64, 0x20, 0x6f, 0x66, 0x66,
    0x65, 0x72, 0x20, 0x79, 0x6f, 0x75, 0x20, 0x6f,
    0x6e, 0x6c, 0x79, 0x20, 0x6f, 0x6e, 0x65, 0x20,
    0x74, 0x69, 0x70, 0x20, 0x66, 0x6f, 0x72, 0x20,
    0x74, 0x68, 0x65, 0x20, 0x66, 0x75, 0x74, 0x75,
    0x72, 0x65, 0x2c, 0x20, 0x73, 0x75, 0x6e, 0x73,
    0x63, 0x72, 0x65, 0x65, 0x6e, 0x20, 0x77, 0x6f,
    0x75, 0x6c, 0x64, 0x20, 0x62, 0x65, 0x20, 0x69,
    0x74, 0x2e
  };
  uint8_t k[32] = {
    0,   1,  2,  3,  4,  5,  6,  7,
    8,   9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23,
    24, 25, 26, 27, 28, 29, 30, 31
  };
  uint8_t n[12] = {
    0, 0, 0, 0, 0, 0, 0, 0x4a, 0, 0, 0, 0
  };
  uint8_t exp[114] = {
    0x6e, 0x2e, 0x35, 0x9a, 0x25, 0x68, 0xf9, 0x80,
    0x41, 0xba, 0x07, 0x28, 0xdd, 0x0d, 0x69, 0x81,
    0xe9, 0x7e, 0x7a, 0xec, 0x1d, 0x43, 0x60, 0xc2,
    0x0a, 0x27, 0xaf, 0xcc, 0xfd, 0x9f, 0xae, 0x0b,
    0xf9, 0x1b, 0x65, 0xc5, 0x52, 0x47, 0x33, 0xab,
    0x8f, 0x59, 0x3d, 0xab, 0xcd, 0x62, 0xb3, 0x57,
    0x16, 0x39, 0xd6, 0x24, 0xe6, 0x51, 0x52, 0xab,
    0x8f, 0x53, 0x0c, 0x35, 0x9f, 0x08, 0x61, 0xd8,
    0x07, 0xca, 0x0d, 0xbf, 0x50, 0x0d, 0x6a, 0x61,
    0x56, 0xa3, 0x8e, 0x08, 0x8a, 0x22, 0xb6, 0x5e,
    0x52, 0xbc, 0x51, 0x4d, 0x16, 0xcc, 0xf8, 0x06,
    0x81, 0x8c, 0xe9, 0x1a, 0xb7, 0x79, 0x37, 0x36,
    0x5a, 0xf9, 0x0b, 0xbf, 0x74, 0xa3, 0x5b, 0xe6,
    0xb4, 0x0b, 0x8e, 0xed, 0xf2, 0x78, 0x5e, 0x42,
    0x87, 0x4d
  };
  uint8_t comp[114] = {0};
  Hacl_Chacha20_Vec32_chacha20_encrypt_32(in_len,comp,in,k,n,1);
  printf("computed:");
  for (int i = 0; i < 114; i++)
    printf("%02x",comp[i]);
  printf("\n");
  printf("expected:");
  for (int i = 0; i < 114; i++)
    printf("%02x",exp[i]);
  printf("\n");
  bool ok = true;
  for (int i = 0; i < 114; i++)
    ok = ok & (exp[i] == comp[i]);
  if (ok) printf("Success!\n");
  else printf("FAILED!\n");

  Hacl_Chacha20_Vec128_chacha20_encrypt_128(in_len,comp,in,k,n,1);
  printf("computed:");
  for (int i = 0; i < 114; i++)
    printf("%02x",comp[i]);
  printf("\n");
  printf("expected:");
  for (int i = 0; i < 114; i++)
    printf("%02x",exp[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 114; i++)
    ok = ok & (exp[i] == comp[i]);
  if (ok) printf("Success!\n");
  else printf("FAILED!\n");

  Hacl_Chacha20_Vec256_chacha20_encrypt_256(in_len,comp,in,k,n,1);
  printf("computed:");
  for (int i = 0; i < 114; i++)
    printf("%02x",comp[i]);
  printf("\n");
  printf("expected:");
  for (int i = 0; i < 114; i++)
    printf("%02x",exp[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 114; i++)
    ok = ok & (exp[i] == comp[i]);
  if (ok) printf("Success!\n");
  else printf("FAILED!\n");

/*
  ossl_chacha20(comp,in,in_len,k,n,1);
  printf("OpenSSL computed:");
  for (int i = 0; i < 114; i++)
    printf("%02x",comp[i]);
  printf("\n");
  printf("expected:");
  for (int i = 0; i < 114; i++)
    printf("%02x",exp[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 32; i++)
    ok = ok & (exp[i] == comp[i]);
  if (ok) printf("Success!\n");
  else printf("FAILED!\n");
*/

  uint64_t len = SIZE;
  uint8_t plain[SIZE];
  uint8_t key[16];
  uint8_t nonce[12];
  cycles a,b;
  clock_t t1,t2;

  memset(plain,'P',SIZE);
  memset(key,'K',16);
  memset(nonce,'N',12);

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20_Vec32_chacha20_encrypt_32(SIZE,plain,plain,key,nonce,1);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20_Vec32_chacha20_encrypt_32(SIZE,plain,plain,key,nonce,1);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff1 = (double)(t2 - t1)/CLOCKS_PER_SEC;
  uint64_t cyc1 = b - a;

  memset(plain,'P',SIZE);
  memset(key,'K',16);
  memset(nonce,'N',12);

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20_Vec128_chacha20_encrypt_128(SIZE,plain,plain,key,nonce,1);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20_Vec128_chacha20_encrypt_128(SIZE,plain,plain,key,nonce,1);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff2 = (double)(t2 - t1)/CLOCKS_PER_SEC;
  uint64_t cyc2 = b - a;

  memset(plain,'P',SIZE);
  memset(key,'K',16);
  memset(nonce,'N',12);

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20_Vec256_chacha20_encrypt_256(SIZE,plain,plain,key,nonce,1);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20_Vec256_chacha20_encrypt_256(SIZE,plain,plain,key,nonce,1);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff3 = (double)(t2 - t1)/CLOCKS_PER_SEC;
  uint64_t cyc3 = b - a;

/*
  memset(plain,'P',SIZE);
  memset(key,'K',16);
  memset(nonce,'N',12);

  for (int j = 0; j < ROUNDS; j++) {
    ossl_chacha20(plain,plain,SIZE,key,nonce,1);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    ossl_chacha20(plain,plain,SIZE,key,nonce,1);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff6 = (double)(t2 - t1)/CLOCKS_PER_SEC;
  uint64_t cyc6 = b - a;
*/

  uint64_t count = ROUNDS * SIZE;

  printf("32-bit Chacha20\n");
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cyc1,(double)cyc1/count);
  printf("bw %8.2f MB/s\n",(double)count/(diff1 * 1000000.0));

  printf("128-bit Chacha20\n");
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cyc2,(double)cyc2/count);
  printf("bw %8.2f MB/s\n",(double)count/(diff2 * 1000000.0));

  printf("256-bit Chacha20\n");
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cyc3,(double)cyc3/count);
  printf("bw %8.2f MB/s\n",(double)count/(diff3 * 1000000.0));

/*
  printf("OpenSSL Chacha20\n");
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cyc6,(double)cyc6/count);
  printf("bw %8.2f MB/s\n",(double)count/(diff6 * 1000000.0));
  */
}
