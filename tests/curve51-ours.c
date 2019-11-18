#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdbool.h>
#include <time.h>

#include "Hacl_Curve25519_51.h"

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

#define ROUNDS 100000
#define SIZE   1

int main() {
  uint8_t pub[32];
  uint8_t priv[32];
  uint8_t key[32];
  uint64_t res = 0;
  uint8_t tag[64];
  cycles a,b;
  clock_t t1,t2;
  uint64_t count = ROUNDS * SIZE;

  int in_len = 34;
  uint8_t scalar1[32] = {
    0xa5, 0x46, 0xe3, 0x6b, 0xf0, 0x52, 0x7c, 0x9d,
    0x3b, 0x16, 0x15, 0x4b, 0x82, 0x46, 0x5e, 0xdd,
    0x62, 0x14, 0x4c, 0x0a, 0xc1, 0xfc, 0x5a, 0x18,
    0x50, 0x6a, 0x22, 0x44, 0xba, 0x44, 0x9a, 0xc4
  };

  uint8_t scalar2[32] = {
    0x4b, 0x66, 0xe9, 0xd4, 0xd1, 0xb4, 0x67, 0x3c,
    0x5a, 0xd2, 0x26, 0x91, 0x95, 0x7d, 0x6a, 0xf5,
    0xc1, 0x1b, 0x64, 0x21, 0xe0, 0xea, 0x01, 0xd4,
    0x2c, 0xa4, 0x16, 0x9e, 0x79, 0x18, 0xba, 0x0d
  };
  uint8_t pub1[32] = {
    0xe6, 0xdb, 0x68, 0x67, 0x58, 0x30, 0x30, 0xdb,
    0x35, 0x94, 0xc1, 0xa4, 0x24, 0xb1, 0x5f, 0x7c,
    0x72, 0x66, 0x24, 0xec, 0x26, 0xb3, 0x35, 0x3b,
    0x10, 0xa9, 0x03, 0xa6, 0xd0, 0xab, 0x1c, 0x4c
  };
  uint8_t pub2[32] = {
    0xe5, 0x21, 0x0f, 0x12, 0x78, 0x68, 0x11, 0xd3,
    0xf4, 0xb7, 0x95, 0x9d, 0x05, 0x38, 0xae, 0x2c,
    0x31, 0xdb, 0xe7, 0x10, 0x6f, 0xc0, 0x3c, 0x3e,
    0xfc, 0x4c, 0xd5, 0x49, 0xc7, 0x15, 0xa4, 0x93
  };

  uint8_t exp1[32] = {
    0xc3, 0xda, 0x55, 0x37, 0x9d, 0xe9, 0xc6, 0x90,
    0x8e, 0x94, 0xea, 0x4d, 0xf2, 0x8d, 0x08, 0x4f,
    0x32, 0xec, 0xcf, 0x03, 0x49, 0x1c, 0x71, 0xf7,
    0x54, 0xb4, 0x07, 0x55, 0x77, 0xa2, 0x85, 0x52
  };

  uint8_t exp2[32] = {
    0x95, 0xcb, 0xde, 0x94, 0x76, 0xe8, 0x90, 0x7d,
    0x7a, 0xad, 0xe4, 0x5c, 0xb4, 0xb8, 0x73, 0xf8,
    0x8b, 0x59, 0x5a, 0x68, 0x79, 0x9f, 0xa1, 0x52,
    0xe6, 0xf8, 0xf7, 0x64, 0x7a, 0xac, 0x79, 0x57
  };

  uint8_t comp[32] = {0};
  bool ok = true;

  Hacl_Curve25519_51_ecdh(comp,scalar1,pub1);
  printf("Curve25519 (51-bit) Result:\n");
  printf("computed:");
  for (int i = 0; i < 32; i++)
    printf("%02x",comp[i]);
  printf("\n");
  printf("expected:");
  for (int i = 0; i < 32; i++)
    printf("%02x",exp1[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 32; i++)
    ok = ok & (exp1[i] == comp[i]);
  if (ok) printf("Success!\n");
  else printf("**FAILED**\n");

  Hacl_Curve25519_51_ecdh(comp,scalar2,pub2);
  printf("Curve25519 (51-bit) Result:\n");
  printf("computed:");
  for (int i = 0; i < 32; i++)
    printf("%02x",comp[i]);
  printf("\n");
  printf("expected:");
  for (int i = 0; i < 32; i++)
    printf("%02x",exp2[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 32; i++)
    ok = ok & (exp2[i] == comp[i]);
  if (ok) printf("Success!\n");
  else printf("**FAILED**\n");

  memset(pub,'P',32);
  memset(priv,'S',32);
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Curve25519_51_ecdh(pub,priv,pub);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Curve25519_51_ecdh(key,priv,pub);
    res ^= key[0] ^ key[15];
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff1 = t2 - t1;
  cycles cdiff1 = b - a;

  double time = (((double)tdiff1) / CLOCKS_PER_SEC);
  double nsigs = ((double)ROUNDS) / time;
  double nbytes = ((double)count/1000000.0) / time;
  printf("Curve25519 (51-bit) PERF:\n");
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cdiff1,(double)cdiff1/count);
  printf("time for %" PRIu64 " bytes: %" PRIu64 "s (%.2fus/byte)\n",count,(uint64_t)time,((double)time * 1000000.0)/count);
  printf("bw %8.2f MB/s\n",nbytes);
  printf("smult %8.2f mul/s\n",nsigs);
}
