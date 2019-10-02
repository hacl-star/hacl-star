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

extern void Hacl_Salsa20_salsa20_encrypt(int in_len, uint8_t* out, uint8_t* in, uint8_t* k, uint8_t* n, uint32_t c);

#define ROUNDS 16384
#define SIZE   81920

int main() {
  int in_len = 512;
  uint8_t in[512] = {0};
  uint8_t k[32] = {0};
  k[0] = 0x80;
  uint8_t n[8] = {0};

  uint8_t exp1[64] = {
    0xE3, 0xBE, 0x8F, 0xDD, 0x8B, 0xEC, 0xA2, 0xE3, 0xEA, 0x8E, 0xF9, 0x47, 0x5B, 0x29, 0xA6, 0xE7,
    0x00, 0x39, 0x51, 0xE1, 0x09, 0x7A, 0x5C, 0x38, 0xD2, 0x3B, 0x7A, 0x5F, 0xAD, 0x9F, 0x68, 0x44,
    0xB2, 0x2C, 0x97, 0x55, 0x9E, 0x27, 0x23, 0xC7, 0xCB, 0xBD, 0x3F, 0xE4, 0xFC, 0x8D, 0x9A, 0x07,
    0x44, 0x65, 0x2A, 0x83, 0xE7, 0x2A, 0x9C, 0x46, 0x18, 0x76, 0xAF, 0x4D, 0x7E, 0xF1, 0xA1, 0x17
    };
  uint8_t exp2[64] = {
    0x57, 0xBE, 0x81, 0xF4, 0x7B, 0x17, 0xD9, 0xAE, 0x7C, 0x4F, 0xF1, 0x54, 0x29, 0xA7, 0x3E, 0x10,
    0xAC, 0xF2, 0x50, 0xED, 0x3A, 0x90, 0xA9, 0x3C, 0x71, 0x13, 0x08, 0xA7, 0x4C, 0x62, 0x16, 0xA9,
    0xED, 0x84, 0xCD, 0x12, 0x6D, 0xA7, 0xF2, 0x8E, 0x8A, 0xBF, 0x8B, 0xB6, 0x35, 0x17, 0xE1, 0xCA,
    0x98, 0xE7, 0x12, 0xF4, 0xFB, 0x2E, 0x1A, 0x6A, 0xED, 0x9F, 0xDC, 0x73, 0x29, 0x1F, 0xAA, 0x17
    };
  uint8_t exp3[64] = {
    0x95, 0x82, 0x11, 0xC4, 0xBA, 0x2E, 0xBD, 0x58, 0x38, 0xC6, 0x35, 0xED, 0xB8, 0x1F, 0x51, 0x3A,
    0x91, 0xA2, 0x94, 0xE1, 0x94, 0xF1, 0xC0, 0x39, 0xAE, 0xEC, 0x65, 0x7D, 0xCE, 0x40, 0xAA, 0x7E,
    0x7C, 0x0A, 0xF5, 0x7C, 0xAC, 0xEF, 0xA4, 0x0C, 0x9F, 0x14, 0xB7, 0x1A, 0x4B, 0x34, 0x56, 0xA6,
    0x3E, 0x16, 0x2E, 0xC7, 0xD8, 0xD1, 0x0B, 0x8F, 0xFB, 0x18, 0x10, 0xD7, 0x10, 0x01, 0xB6, 0x18
    };
  uint8_t exp4[64] = {
    0x69, 0x6A, 0xFC, 0xFD, 0x0C, 0xDD, 0xCC, 0x83, 0xC7, 0xE7, 0x7F, 0x11, 0xA6, 0x49, 0xD7, 0x9A,
    0xCD, 0xC3, 0x35, 0x4E, 0x96, 0x35, 0xFF, 0x13, 0x7E, 0x92, 0x99, 0x33, 0xA0, 0xBD, 0x6F, 0x53,
    0x77, 0xEF, 0xA1, 0x05, 0xA3, 0xA4, 0x26, 0x6B, 0x7C, 0x0D, 0x08, 0x9D, 0x08, 0xF1, 0xE8, 0x55,
    0xCC, 0x32, 0xB1, 0x5B, 0x93, 0x78, 0x4A, 0x36, 0xE5, 0x6A, 0x76, 0xCC, 0x64, 0xBC, 0x84, 0x77
    };

  uint8_t comp[512] = {0};
  bool ok;
  Hacl_Salsa20_salsa20_encrypt(in_len,comp,in,k,n,0);
  printf("computed1:");
  for (int i = 0; i < 64; i++)
    printf("%02x",comp[i]);
  printf("\n");
  printf("expected1:");
  for (int i = 0; i < 64; i++)
    printf("%02x",exp1[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 64; i++)
    ok = ok & (exp1[i] == comp[i]);
  if (ok) printf("Success!\n");
  else printf("FAILED!\n");

  printf("computed2:");
  for (int i = 0; i < 64; i++)
    printf("%02x",comp[192+i]);
  printf("\n");
  printf("expected2:");
  for (int i = 0; i < 64; i++)
    printf("%02x",exp2[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 64; i++)
    ok = ok & (exp2[i] == comp[192+i]);
  if (ok) printf("Success!\n");
  else printf("FAILED!\n");

  printf("computed3:");
  for (int i = 0; i < 64; i++)
    printf("%02x",comp[256+i]);
  printf("\n");
  printf("expected3:");
  for (int i = 0; i < 64; i++)
    printf("%02x",exp3[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 64; i++)
    ok = ok & (exp3[i] == comp[256+i]);
  if (ok) printf("Success!\n");
  else printf("FAILED!\n");

  printf("computed4:");
  for (int i = 0; i < 64; i++)
    printf("%02x",comp[448+i]);
  printf("\n");
  printf("expected4:");
  for (int i = 0; i < 64; i++)
    printf("%02x",exp4[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 64; i++)
    ok = ok & (exp4[i] == comp[448+i]);
  if (ok) printf("Success!\n");
  else printf("FAILED!\n");

  uint64_t len = SIZE;
  uint8_t plain[SIZE];
  uint8_t key[16];
  uint8_t nonce[12];
  memset(plain,'P',SIZE);
  memset(key,'K',16);
  memset(nonce,'N',12);

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Salsa20_salsa20_encrypt(SIZE,plain,plain,key,nonce,1);
  }

  cycles a,b;
  clock_t t1,t2;
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Salsa20_salsa20_encrypt(SIZE,plain,plain,key,nonce,1);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff = (double)(t2 - t1)/CLOCKS_PER_SEC;

  uint64_t count = ROUNDS * SIZE;
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)(b-a),(double)(b-a)/count);
  printf("time for %" PRIu64 " bytes: %" PRIu64 " (%.2fus/byte)\n",count,(uint64_t)(t2-t1),(double)(t2-t1)/count);
  printf("bw %8.2f MB/s\n",(double)count/(diff * 1000000.0));
  
}
