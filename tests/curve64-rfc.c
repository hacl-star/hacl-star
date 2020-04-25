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

#include "test_helpers.h"
#include "curve25519_vectors.h"

typedef __attribute__((aligned(32))) uint8_t X25519_KEY[32];

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

extern void x25519_shared_secret_x64(uint8_t* sec, uint8_t* priv, uint8_t* pub);

#define ROUNDS 100000
#define SIZE   1

void print_time(clock_t tdiff, cycles cdiff){
  uint64_t count = ROUNDS * SIZE;
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cdiff,(double)cdiff/count);
  printf("time for %" PRIu64 " bytes: %" PRIu64 " (%.2fus/byte)\n",count,(uint64_t)tdiff,(double)tdiff/count);
  printf("bw %8.2f MB/s\n",(double)count/(((double)tdiff / CLOCKS_PER_SEC) * 1000000.0));
}


bool print_result(int in_len, uint8_t* comp, uint8_t* exp) {
  return compare_and_print(in_len, comp, exp);
}

bool print_test(uint8_t* scalar, uint8_t* pub, uint8_t* exp){
  uint8_t comp[32] = {0};

  x25519_shared_secret_x64(comp,pub,scalar);
  printf("Curve25519 (RFC7794 Original 64-bit) Result:\n");
  bool ok = print_result(32,comp,exp);
  return ok;
}


int main() {
  uint8_t *scalar0 = vectors[0].scalar;
  uint8_t *pub0 = vectors[0].public;
  uint8_t *exp0 = vectors[0].secret;

  uint8_t *scalar1 = vectors[1].scalar;
  uint8_t *pub1 = vectors[1].public;
  uint8_t *exp1 = vectors[1].secret;

  bool ok = print_test(scalar0,pub0,exp0);
  ok = print_test(scalar1,pub1,exp1) && ok;


  X25519_KEY pub, priv, key;
  uint64_t res = 0;
  cycles a,b;
  clock_t t1,t2;

  memset(pub,'P',32);
  memset(priv,'S',32);
  for (int j = 0; j < ROUNDS; j++) {
    x25519_shared_secret_x64(pub,priv,pub);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    x25519_shared_secret_x64(key,priv,pub);
    res ^= key[0] ^ key[15];
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff1 = t2 - t1;
  cycles cdiff1 = b - a;

  double time = (((double)tdiff1) / CLOCKS_PER_SEC);
  double nsigs = ((double)ROUNDS) / time;
  printf("Curve25519 (RFC7748 Original) PERF:\n"); print_time(tdiff1,cdiff1);
  printf("smult %8.2f mul/s\n",nsigs);

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
