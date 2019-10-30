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

#include "Hacl_Chacha20Poly1305_32.h"
#include "Hacl_Chacha20Poly1305_128.h"
#include "Hacl_Chacha20Poly1305_256.h"

#define ROUNDS 100000
#define SIZE   16384

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

extern void
Hacl_Chacha20Poly1305_32_aead_encrypt(uint8_t *k, uint8_t *n1, uint32_t aadlen, uint8_t *aad, uint32_t mlen, uint8_t *m, uint8_t *cipher, uint8_t *mac);
extern void
Hacl_Chacha20Poly1305_128_aead_encrypt(uint8_t *k, uint8_t *n1, uint32_t aadlen, uint8_t *aad, uint32_t mlen, uint8_t *m, uint8_t *cipher, uint8_t *mac);
extern void
Hacl_Chacha20Poly1305_256_aead_encrypt(uint8_t *k, uint8_t *n1, uint32_t aadlen, uint8_t *aad, uint32_t mlen, uint8_t *m, uint8_t *cipher, uint8_t *mac);

extern uint32_t
Hacl_Chacha20Poly1305_32_aead_decrypt(uint8_t *k, uint8_t *n1, uint32_t aadlen, uint8_t *aad, uint32_t mlen, uint8_t *m, uint8_t *cipher, uint8_t *mac);
extern uint32_t
Hacl_Chacha20Poly1305_128_aead_decrypt(uint8_t *k, uint8_t *n1, uint32_t aadlen, uint8_t *aad, uint32_t mlen, uint8_t *m, uint8_t *cipher, uint8_t *mac);
extern uint32_t
Hacl_Chacha20Poly1305_256_aead_decrypt(uint8_t *k, uint8_t *n1, uint32_t aadlen, uint8_t *aad, uint32_t mlen, uint8_t *m, uint8_t *cipher, uint8_t *mac);

uint8_t
aead_plaintext[114] = {
  0x4c, 0x61, 0x64, 0x69, 0x65, 0x73, 0x20, 0x61, 0x6e, 0x64, 0x20, 0x47, 0x65, 0x6e, 0x74, 0x6c,
  0x65, 0x6d, 0x65, 0x6e, 0x20, 0x6f, 0x66, 0x20, 0x74, 0x68, 0x65, 0x20, 0x63, 0x6c, 0x61, 0x73,
  0x73, 0x20, 0x6f, 0x66, 0x20, 0x27, 0x39, 0x39, 0x3a, 0x20, 0x49, 0x66, 0x20, 0x49, 0x20, 0x63,
  0x6f, 0x75, 0x6c, 0x64, 0x20, 0x6f, 0x66, 0x66, 0x65, 0x72, 0x20, 0x79, 0x6f, 0x75, 0x20, 0x6f,
  0x6e, 0x6c, 0x79, 0x20, 0x6f, 0x6e, 0x65, 0x20, 0x74, 0x69, 0x70, 0x20, 0x66, 0x6f, 0x72, 0x20,
  0x74, 0x68, 0x65, 0x20, 0x66, 0x75, 0x74, 0x75, 0x72, 0x65, 0x2c, 0x20, 0x73, 0x75, 0x6e, 0x73,
  0x63, 0x72, 0x65, 0x65, 0x6e, 0x20, 0x77, 0x6f, 0x75, 0x6c, 0x64, 0x20, 0x62, 0x65, 0x20, 0x69,
  0x74, 0x2e };

uint8_t aead_nonce[12] = {
  0x07, 0x00, 0x00, 0x00, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47 };

uint8_t aead_key[32] = {
  0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d, 0x8e, 0x8f,
  0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9a, 0x9b, 0x9c, 0x9d, 0x9e, 0x9f };

uint8_t aead_aad[12] = {
  0x50, 0x51, 0x52, 0x53, 0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7 };

uint8_t aead_ciphertext[114] = {
  0xd3, 0x1a, 0x8d, 0x34, 0x64, 0x8e, 0x60, 0xdb, 0x7b, 0x86, 0xaf, 0xbc, 0x53, 0xef, 0x7e, 0xc2,
  0xa4, 0xad, 0xed, 0x51, 0x29, 0x6e, 0x08, 0xfe, 0xa9, 0xe2, 0xb5, 0xa7, 0x36, 0xee, 0x62, 0xd6,
  0x3d, 0xbe, 0xa4, 0x5e, 0x8c, 0xa9, 0x67, 0x12, 0x82, 0xfa, 0xfb, 0x69, 0xda, 0x92, 0x72, 0x8b,
  0x1a, 0x71, 0xde, 0x0a, 0x9e, 0x06, 0x0b, 0x29, 0x05, 0xd6, 0xa5, 0xb6, 0x7e, 0xcd, 0x3b, 0x36,
  0x92, 0xdd, 0xbd, 0x7f, 0x2d, 0x77, 0x8b, 0x8c, 0x98, 0x03, 0xae, 0xe3, 0x28, 0x09, 0x1b, 0x58,
  0xfa, 0xb3, 0x24, 0xe4, 0xfa, 0xd6, 0x75, 0x94, 0x55, 0x85, 0x80, 0x8b, 0x48, 0x31, 0xd7, 0xbc,
  0x3f, 0xf4, 0xde, 0xf0, 0x8e, 0x4b, 0x7a, 0x9d, 0xe5, 0x76, 0xd2, 0x65, 0x86, 0xce, 0xc6, 0x4b,
  0x61, 0x16 };

uint8_t aead_mac[16] = {
  0x1a, 0xe1, 0x0b, 0x59, 0x4f, 0x09, 0xe2, 0x6a, 0x7e, 0x90, 0x2e, 0xcb, 0xd0, 0x60, 0x06, 0x91 };

int main(){
  int res;
  uint8_t plaintext[114];
  memset(plaintext, 0, 114 * sizeof plaintext[0]);
  uint8_t ciphertext[114];
  memset(ciphertext, 0, 114 * sizeof ciphertext[0]);
  uint8_t mac[16];
  memset(mac, 0, 16 * sizeof mac[0]);

  printf("Testing HACL* Hacl_Chacha20Poly1305 (32-bit)\n");
  Hacl_Chacha20Poly1305_32_aead_encrypt(aead_key, aead_nonce, 12, aead_aad, 114, aead_plaintext, ciphertext, mac);
  res = memcmp(ciphertext, aead_ciphertext, 114 * sizeof (uint8_t));
  if (res != 0){
    printf("AEAD (Chacha20) failed on RFC test of size 114\n.");
  }
  res = memcmp(mac, aead_mac, 16 * sizeof (uint8_t));
  if (res != 0){
    printf("AEAD (Poly1305) failed on RFC test of size 114\n.");
  }

  res = Hacl_Chacha20Poly1305_32_aead_decrypt(aead_key, aead_nonce, 12, aead_aad, 114, plaintext, aead_ciphertext, aead_mac);
  if (res != 0){
    printf("AEAD Decrypt (Chacha20/Poly1305) failed on RFC test of size 114\n.");
  }
  res = memcmp(plaintext, aead_plaintext, 114 * sizeof (uint8_t));
  if (res != 0){
    printf("AEAD Decrypt (Chacha20/Poly1305) failed on RFC test of size 114\n.");
  }

  if (res == 0){
    printf("\nSuccess !\n");
  } else {
    printf("\nFailure !\n");
  }

  res = 0;
  printf("Testing HACL* Hacl_Chacha20Poly1305 (128-bit)\n");
  Hacl_Chacha20Poly1305_128_aead_encrypt(aead_key, aead_nonce, 12, aead_aad, 114, aead_plaintext, ciphertext, mac);
  res = memcmp(ciphertext, aead_ciphertext, 114 * sizeof (uint8_t));
  if (res != 0){
    printf("AEAD (Chacha20) failed on RFC test of size 114\n.");
  }
  res = memcmp(mac, aead_mac, 16 * sizeof (uint8_t));
  if (res != 0){
    printf("AEAD (Poly1305) failed on RFC test of size 114\n.");
  }

  res = Hacl_Chacha20Poly1305_128_aead_decrypt(aead_key, aead_nonce, 12, aead_aad, 114, plaintext, aead_ciphertext, aead_mac);
  if (res != 0){
    printf("AEAD Decrypt (Chacha20/Poly1305) failed on RFC test of size 114\n.");
  }
  res = memcmp(plaintext, aead_plaintext, 114 * sizeof (uint8_t));
  if (res != 0){
    printf("AEAD Decrypt (Chacha20/Poly1305) failed on RFC test of size 114\n.");
  }

  if (res == 0){
    printf("\nSuccess !\n");
  } else {
    printf("\nFailure !\n");
  }

  res = 0;
  printf("Testing HACL* Hacl_Chacha20Poly1305 (256-bit)\n");
  Hacl_Chacha20Poly1305_256_aead_encrypt(aead_key, aead_nonce, 12, aead_aad, 114, aead_plaintext, ciphertext, mac);
  res = memcmp(ciphertext, aead_ciphertext, 114 * sizeof (uint8_t));
  if (res != 0){
    printf("AEAD (Chacha20) failed on RFC test of size 114\n.");
  }
  res = memcmp(mac, aead_mac, 16 * sizeof (uint8_t));
  if (res != 0){
    printf("AEAD (Poly1305) failed on RFC test of size 114\n.");
  }

  res = Hacl_Chacha20Poly1305_256_aead_decrypt(aead_key, aead_nonce, 12, aead_aad, 114, plaintext, aead_ciphertext, aead_mac);
  if (res != 0){
    printf("AEAD Decrypt (Chacha20/Poly1305) failed on RFC test of size 114\n.");
  }
  res = memcmp(plaintext, aead_plaintext, 114 * sizeof (uint8_t));
  if (res != 0){
    printf("AEAD Decrypt (Chacha20/Poly1305) failed on RFC test of size 114\n.");
  }

  if (res == 0){
    printf("\nSuccess !\n");
  } else {
    printf("\nFailure !\n");
  }



  uint8_t plain[SIZE];
  uint8_t cipher[SIZE];
  res = 0;
  uint8_t tag[16];
  cycles a,b;
  clock_t t1,t2;
  uint64_t count = ROUNDS * SIZE;

  memset(plain,'P',SIZE);
  memset(aead_key,'K',32);
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20Poly1305_32_aead_encrypt(aead_key, aead_nonce, 12, aead_aad, SIZE, plain, cipher, tag);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20Poly1305_32_aead_encrypt(aead_key, aead_nonce, 12, aead_aad, SIZE, plain, cipher, tag);
    res ^= tag[0] ^ tag[15];
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff1 = t2 - t1;
  cycles cdiff1 = b - a;

  memset(plain,'P',SIZE);
  memset(aead_key,'K',32);
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20Poly1305_128_aead_encrypt(aead_key, aead_nonce, 12, aead_aad, SIZE, plain, cipher, tag);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20Poly1305_128_aead_encrypt(aead_key, aead_nonce, 12, aead_aad, SIZE, plain, cipher, tag);
    res ^= tag[0] ^ tag[15];
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff2 = t2 - t1;
  cycles cdiff2 = b - a;

  memset(plain,'P',SIZE);
  memset(aead_key,'K',32);
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20Poly1305_256_aead_encrypt(aead_key, aead_nonce, 12, aead_aad, SIZE, plain, cipher, tag);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20Poly1305_256_aead_encrypt(aead_key, aead_nonce, 12, aead_aad, SIZE, plain, cipher, tag);
    res ^= tag[0] ^ tag[15];
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff3 = t2 - t1;
  cycles cdiff3 = b - a;


  int res1 = 0;
  for (int j = 0; j < ROUNDS; j++) {
    res1 = Hacl_Chacha20Poly1305_32_aead_decrypt(aead_key, aead_nonce, 12, aead_aad, SIZE, plain, cipher, tag);
    res1 ^= res1;
  }

  res1 = 0;
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20Poly1305_32_aead_decrypt(aead_key, aead_nonce, 12, aead_aad, SIZE, plain, cipher, tag);
    res1 ^= res1;
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff4 = t2 - t1;
  cycles cdiff4 = b - a;


  res1 = 0;
  for (int j = 0; j < ROUNDS; j++) {
    res1 = Hacl_Chacha20Poly1305_128_aead_decrypt(aead_key, aead_nonce, 12, aead_aad, SIZE, plain, cipher, tag);
    res1 ^= res1;
  }

  res1 = 0;
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20Poly1305_128_aead_decrypt(aead_key, aead_nonce, 12, aead_aad, SIZE, plain, cipher, tag);
    res1 ^= res1;
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff5 = t2 - t1;
  cycles cdiff5 = b - a;

  res1 = 0;
  for (int j = 0; j < ROUNDS; j++) {
    res1 = Hacl_Chacha20Poly1305_256_aead_decrypt(aead_key, aead_nonce, 12, aead_aad, SIZE, plain, cipher, tag);
    res1 ^= res1;
  }

  res1 = 0;
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20Poly1305_256_aead_decrypt(aead_key, aead_nonce, 12, aead_aad, SIZE, plain, cipher, tag);
    res1 ^= res1;
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff6 = t2 - t1;
  cycles cdiff6 = b - a;
  printf ("\n res1: %i \n", res1);

  printf("\n\nChacha20Poly1305 Encrypt (32-bit) PERF:\n");
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cdiff1,(double)cdiff1/count);
  printf("time for %" PRIu64 " bytes: %" PRIu64 " (%.2fus/byte)\n",count,(uint64_t)tdiff1,(double)tdiff1/count);
  printf("bw %8.2f MB/s\n",(double)count/(((double)tdiff1 / CLOCKS_PER_SEC) * 1000000.0));

  printf("Chacha20Poly1305 Encrypt (128-bit) PERF:\n");
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cdiff2,(double)cdiff2/count);
  printf("time for %" PRIu64 " bytes: %" PRIu64 " (%.2fus/byte)\n",count,(uint64_t)tdiff2,(double)tdiff2/count);
  printf("bw %8.2f MB/s\n",(double)count/(((double)tdiff2 / CLOCKS_PER_SEC) * 1000000.0));

  printf("Chacha20Poly1305 Encrypt (256-bit) PERF:\n");
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cdiff3,(double)cdiff3/count);
  printf("time for %" PRIu64 " bytes: %" PRIu64 " (%.2fus/byte)\n",count,(uint64_t)tdiff3,(double)tdiff3/count);
  printf("bw %8.2f MB/s\n",(double)count/(((double)tdiff3 / CLOCKS_PER_SEC) * 1000000.0));

  printf("\n\nChacha20Poly1305 Decrypt (32-bit) PERF:\n");
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cdiff4,(double)cdiff4/count);
  printf("time for %" PRIu64 " bytes: %" PRIu64 " (%.2fus/byte)\n",count,(uint64_t)tdiff4,(double)tdiff4/count);
  printf("bw %8.2f MB/s\n",(double)count/(((double)tdiff4 / CLOCKS_PER_SEC) * 1000000.0));

  printf("Chacha20Poly1305 Decrypt (128-bit) PERF:\n");
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cdiff5,(double)cdiff5/count);
  printf("time for %" PRIu64 " bytes: %" PRIu64 " (%.2fus/byte)\n",count,(uint64_t)tdiff5,(double)tdiff5/count);
  printf("bw %8.2f MB/s\n",(double)count/(((double)tdiff5 / CLOCKS_PER_SEC) * 1000000.0));

  printf("Chacha20Poly1305 Decrypt (256-bit) PERF:\n");
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cdiff6,(double)cdiff6/count);
  printf("time for %" PRIu64 " bytes: %" PRIu64 " (%.2fus/byte)\n",count,(uint64_t)tdiff6,(double)tdiff6/count);
  printf("bw %8.2f MB/s\n",(double)count/(((double)tdiff6 / CLOCKS_PER_SEC) * 1000000.0));

}
