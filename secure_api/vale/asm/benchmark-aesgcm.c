#include <stdio.h>
#include <stdint.h>

#define N 10000
#define NBLOCKS 256
#define OVERHEAD 42

typedef unsigned char byte;

typedef struct args
{
    byte *plain_ptr;
    uint64_t plain_len;
    byte *auth_ptr;
    uint64_t auth_len;
    byte *iv_ptr;
    byte *expanded_key_ptr;
    byte *out_ptr;
    byte *tag_ptr;
} args;

extern void aes128_key_expansion(byte *key_ptr, byte *key_expansion_ptr);
extern void gcm128_encrypt(args *a);

byte key[16] = { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 };
byte expanded_key[11 * 16];
byte plain[16] =
  { 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215 };
byte auth[1]; // actually size 0
byte iv[16] =
  { 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 0, 0, 0, 0 };
byte out[16];
byte tag[16];
byte plain2[NBLOCKS * 16];
byte out2[NBLOCKS * 16];

/*
 See
 https://www.intel.com/content/dam/www/public/us/en/documents/white-papers/ia-32-ia-64-benchmark-code-execution-paper.pdf
*/
static inline void cycles_begin(unsigned *hi, unsigned *lo) {
  asm volatile ("CPUID\n\t" 
                "RDTSC\n\t" 
                "mov %%edx, %0\n\t" 
                "mov %%eax, %1\n\t": "=r" (*hi), "=r" (*lo):: 
                "%rax", "%rbx", "%rcx", "%rdx"); 
}

static inline void cycles_end(unsigned *hi, unsigned *lo) {
  asm volatile("RDTSCP\n\t" 
               "mov %%edx, %0\n\t" 
               "mov %%eax, %1\n\t" 
               "CPUID\n\t": "=r" (*hi), "=r" (*lo)::
               "%rax", "%rbx", "%rcx", "%rdx");
}

void print_bytes(char *label, byte *b, int len)
{
    printf("%s:", label);
    for (int i = 0; i < len; i++) printf(" %2x", b[i]);
    printf("\n");
}

int main(void)
{
  args a = { plain, 1, auth, 0, iv, expanded_key, out, tag };
  
  aes128_key_expansion(key, expanded_key);

  /*
  gcm128_encrypt(&a);

  print_bytes("Ciphertext", out, 16);
  print_bytes("Tag       ", tag, 16);
  
  //Ciphertext: d2 ab 84 6e 17 cf 76 35 4b ef 85 c3 52 1f fd 3b
  //Tag       : f8 7b 6b 54 31 1f 86 c2 87 c2 8e 4d a4 df 96 8c
  */
    
  for (int i = 0; i < NBLOCKS * 16; i++)
    {
      plain2[i] = i % NBLOCKS;
    }
  a.plain_ptr = plain2;
  a.plain_len = NBLOCKS;
  a.out_ptr   = out2;

  printf("Encrypting %u blocks (%u bytes) %u times\n", NBLOCKS, NBLOCKS * 16, N);

  uint64_t total = 0, max = 0, min = UINT64_MAX;
  for (int i = 0; i < 1; i++)
    {
      unsigned hi1, lo1, hi2, lo2, nbytes;
      uint64_t start, end, ncycles;
      for (int j = 0; j < N; j++)
        {
          cycles_begin(&hi1, &lo1);
          gcm128_encrypt(&a);
          cycles_end(&hi2, &lo2);
          start = ( ((uint64_t)hi1 << 32) | lo1 ); 
          end   = ( ((uint64_t)hi2 << 32) | lo2 );
          ncycles = end - start - OVERHEAD;
          total += ncycles;     
          if (ncycles < min) {
            min = ncycles;
          }
          if (ncycles > max) {
            max = ncycles;
          }            
        }
      nbytes = N * NBLOCKS * 16;
      printf("AES-128-GCM cycles per byte (%llu averaged over %d bytes) is %f\n",
             total, nbytes, (double)total / nbytes);
      printf("max = %f; min = %f\n",
             (double)max / (NBLOCKS * 16), (double)min / (NBLOCKS * 16));
    }

    return 0;
}
