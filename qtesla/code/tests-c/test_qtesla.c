/*************************************************************************************
* qTESLA: an efficient post-quantum signature scheme based on the R-LWE problem
*
* Abstract: testing and benchmarking code
**************************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include "random.h"
#include "cpucycles.h"
#include "api.h"
/*#include "../poly.h"
#include "../pack.h"
#include "../sample.h"
#include "../params.h"
#include "../sha3/fips202.h"*/
#include "Hacl_Impl_QTesla.h"
  
#if (OS_TARGET == OS_LINUX)
  #include <sys/types.h>
  #include <sys/stat.h>
  #include <fcntl.h>
  #include <unistd.h>
#endif

#define MLEN 59
#define NRUNS 5000
#define NTESTS 100


static int cmp_llu(const void *a, const void*b)
{
  if (*(unsigned long long *)a < *(unsigned long long *)b) return -1;
  if (*(unsigned long long *)a > *(unsigned long long *)b) return 1;
  return 0;
}


static unsigned long long median(unsigned long long *l, size_t llen)
{
  qsort(l,llen,sizeof(unsigned long long),cmp_llu);

  if (llen%2) return l[llen/2];
  else return (l[llen/2-1]+l[llen/2])/2;
}


static unsigned long long average(unsigned long long *t, size_t tlen)
{
  unsigned long long acc=0;
  size_t i;
  for (i=0; i<tlen; i++)
    acc += t[i];
  return acc/(tlen);
}


static void print_results(const char *s, unsigned long long *t, size_t tlen)
{
  printf("%s", s);
  printf("\n");
  printf(
#ifdef USE_PRINTF_I64
	 "median:  %I64u",
#else
	 "median:  %llu",
#endif
	                  median(t, tlen));  print_unit; printf("\n");
 printf(
#ifdef USE_PRINTF_I64
	 "average: %I64u",
#else
	 "average:  %llu",
#endif
                          average(t, tlen-1));  print_unit; printf("\n");
  printf("\n");
}


unsigned char mi[MLEN];
unsigned char mo[MLEN+CRYPTO_BYTES];
unsigned char sm[MLEN+CRYPTO_BYTES];
unsigned char pk[CRYPTO_PUBLICKEYBYTES];
unsigned char sk[CRYPTO_SECRETKEYBYTES];
unsigned long long smlen, mlen;

extern unsigned long long rejwctr;
extern unsigned long long rejyzctr;
extern unsigned long long ctr_keygen;
extern unsigned long long ctr_sign;


#ifdef DEBUG  

int print_accrates()
{
  int r;
  double rejw=.0, rejyz=.0, rejctr=.0, rejctrkg=.0;
  unsigned long long i, j;

  for (i=0; i<NTESTS; i++){
    crypto_sign_keypair(pk, sk);
    rejctrkg+=ctr_keygen;
  }

  // Print acceptance rate for keygen. The counter increased by PARAM_K for each try
  printf("Acceptance rate of Keygen : %.2f\n", (double)((PARAM_K+1)*NTESTS)/((double)rejctrkg)); fflush(stdout);
 
  for (i=0; i<NTESTS; i++)
  {
    randombytes(mi, MLEN);
    crypto_sign(sm, &smlen, mi, MLEN, sk);    
    rejctr+=ctr_sign;
    rejw+=rejwctr;
    rejyz+=rejyzctr;
  }
  
  printf("Acceptance rate of v\t  : %.2f\n",1/((rejw/NTESTS)+1));
  printf("Acceptance rate of z\t  : %.2f\n",1/((rejyz/(NTESTS+rejw))+1));
  printf("Acceptance rate of Signing: %.2f\n",(double)NTESTS/rejctr);
  printf("\n");
 
  return 0;
}


void test_functions()
{
  unsigned int i;
  unsigned long long cycles0[NRUNS];
  int nonce;
  poly t, a, s, e, y, v, z;
  unsigned char randomness[CRYPTO_RANDOMBYTES]; 
  unsigned char c[CRYPTO_C_BYTES], seed[2*CRYPTO_SEEDBYTES], randomness_extended[4*CRYPTO_SEEDBYTES];
  unsigned char hm[HM_BYTES];
  unsigned char sk[CRYPTO_SECRETKEYBYTES];
  uint32_t pos_list[PARAM_H];
  int16_t sign_list[PARAM_H], ss[PARAM_N], ee[PARAM_N]; 
  int32_t pk_t[PARAM_N];

  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    randombytes(randomness, CRYPTO_RANDOMBYTES);
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("randombytes: ", cycles0, NRUNS);

  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    SHAKE(randomness_extended, 4*CRYPTO_SEEDBYTES, randomness, CRYPTO_RANDOMBYTES);
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("SHAKE: ", cycles0, NRUNS);

  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    SHAKE(randomness_extended, HM_BYTES, mi, MLEN);
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("SHAKE: ", cycles0, NRUNS);

  nonce = 0;
  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    sample_gauss_poly(e, randomness, nonce++);     
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("GaussSampler: ", cycles0, NRUNS);

  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    poly_uniform(a, randomness);
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("GenA: ", cycles0, NRUNS);
  
  nonce = 0;
  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    sample_y(y, randomness, nonce++); 
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("ySampler: ", cycles0, NRUNS);
  
  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    hash_vm(c, v, hm);
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("H: ", cycles0, NRUNS);
  
  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    encode_c(pos_list, sign_list, c); 
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("Enc: ", cycles0, NRUNS);

  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    sparse_mul16(t, ss, pos_list, sign_list);
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("Sparse mul16: ", cycles0, NRUNS);

  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    sparse_mul32(t, pk_t, pos_list, sign_list);
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("Sparse mul32: ", cycles0, NRUNS);

  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    poly_mul(t, a, t);
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("Poly mul: ", cycles0, NRUNS);

  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    poly_add(t, a, t);
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("Poly add: ", cycles0, NRUNS);

  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    poly_add_correct(t, a, t);
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("Poly add with correction: ", cycles0, NRUNS);

  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    poly_sub_correct(t, a, t);
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("Poly sub with correction: ", cycles0, NRUNS);

  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    poly_sub_reduce(t, a, t);
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("Poly sub with reduction: ", cycles0, NRUNS);

  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    encode_sk(sk, s, e, seed);
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("Encode sk: ", cycles0, NRUNS);

  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    decode_sk(seed, ss, ee, sk);
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("Decode sk: ", cycles0, NRUNS);

  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    encode_pk(pk, t, seed);
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("Encode pk: ", cycles0, NRUNS);

  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    encode_sig(sm, c, z);
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("Encode sig: ", cycles0, NRUNS);
  
  randombytes(mi, MLEN);
  crypto_sign_keypair(pk, sk);
  crypto_sign(sm, &smlen, mi, MLEN, sk);

  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    decode_sig(c, z, sm); 
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("Decode sig: ", cycles0, NRUNS);

  for (i = 0; i < NRUNS; i++) {
    cycles0[i] = cpucycles();
    decode_pk(pk_t, seed, pk);
    cycles0[i] = cpucycles() - cycles0[i];
  }
  print_results("Decode pk: ", cycles0, NRUNS);
 
  printf("\n");
}

#endif

int main(void)
{
  unsigned int i, j;
  unsigned char r;
  unsigned long long cycles0[NRUNS], cycles1[NRUNS], cycles2[NRUNS];
  int valid, response;
    
  printf("\n");
  printf("===========================================================================================\n");
  printf("Testing signature scheme qTESLA, system %s, tests for %d iterations\n", CRYPTO_ALGNAME, NRUNS);
  printf("===========================================================================================\n");

  printf("\nCRYPTO_PUBLICKEY_BYTES: %d\n", CRYPTO_PUBLICKEYBYTES);
  printf("CRYPTO_SECRETKEY_BYTES: %d\n", (int)CRYPTO_SECRETKEYBYTES);
  printf("CRYPTO_SIGNATURE_BYTES: %d\n\n", CRYPTO_BYTES);

#ifdef DEBUG  
  print_accrates();
  test_functions();
#endif

  for (i = 0; i < NRUNS; i++) {
    randombytes(mi, MLEN);

    cycles0[i] = cpucycles();
    crypto_sign_keypair(pk, sk);
    cycles0[i] = cpucycles() - cycles0[i];

    cycles1[i] = cpucycles();
    crypto_sign(sm, &smlen, mi, MLEN, sk);
    cycles1[i] = cpucycles() - cycles1[i];

    cycles2[i] = cpucycles();
    valid = crypto_sign_open(mo, &mlen, sm, smlen, pk);
    cycles2[i] = cpucycles() - cycles2[i];
    
    if (valid != 0) {
      printf("Signature verification FAILED. \n");
      return -1;
    } else if (mlen != MLEN) {
      printf("crypto_sign_open returned BAD message length. \n");
      return -1;
    }

    for (j = 0; j < mlen; j++) {
      if (mi[j] != mo[j]) {
        printf ("crypto_sign_open returned BAD message value. \n");
        return -1;
      }
    }

    // Change something in the signature somewhere    
    randombytes(&r, 1);
    sm[r % (MLEN+CRYPTO_BYTES)] ^= 1;
    response = crypto_sign_open(mo, &mlen, sm, smlen, pk);
    if (response == 0) {
      printf("Corrupted signature VERIFIED. \n");
      return -1;
    }
  }
  printf("Signature tests PASSED... \n\n");

  print_results("qTESLA keygen: ", cycles0, NRUNS);
  print_results("qTESLA sign: ", cycles1, NRUNS);
  print_results("qTESLA verify: ", cycles2, NRUNS);

  return 0;
}
