/* Deterministic randombytes by Daniel J. Bernstein */
/* taken from SUPERCOP (https://bench.cr.yp.to)     */

#include <math.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>

#include "indcpa.h"
#include "poly.h"
#include "polyvec.h"

void indcpa_keypair(polyvec *s, polyvec *t, unsigned char *rho, const unsigned char *coins);

void indcpa_enc(polyvec *u, poly *v,  /* output ciphertext */
               const unsigned char *m, /* 256-bit message */
               const polyvec *t, const unsigned char *rho, /* public key */
               const unsigned char *coins);

void indcpa_dec(unsigned char *m,
               const polyvec *u, const poly *v, /* ciphertext */
               const polyvec *s);



const unsigned char keypaircoins[32] = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31};
const unsigned char encryptcoins[32] = {32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63};

const unsigned char msg[32] = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32};


static void print_poly(const poly *x, const char *name)
{
  int i;
  printf("%s = (", name);
  for(i=0;i<KYBER_N-1;i++)
    printf("%u*x^%d +", x->coeffs[i] % KYBER_Q, i);
  printf("%u*x^%d)\n", x->coeffs[i] % KYBER_Q, i);
}

static void print_polyvec(const polyvec *x, const char *name)
{
  int i,k;
  for(k=0;k<KYBER_K;k++)
  {
    printf("%s[%d] = (", name, k);
    for(i=0;i<KYBER_N-1;i++)
      printf("%u*x^%d +", x->vec[k].coeffs[i] % KYBER_Q, i);
    printf("%u*x^%d)\n", x->vec[k].coeffs[i] % KYBER_Q, i);
  }
}


int main(void)
{
  polyvec s, t, u;
  poly v;
  unsigned char rho[32];
  unsigned char outmsg[32];
  int i;


  // Key-pair generation
  indcpa_keypair(&s, &t, rho, keypaircoins);

  printf("Result of keypair:\n");
  print_polyvec(&s, "s");
  print_polyvec(&t, "t");
  printf("rho = {");
  for(i=0;i<32;i++)
    printf("0x%02x ", rho[i]);
  printf("}\n");

  // Encapsulation
  indcpa_enc(&u, &v, msg, &t, rho, encryptcoins);

  printf("Result of encrypt:\n");
  print_polyvec(&u, "u");
  print_poly(&v, "v");

  // Decapsulation
  indcpa_dec(outmsg, &u, &v, &s);
  for(i=0;i<32;i++)
  {
    if(msg[i] != outmsg[i])
    {
      printf("ERROR: decryption failed %d, %u!\n", i, outmsg[i]);
      return -1;
    }
  }

  return 0;
}
