#include <string.h>
#include "indcpa.h"
#include "poly.h"
#include "polyvec.h"
#include "randombytes.h"
#include "fips202.h"
#include "ntt.h"


#define gen_a(A,B)  gen_matrix(A,B,0)
#define gen_at(A,B) gen_matrix(A,B,1)

/*************************************************
* Name:        gen_matrix
* 
* Description: Deterministically generate matrix A (or the transpose of A)
*              from a seed. Entries of the matrix are polynomials that look
*              uniformly random. Performs rejection sampling on output of 
*              SHAKE-128
*
* Arguments:   - polyvec *a:                pointer to ouptput matrix A
*              - const unsigned char *seed: pointer to input seed
*              - int transposed:            boolean deciding whether A or A^T is generated
**************************************************/
void gen_matrix(polyvec *a, const unsigned char *seed, int transposed) // Not static for benchmarking
{
  unsigned int pos=0, ctr;
  uint16_t val;
  unsigned int nblocks;
  const unsigned int maxnblocks=4;
  uint8_t buf[SHAKE128_RATE*maxnblocks];
  int i,j;
  uint64_t state[25]; // SHAKE state
  unsigned char extseed[KYBER_SYMBYTES+2];

  for(i=0;i<KYBER_SYMBYTES;i++)
    extseed[i] = seed[i];


  for(i=0;i<KYBER_K;i++)
  {
    for(j=0;j<KYBER_K;j++)
    {
      ctr = pos = 0;
      nblocks = maxnblocks;
      if(transposed) 
      {
        extseed[KYBER_SYMBYTES]   = i;
        extseed[KYBER_SYMBYTES+1] = j;
      }
      else
      {
        extseed[KYBER_SYMBYTES]   = j;
        extseed[KYBER_SYMBYTES+1] = i;
      }
        
      shake128_absorb(state,extseed,KYBER_SYMBYTES+2);
      shake128_squeezeblocks(buf,nblocks,state);

      while(ctr < KYBER_N)
      {
        val = (buf[pos] | ((uint16_t) buf[pos+1] << 8)) & 0x1fff;
        if(val < KYBER_Q)
        {
            a[i].vec[j].coeffs[ctr++] = val;
        }
        pos += 2;

        if(pos > SHAKE128_RATE*nblocks-2)
        {
          nblocks = 1;
          shake128_squeezeblocks(buf,nblocks,state);
          pos = 0;
        }
      }
    }
  }
}



void indcpa_keypair(polyvec *s, polyvec *t, unsigned char *rho, const unsigned char *coins)
{
  polyvec a[KYBER_K], e;
  unsigned char buf[KYBER_SYMBYTES+KYBER_SYMBYTES];
  unsigned char *publicseed = buf;
  unsigned char *noiseseed = buf+KYBER_SYMBYTES;
  int i;
  unsigned char nonce=0;

//  randombytes(buf, KYBER_SYMBYTES);
  sha3_512(buf, coins, KYBER_SYMBYTES);

  gen_a(a, publicseed);

  for(i=0;i<KYBER_K;i++)
    poly_getnoise(s->vec+i,noiseseed,nonce++);

  polyvec_ntt(s);
  
  for(i=0;i<KYBER_K;i++)
    poly_getnoise(e.vec+i,noiseseed,nonce++);

  // matrix-vector multiplication
  for(i=0;i<KYBER_K;i++)
    polyvec_pointwise_acc(&t->vec[i],s,a+i);

  polyvec_invntt(t);
  polyvec_add(t,t,&e);

  for(i=0;i<KYBER_SYMBYTES;i++)
    rho[i] = publicseed[i];
}


void indcpa_enc(polyvec *u, poly *v,  /* output ciphertext */
               const unsigned char *m, /* 256-bit message */
               const polyvec *t, const unsigned char *rho, /* public key */
               const unsigned char *coins)
{
  polyvec sp, ep, tt, at[KYBER_K];
  poly k, epp;
  int i;
  unsigned char nonce=0;


  poly_frommsg(&k, m);

  tt = *t;
  polyvec_ntt(&tt);

  gen_at(at, rho);

  for(i=0;i<KYBER_K;i++)
    poly_getnoise(sp.vec+i,coins,nonce++);

  polyvec_ntt(&sp);

  for(i=0;i<KYBER_K;i++)
    poly_getnoise(ep.vec+i,coins,nonce++);

  // matrix-vector multiplication
  for(i=0;i<KYBER_K;i++)
    polyvec_pointwise_acc(&u->vec[i],&sp,at+i);

  polyvec_invntt(u);
  polyvec_add(u, u, &ep);
 
  polyvec_pointwise_acc(v, &tt, &sp);
  poly_invntt(v);

  poly_getnoise(&epp,coins,nonce++);

  poly_add(v, v, &epp);
  poly_add(v, v, &k);
}

void indcpa_dec(unsigned char *m,
               const polyvec *u, const poly *v, /* ciphertext */
               const polyvec *s)
{
  polyvec uu;
  poly mp;

  uu = *u;

  polyvec_ntt(&uu);

  polyvec_pointwise_acc(&mp,s,&uu);
  poly_invntt(&mp);

  poly_sub(&mp, &mp, v);

  poly_tomsg(m, &mp);
}
