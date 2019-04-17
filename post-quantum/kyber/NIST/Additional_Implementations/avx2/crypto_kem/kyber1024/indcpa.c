#include <string.h>
#include "indcpa.h"
#include "poly.h"
#include "polyvec.h"
#include "rng.h"
#include "fips202.h"
#include "ntt.h"
#include "genmatrix.h"

static void pack_pk(unsigned char *r, const polyvec *pk, const unsigned char *seed)
{
  int i;
  polyvec_compress(r, pk);
  for(i=0;i<KYBER_SYMBYTES;i++)
    r[i+KYBER_POLYVECCOMPRESSEDBYTES] = seed[i];
}


static void unpack_pk(polyvec *pk, unsigned char *seed, const unsigned char *packedpk)
{
  int i;
  polyvec_decompress(pk, packedpk);

  for(i=0;i<KYBER_SYMBYTES;i++)
    seed[i] = packedpk[i+KYBER_POLYVECCOMPRESSEDBYTES];
}


static void pack_ciphertext(unsigned char *r, const polyvec *b, const poly *v)
{
  polyvec_compress(r, b);
  poly_compress(r+KYBER_POLYVECCOMPRESSEDBYTES, v);
}


static void unpack_ciphertext(polyvec *b, poly *v, const unsigned char *c)
{
  polyvec_decompress(b, c);
  poly_decompress(v, c+KYBER_POLYVECCOMPRESSEDBYTES);
}

static void pack_sk(unsigned char *r, const polyvec *sk)
{
  polyvec_tobytes(r, sk);
}

static void unpack_sk(polyvec *sk, const unsigned char *packedsk)
{
  polyvec_frombytes(sk, packedsk);
}





void indcpa_keypair(unsigned char *pk, 
                   unsigned char *sk)
{
  polyvec a[KYBER_K], e, pkpv, skpv;
  unsigned char buf[KYBER_SYMBYTES+KYBER_SYMBYTES];
  unsigned char *publicseed = buf;
  unsigned char *noiseseed = buf+KYBER_SYMBYTES;
  int i;

  randombytes(buf, KYBER_SYMBYTES);
  sha3_512(buf, buf, KYBER_SYMBYTES);

  genmatrix(a, publicseed, 0);

#if (KYBER_K == 2)
    poly_getnoise4x(skpv.vec+0,skpv.vec+1,e.vec+0,e.vec+1,noiseseed,0,1,2,3);
#elif (KYBER_K == 3)
    poly_getnoise4x(skpv.vec+0,skpv.vec+1,skpv.vec+2,e.vec+0,noiseseed,0,1,2,3);
    poly_getnoise(e.vec+1,noiseseed,4);
    poly_getnoise(e.vec+2,noiseseed,5);
#elif (KYBER_K == 4)
    poly_getnoise4x(skpv.vec+0,skpv.vec+1,skpv.vec+2,skpv.vec+3,noiseseed,0,1,2,3);
    poly_getnoise4x(e.vec+0,e.vec+1,e.vec+2,e.vec+3,noiseseed,4,5,6,7);
#else
  unsigned char nonce=0;
  for(i=0;i<KYBER_K;i++)
    poly_getnoise(skpv.vec+i,noiseseed,nonce++);
  for(i=0;i<KYBER_K;i++)
    poly_getnoise(e.vec+i,noiseseed,nonce++);
#endif

  polyvec_ntt(&skpv);
  
  // matrix-vector multiplication
  for(i=0;i<KYBER_K;i++)
    polyvec_pointwise_acc(&pkpv.vec[i],&skpv,a+i);

  polyvec_invntt(&pkpv);
  polyvec_add(&pkpv,&pkpv,&e);

  pack_sk(sk, &skpv);
  pack_pk(pk, &pkpv, publicseed);
}


void indcpa_enc(unsigned char *c,
               const unsigned char *m,
               const unsigned char *pk,
               const unsigned char *coins)
{
  polyvec sp, pkpv, ep, at[KYBER_K], bp;
  poly v, k, epp;
  unsigned char seed[KYBER_SYMBYTES];
  int i;


  unpack_pk(&pkpv, seed, pk);

  poly_frommsg(&k, m);

  polyvec_ntt(&pkpv);

  genmatrix(at, seed, 1);

#if (KYBER_K == 2)
    poly_getnoise4x(sp.vec+0,sp.vec+1,ep.vec+0,ep.vec+1,coins,0,1,2,3);
    poly_getnoise(&epp,coins,4);
#else
  unsigned char nonce=0;
  for(i=0;i<KYBER_K;i++)
    poly_getnoise(sp.vec+i,coins,nonce++);
  for(i=0;i<KYBER_K;i++)
    poly_getnoise(ep.vec+i,coins,nonce++);
  poly_getnoise(&epp,coins,nonce++);
#endif

  polyvec_ntt(&sp);

  // matrix-vector multiplication
  for(i=0;i<KYBER_K;i++)
    polyvec_pointwise_acc(&bp.vec[i],&sp,at+i);

  polyvec_invntt(&bp);
  polyvec_add(&bp, &bp, &ep);
 
  polyvec_pointwise_acc(&v, &pkpv, &sp);
  poly_invntt(&v);

  poly_add(&v, &v, &epp);
  poly_add(&v, &v, &k);

  pack_ciphertext(c, &bp, &v);
}


void indcpa_dec(unsigned char *m,
               const unsigned char *c,
               const unsigned char *sk)
{
  polyvec bp, skpv;
  poly v, mp;

  unpack_ciphertext(&bp, &v, c);
  unpack_sk(&skpv, sk);

  polyvec_ntt(&bp);

  polyvec_pointwise_acc(&mp,&skpv,&bp);
  poly_invntt(&mp);

  poly_sub(&mp, &mp, &v);

  poly_tomsg(m, &mp);
}
