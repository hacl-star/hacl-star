#include <stdint.h>
#include "rng.h"
#include "indcpa.h"
#include "poly.h"
#include "polyvec.h"
#include "ntt.h"
#include "symmetric.h"
#include "rejsample.h"
#include "cbd.h"

/*************************************************
* Name:        pack_pk
*
* Description: Serialize the public key as concatenation of the
*              compressed and serialized vector of polynomials pk
*              and the public seed used to generate the matrix A.
*
* Arguments:   unsigned char *r:          pointer to the output serialized public key
*              const poly *pk:            pointer to the input public-key polynomial
*              const unsigned char *seed: pointer to the input public seed
**************************************************/
static void pack_pk(unsigned char *r, polyvec *pk, const unsigned char *seed)
{
  int i;
  polyvec_tobytes(r, pk);
  for(i=0;i<KYBER_SYMBYTES;i++)
    r[i+KYBER_POLYVECBYTES] = seed[i];
}

/*************************************************
* Name:        unpack_pk
*
* Description: De-serialize and decompress public key from a byte array;
*              approximate inverse of pack_pk
*
* Arguments:   - polyvec *pk:                   pointer to output public-key vector of polynomials
*              - unsigned char *seed:           pointer to output seed to generate matrix A
*              - const unsigned char *packedpk: pointer to input serialized public key
**************************************************/
static void unpack_pk(polyvec *pk, unsigned char *seed, const unsigned char *packedpk)
{
  int i;
  polyvec_frombytes(pk, packedpk);
  for(i=0;i<KYBER_SYMBYTES;i++)
    seed[i] = packedpk[i+KYBER_POLYVECBYTES];
}

/*************************************************
* Name:        pack_sk
*
* Description: Serialize the secret key
*
* Arguments:   - unsigned char *r:  pointer to output serialized secret key
*              - const polyvec *sk: pointer to input vector of polynomials (secret key)
**************************************************/
static void pack_sk(unsigned char *r, polyvec *sk)
{
  polyvec_tobytes(r, sk);
}

/*************************************************
* Name:        unpack_sk
*
* Description: De-serialize the secret key;
*              inverse of pack_sk
*
* Arguments:   - polyvec *sk:                   pointer to output vector of polynomials (secret key)
*              - const unsigned char *packedsk: pointer to input serialized secret key
**************************************************/
static void unpack_sk(polyvec *sk, const unsigned char *packedsk)
{
  polyvec_frombytes(sk, packedsk);
}

/*************************************************
* Name:        pack_ciphertext
*
* Description: Serialize the ciphertext as concatenation of the
*              compressed and serialized vector of polynomials b
*              and the compressed and serialized polynomial v
*
* Arguments:   unsigned char *r:          pointer to the output serialized ciphertext
*              const poly *pk:            pointer to the input vector of polynomials b
*              const unsigned char *seed: pointer to the input polynomial v
**************************************************/
static void pack_ciphertext(unsigned char *r, polyvec *b, poly *v)
{
  polyvec_compress(r, b);
  poly_compress(r+KYBER_POLYVECCOMPRESSEDBYTES, v);
}

/*************************************************
* Name:        unpack_ciphertext
*
* Description: De-serialize and decompress ciphertext from a byte array;
*              approximate inverse of pack_ciphertext
*
* Arguments:   - polyvec *b:             pointer to the output vector of polynomials b
*              - poly *v:                pointer to the output polynomial v
*              - const unsigned char *c: pointer to the input serialized ciphertext
**************************************************/
static void unpack_ciphertext(polyvec *b, poly *v, const unsigned char *c)
{
  polyvec_decompress(b, c);
  poly_decompress(v, c+KYBER_POLYVECCOMPRESSEDBYTES);
}

static unsigned int rej_uniform_ref(int16_t *r, unsigned int len, const unsigned char *buf, unsigned int buflen)
{
  unsigned int ctr, pos;
  uint16_t val;

  ctr = pos = 0;
  while(ctr < len && pos + 2 <= buflen)
  {
    val = buf[pos] | ((uint16_t)buf[pos+1] << 8);
    pos += 2;

    if(val < 19*KYBER_Q)
    {
      val -= ((uint32_t)val*20159 >> 26)*KYBER_Q; // Barrett reduction
      r[ctr++] = (int16_t)val;
    }
  }

  return ctr;
}

#define gen_a(A,B)  gen_matrix(A,B,0)
#define gen_at(A,B) gen_matrix(A,B,1)

/*************************************************
* Name:        gen_matrix
*
* Description: Deterministically generate matrix A (or the transpose of A)
*              from a seed. Entries of the matrix are polynomials that look
*              uniformly random. Performs rejection sampling on output of
*              a XOF
*
* Arguments:   - polyvec *a:                pointer to ouptput matrix A
*              - const unsigned char *seed: pointer to input seed
*              - int transposed:            boolean deciding whether A or A^T is generated
**************************************************/
#ifdef KYBER_90S
void gen_matrix(polyvec *a, const unsigned char *seed, int transposed)
{
  unsigned int i, j, ctr;
  const unsigned int maxnblocks=(530+XOF_BLOCKBYTES)/XOF_BLOCKBYTES; /* 530 is expected number of required bytes */
  unsigned char __attribute__((aligned(32))) buf[XOF_BLOCKBYTES*maxnblocks];
  aes256ctr_ctx state;

  aes256ctr_init(&state, seed, 0);

  for(i=0;i<KYBER_K;i++)
  {
    for(j=0;j<KYBER_K;j++)
    {
      if(transposed)
        aes256ctr_select(&state, (i << 8) + j);  // FIXME: Also in spec?
      else
        aes256ctr_select(&state, (j << 8) + i);

      aes256ctr_squeezeblocks(buf, maxnblocks, &state);
      ctr = rej_uniform(a[i].vec[j].coeffs, KYBER_N, buf, maxnblocks*XOF_BLOCKBYTES);

      while(ctr < KYBER_N)
      {
        aes256ctr_squeezeblocks(buf, 1, &state);
        ctr += rej_uniform_ref(a[i].vec[j].coeffs + ctr, KYBER_N - ctr, buf, XOF_BLOCKBYTES);
      }

      poly_nttunpack(&a[i].vec[j]);
    }
  }
}
#else
#if KYBER_K == 2
void gen_matrix(polyvec *a, const unsigned char *seed, int transposed)
{
  unsigned int ctr0, ctr1, ctr2, ctr3, bufbytes;
  const unsigned int maxnblocks=(530+XOF_BLOCKBYTES)/XOF_BLOCKBYTES; /* 530 is expected number of required bytes */
  unsigned char __attribute__((aligned(32))) buf[4][XOF_BLOCKBYTES*maxnblocks];
  keccak4x_state state;

  if(transposed)
    kyber_shake128x4_absorb(&state, seed, 0, 256, 1, 257);
  else
    kyber_shake128x4_absorb(&state, seed, 0, 1, 256, 257);

  shake128x4_squeezeblocks(buf[0], buf[1], buf[2], buf[3], maxnblocks, &state);
  bufbytes = maxnblocks*XOF_BLOCKBYTES;

  ctr0 = rej_uniform(a[0].vec[0].coeffs, KYBER_N, buf[0], bufbytes);
  ctr1 = rej_uniform(a[0].vec[1].coeffs, KYBER_N, buf[1], bufbytes);
  ctr2 = rej_uniform(a[1].vec[0].coeffs, KYBER_N, buf[2], bufbytes);
  ctr3 = rej_uniform(a[1].vec[1].coeffs, KYBER_N, buf[3], bufbytes);

  while(ctr0 < KYBER_N || ctr1 < KYBER_N || ctr2 < KYBER_N || ctr3 < KYBER_N)
  {
    shake128x4_squeezeblocks(buf[0], buf[1], buf[2], buf[3], 1, &state);
    bufbytes = XOF_BLOCKBYTES;

    ctr0 += rej_uniform_ref(a[0].vec[0].coeffs + ctr0, KYBER_N - ctr0, buf[0], bufbytes);
    ctr1 += rej_uniform_ref(a[0].vec[1].coeffs + ctr1, KYBER_N - ctr1, buf[1], bufbytes);
    ctr2 += rej_uniform_ref(a[1].vec[0].coeffs + ctr2, KYBER_N - ctr2, buf[2], bufbytes);
    ctr3 += rej_uniform_ref(a[1].vec[1].coeffs + ctr3, KYBER_N - ctr3, buf[3], bufbytes);
  }

  poly_nttunpack(&a[0].vec[0]);
  poly_nttunpack(&a[0].vec[1]);
  poly_nttunpack(&a[1].vec[0]);
  poly_nttunpack(&a[1].vec[1]);
}
#elif KYBER_K == 3
void gen_matrix(polyvec *a, const unsigned char *seed, int transposed)
{
  unsigned int ctr0, ctr1, ctr2, ctr3, bufbytes;
  const unsigned int maxnblocks=(530+XOF_BLOCKBYTES)/XOF_BLOCKBYTES; /* 530 is expected number of required bytes */
  unsigned char __attribute__((aligned(32))) buf[4][XOF_BLOCKBYTES*maxnblocks];
  keccak4x_state state;
  keccak_state state1x;

  if(transposed)
    kyber_shake128x4_absorb(&state, seed, 0, 256, 512, 1);
  else
    kyber_shake128x4_absorb(&state, seed, 0, 1, 2, 256);

  shake128x4_squeezeblocks(buf[0], buf[1], buf[2], buf[3], maxnblocks, &state);
  bufbytes = maxnblocks*XOF_BLOCKBYTES;

  ctr0 = rej_uniform(a[0].vec[0].coeffs, KYBER_N, buf[0], bufbytes);
  ctr1 = rej_uniform(a[0].vec[1].coeffs, KYBER_N, buf[1], bufbytes);
  ctr2 = rej_uniform(a[0].vec[2].coeffs, KYBER_N, buf[2], bufbytes);
  ctr3 = rej_uniform(a[1].vec[0].coeffs, KYBER_N, buf[3], bufbytes);

  while(ctr0 < KYBER_N || ctr1 < KYBER_N || ctr2 < KYBER_N || ctr3 < KYBER_N)
  {
    shake128x4_squeezeblocks(buf[0], buf[1], buf[2], buf[3], 1, &state);
    bufbytes = XOF_BLOCKBYTES;

    ctr0 += rej_uniform_ref(a[0].vec[0].coeffs + ctr0, KYBER_N - ctr0, buf[0], bufbytes);
    ctr1 += rej_uniform_ref(a[0].vec[1].coeffs + ctr1, KYBER_N - ctr1, buf[1], bufbytes);
    ctr2 += rej_uniform_ref(a[0].vec[2].coeffs + ctr2, KYBER_N - ctr2, buf[2], bufbytes);
    ctr3 += rej_uniform_ref(a[1].vec[0].coeffs + ctr3, KYBER_N - ctr3, buf[3], bufbytes);
  }

  poly_nttunpack(&a[0].vec[0]);
  poly_nttunpack(&a[0].vec[1]);
  poly_nttunpack(&a[0].vec[2]);
  poly_nttunpack(&a[1].vec[0]);

  if(transposed)
    kyber_shake128x4_absorb(&state, seed, 257, 513, 2, 258);
  else
    kyber_shake128x4_absorb(&state, seed, 257, 258, 512, 513);

  shake128x4_squeezeblocks(buf[0], buf[1], buf[2], buf[3], maxnblocks, &state);
  bufbytes = maxnblocks*XOF_BLOCKBYTES;

  ctr0 = rej_uniform(a[1].vec[1].coeffs, KYBER_N, buf[0], bufbytes);
  ctr1 = rej_uniform(a[1].vec[2].coeffs, KYBER_N, buf[1], bufbytes);
  ctr2 = rej_uniform(a[2].vec[0].coeffs, KYBER_N, buf[2], bufbytes);
  ctr3 = rej_uniform(a[2].vec[1].coeffs, KYBER_N, buf[3], bufbytes);

  while(ctr0 < KYBER_N || ctr1 < KYBER_N || ctr2 < KYBER_N || ctr3 < KYBER_N)
  {
    shake128x4_squeezeblocks(buf[0], buf[1], buf[2], buf[3], 1, &state);
    bufbytes = XOF_BLOCKBYTES;

    ctr0 += rej_uniform_ref(a[1].vec[1].coeffs + ctr0, KYBER_N - ctr0, buf[0], bufbytes);
    ctr1 += rej_uniform_ref(a[1].vec[2].coeffs + ctr1, KYBER_N - ctr1, buf[1], bufbytes);
    ctr2 += rej_uniform_ref(a[2].vec[0].coeffs + ctr2, KYBER_N - ctr2, buf[2], bufbytes);
    ctr3 += rej_uniform_ref(a[2].vec[1].coeffs + ctr3, KYBER_N - ctr3, buf[3], bufbytes);
  }

  poly_nttunpack(&a[1].vec[1]);
  poly_nttunpack(&a[1].vec[2]);
  poly_nttunpack(&a[2].vec[0]);
  poly_nttunpack(&a[2].vec[1]);

  if(transposed)
    kyber_shake128_absorb(&state1x, seed, 2, 2);
  else
    kyber_shake128_absorb(&state1x, seed, 2, 2);

  kyber_shake128_squeezeblocks(buf[0], maxnblocks, &state1x);
  bufbytes = maxnblocks*XOF_BLOCKBYTES;

  ctr0 = rej_uniform(a[2].vec[2].coeffs, KYBER_N, buf[0], bufbytes);

  while(ctr0 < KYBER_N)
  {
    kyber_shake128_squeezeblocks(buf[0], 1, &state1x);
    bufbytes = XOF_BLOCKBYTES;

    ctr0 += rej_uniform_ref(a[2].vec[2].coeffs + ctr0, KYBER_N - ctr0, buf[0], bufbytes);
  }

  poly_nttunpack(&a[2].vec[2]);
}
#elif KYBER_K == 4
void gen_matrix(polyvec *a, const unsigned char *seed, int transposed)
{
  unsigned int i, ctr0, ctr1, ctr2, ctr3, bufbytes;
  const unsigned int maxnblocks=(530+XOF_BLOCKBYTES)/XOF_BLOCKBYTES; /* 530 is expected number of required bytes */
  unsigned char __attribute__((aligned(32))) buf[4][XOF_BLOCKBYTES*maxnblocks];
  keccak4x_state state;

  for(i = 0; i < 4; i++)
  {
    if(transposed)
      kyber_shake128x4_absorb(&state, seed, i+0, i+256, i+512, i+768);
    else
      kyber_shake128x4_absorb(&state, seed, 256*i+0, 256*i+1, 256*i+2, 256*i+3);

    shake128x4_squeezeblocks(buf[0], buf[1], buf[2], buf[3], maxnblocks, &state);
    bufbytes = maxnblocks*XOF_BLOCKBYTES;

    ctr0 = rej_uniform(a[i].vec[0].coeffs, KYBER_N, buf[0], bufbytes);
    ctr1 = rej_uniform(a[i].vec[1].coeffs, KYBER_N, buf[1], bufbytes);
    ctr2 = rej_uniform(a[i].vec[2].coeffs, KYBER_N, buf[2], bufbytes);
    ctr3 = rej_uniform(a[i].vec[3].coeffs, KYBER_N, buf[3], bufbytes);

    while(ctr0 < KYBER_N || ctr1 < KYBER_N || ctr2 < KYBER_N || ctr3 < KYBER_N)
    {
      shake128x4_squeezeblocks(buf[0], buf[1], buf[2], buf[3], 1, &state);
      bufbytes = XOF_BLOCKBYTES;

      ctr0 += rej_uniform_ref(a[i].vec[0].coeffs + ctr0, KYBER_N - ctr0, buf[0], bufbytes);
      ctr1 += rej_uniform_ref(a[i].vec[1].coeffs + ctr1, KYBER_N - ctr1, buf[1], bufbytes);
      ctr2 += rej_uniform_ref(a[i].vec[2].coeffs + ctr2, KYBER_N - ctr2, buf[2], bufbytes);
      ctr3 += rej_uniform_ref(a[i].vec[3].coeffs + ctr3, KYBER_N - ctr3, buf[3], bufbytes);
    }

    poly_nttunpack(&a[i].vec[0]);
    poly_nttunpack(&a[i].vec[1]);
    poly_nttunpack(&a[i].vec[2]);
    poly_nttunpack(&a[i].vec[3]);
    }
}
#endif
#endif

/*************************************************
* Name:        indcpa_keypair
*
* Description: Generates public and private key for the CPA-secure
*              public-key encryption scheme underlying Kyber
*
* Arguments:   - unsigned char *pk: pointer to output public key (of length KYBER_INDCPA_PUBLICKEYBYTES bytes)
*              - unsigned char *sk: pointer to output private key (of length KYBER_INDCPA_SECRETKEYBYTES bytes)
**************************************************/
void indcpa_keypair(unsigned char *pk, unsigned char *sk)
{
  int i;
  polyvec a[KYBER_K], skpv, e, pkpv;
  unsigned char buf[2*KYBER_SYMBYTES];
  const unsigned char *publicseed = buf;
  const unsigned char *noiseseed = buf+KYBER_SYMBYTES;
  unsigned char nonce=0;

  randombytes(buf, KYBER_SYMBYTES);
  hash_g(buf, buf, KYBER_SYMBYTES);

  gen_a(a, publicseed);

#if KYBER_90S
  aes256ctr_ctx state;
  unsigned char coins[128];
  aes256ctr_init(&state, noiseseed, 0);
  for(i=0;i<KYBER_K;i++) {
    aes256ctr_select(&state, (uint16_t)nonce++ << 8);
    aes256ctr_squeezeblocks(coins, 1, &state);
    cbd(skpv.vec+i, coins);
  }
  for(i=0;i<KYBER_K;i++) {
    aes256ctr_select(&state, (uint16_t)nonce++ << 8);
    aes256ctr_squeezeblocks(coins, 1, &state);
    cbd(e.vec+i, coins);
  }
#else
#if KYBER_K == 2
  poly_getnoise4x(skpv.vec+0, skpv.vec+1, e.vec+0, e.vec+1, noiseseed, nonce+0, nonce+1, nonce+2, nonce+3);
  nonce += 4;
#elif KYBER_K == 3
  poly_getnoise4x(skpv.vec+0, skpv.vec+1, skpv.vec+2, e.vec+0, noiseseed, nonce+0, nonce+1, nonce+2, nonce+3);
  poly_getnoise4x(e.vec+1, e.vec+2, pkpv.vec+0, pkpv.vec+1, noiseseed, nonce+4, nonce+5, 0, 0);
  nonce += 6;
#elif KYBER_K == 4
  poly_getnoise4x(skpv.vec+0, skpv.vec+1, skpv.vec+2, skpv.vec+3, noiseseed, nonce+0, nonce+1, nonce+2, nonce+3);
  poly_getnoise4x(e.vec+0, e.vec+1, e.vec+2, e.vec+3, noiseseed, nonce+4, nonce+5, nonce+6, nonce+7);
  nonce += 8;
#endif
#endif

  polyvec_ntt(&skpv);
  polyvec_ntt(&e);

  // matrix-vector multiplication
  for(i=0;i<KYBER_K;i++) {
    polyvec_pointwise_acc(pkpv.vec+i, a+i, &skpv);
    poly_frommont(pkpv.vec+i);
  }

  polyvec_add(&pkpv, &pkpv, &e);
  polyvec_reduce(&pkpv);

  pack_sk(sk, &skpv);
  pack_pk(pk, &pkpv, publicseed);
}

/*************************************************
* Name:        indcpa_enc
*
* Description: Encryption function of the CPA-secure
*              public-key encryption scheme underlying Kyber.
*
* Arguments:   - unsigned char *c:          pointer to output ciphertext (of length KYBER_INDCPA_BYTES bytes)
*              - const unsigned char *m:    pointer to input message (of length KYBER_INDCPA_MSGBYTES bytes)
*              - const unsigned char *pk:   pointer to input public key (of length KYBER_INDCPA_PUBLICKEYBYTES bytes)
*              - const unsigned char *coin: pointer to input random coins used as seed (of length KYBER_SYMBYTES bytes)
*                                           to deterministically generate all randomness
**************************************************/
void indcpa_enc(unsigned char *c,
                const unsigned char *m,
                const unsigned char *pk,
                const unsigned char *coins)
{
  int i;
  polyvec at[KYBER_K], pkpv, sp, ep, bp;
  poly k, v, epp;
  unsigned char seed[KYBER_SYMBYTES];
  unsigned char nonce=0;

  unpack_pk(&pkpv, seed, pk);
  poly_frommsg(&k, m);
  gen_at(at, seed);

#if KYBER_90S
  aes256ctr_ctx state;
  unsigned char buf[128];
  aes256ctr_init(&state, coins, 0);
  for(i=0;i<KYBER_K;i++) {
    aes256ctr_select(&state, (uint16_t)nonce++ << 8);
    aes256ctr_squeezeblocks(buf, 1, &state);
    cbd(sp.vec+i, buf);
  }
  for(i=0;i<KYBER_K;i++) {
    aes256ctr_select(&state, (uint16_t)nonce++ << 8);
    aes256ctr_squeezeblocks(buf, 1, &state);
    cbd(ep.vec+i, buf);
  }
  aes256ctr_select(&state, (uint16_t)nonce++ << 8);
  aes256ctr_squeezeblocks(buf, 1, &state);
  cbd(&epp, buf);
#else
#if KYBER_K == 2
  poly_getnoise4x(sp.vec+0, sp.vec+1, ep.vec+0, ep.vec+1, coins, nonce+0, nonce+1, nonce+2, nonce+3);
  poly_getnoise(&epp, coins, nonce+4);
  nonce += 5;
#elif KYBER_K == 3
  poly_getnoise4x(sp.vec+0, sp.vec+1, sp.vec+2, ep.vec+0, coins, nonce+0, nonce+1, nonce+2, nonce+3);
  poly_getnoise4x(ep.vec+1, ep.vec+2, &epp, bp.vec+0, coins, nonce+4, nonce+5, nonce+6, 0);
  nonce += 7;
#elif KYBER_K == 4
  poly_getnoise4x(sp.vec+0, sp.vec+1, sp.vec+2, sp.vec+3, coins, nonce+0, nonce+1, nonce+2, nonce+3);
  poly_getnoise4x(ep.vec+0, ep.vec+1, ep.vec+2, ep.vec+3, coins, nonce+4, nonce+5, nonce+6, nonce+7);
  poly_getnoise(&epp, coins, nonce+8);
  nonce += 9;
#endif
#endif

  polyvec_ntt(&sp);

  // matrix-vector multiplication
  for(i=0;i<KYBER_K;i++)
    polyvec_pointwise_acc(bp.vec+i, at+i, &sp);

  polyvec_pointwise_acc(&v, &pkpv, &sp);

  polyvec_invntt(&bp);
  poly_invntt(&v);

  polyvec_add(&bp, &bp, &ep);
  poly_add(&v, &v, &epp);
  poly_add(&v, &v, &k);
  polyvec_reduce(&bp);
  poly_reduce(&v);

  pack_ciphertext(c, &bp, &v);
}

/*************************************************
* Name:        indcpa_dec
*
* Description: Decryption function of the CPA-secure
*              public-key encryption scheme underlying Kyber.
*
* Arguments:   - unsigned char *m:        pointer to output decrypted message (of length KYBER_INDCPA_MSGBYTES)
*              - const unsigned char *c:  pointer to input ciphertext (of length KYBER_INDCPA_BYTES)
*              - const unsigned char *sk: pointer to input secret key (of length KYBER_INDCPA_SECRETKEYBYTES)
**************************************************/
void indcpa_dec(unsigned char *m,
                const unsigned char *c,
                const unsigned char *sk)
{
  polyvec bp, skpv;
  poly v, mp;

  unpack_ciphertext(&bp, &v, c);
  unpack_sk(&skpv, sk);

  polyvec_ntt(&bp);
  polyvec_pointwise_acc(&mp, &skpv, &bp);
  poly_invntt(&mp);

  poly_sub(&mp, &v, &mp);
  poly_reduce(&mp);

  poly_tomsg(m, &mp);
}
