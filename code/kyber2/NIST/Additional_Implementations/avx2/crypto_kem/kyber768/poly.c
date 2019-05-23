#include <stdint.h>
#include <immintrin.h>
#include "params.h"
#include "poly.h"
#include "ntt.h"
#include "reduce.h"
#include "cbd.h"
#include "symmetric.h"

/*************************************************
* Name:        poly_compress
*
* Description: Compression and subsequent serialization of a polynomial
*
* Arguments:   - unsigned char *r: pointer to output byte array
*              - const poly *a:    pointer to input polynomial
**************************************************/
void poly_compress(unsigned char * restrict r, poly * restrict a)
{
  uint8_t t[8];
  int i,j,k=0;

  poly_csubq(a);

#if (KYBER_POLYCOMPRESSEDBYTES == 96)
  for(i=0;i<KYBER_N;i+=8)
  {
    for(j=0;j<8;j++)
      t[j] = ((((uint16_t)a->coeffs[i+j] << 3) + KYBER_Q/2) / KYBER_Q) & 7;

    r[k]   =  t[0]       | (t[1] << 3) | (t[2] << 6);
    r[k+1] = (t[2] >> 2) | (t[3] << 1) | (t[4] << 4) | (t[5] << 7);
    r[k+2] = (t[5] >> 1) | (t[6] << 2) | (t[7] << 5);
    k += 3;
  }
#elif (KYBER_POLYCOMPRESSEDBYTES == 128)
  for(i=0;i<KYBER_N;i+=8)
  {
    for(j=0;j<8;j++)
      t[j] = ((((uint16_t)a->coeffs[i+j] << 4) + KYBER_Q/2) / KYBER_Q) & 15;

    r[k]   = t[0] | (t[1] << 4);
    r[k+1] = t[2] | (t[3] << 4);
    r[k+2] = t[4] | (t[5] << 4);
    r[k+3] = t[6] | (t[7] << 4);
    k += 4;
  }
#elif (KYBER_POLYCOMPRESSEDBYTES == 160)
  for(i=0;i<KYBER_N;i+=8)
  {
    for(j=0;j<8;j++)
      t[j] = ((((uint32_t)a->coeffs[i+j] << 5) + KYBER_Q/2) / KYBER_Q) & 31;

    r[k]   =  t[0]       | (t[1] << 5);
    r[k+1] = (t[1] >> 3) | (t[2] << 2) | (t[3] << 7);
    r[k+2] = (t[3] >> 1) | (t[4] << 4);
    r[k+3] = (t[4] >> 4) | (t[5] << 1) | (t[6] << 6);
    r[k+4] = (t[6] >> 2) | (t[7] << 3);
    k += 5;
  }
#else
#error "KYBER_POLYCOMPRESSEDBYTES needs to be in {96, 128, 160}"
#endif
}

/*************************************************
* Name:        poly_decompress
*
* Description: De-serialization and subsequent decompression of a polynomial;
*              approximate inverse of poly_compress
*
* Arguments:   - poly *r:                pointer to output polynomial
*              - const unsigned char *a: pointer to input byte array
**************************************************/
void poly_decompress(poly * restrict r, const unsigned char * restrict a)
{
  int i;
#if (KYBER_POLYCOMPRESSEDBYTES == 96)
  for(i=0;i<KYBER_N;i+=8)
  {
    r->coeffs[i+0] =  (((a[0] & 7) * KYBER_Q) + 4) >> 3;
    r->coeffs[i+1] = ((((a[0] >> 3) & 7) * KYBER_Q) + 4) >> 3;
    r->coeffs[i+2] = ((((a[0] >> 6) | ((a[1] << 2) & 4)) * KYBER_Q) + 4) >> 3;
    r->coeffs[i+3] = ((((a[1] >> 1) & 7) * KYBER_Q) + 4) >> 3;
    r->coeffs[i+4] = ((((a[1] >> 4) & 7) * KYBER_Q) + 4) >> 3;
    r->coeffs[i+5] = ((((a[1] >> 7) | ((a[2] << 1) & 6)) * KYBER_Q) + 4) >> 3;
    r->coeffs[i+6] = ((((a[2] >> 2) & 7) * KYBER_Q) + 4) >> 3;
    r->coeffs[i+7] = ((((a[2] >> 5)) * KYBER_Q) + 4) >> 3;
    a += 3;
  }
#elif (KYBER_POLYCOMPRESSEDBYTES == 128)
  for(i=0;i<KYBER_N;i+=8)
  {
    r->coeffs[i+0] = (((a[0] & 15) * KYBER_Q) + 8) >> 4;
    r->coeffs[i+1] = (((a[0] >> 4) * KYBER_Q) + 8) >> 4;
    r->coeffs[i+2] = (((a[1] & 15) * KYBER_Q) + 8) >> 4;
    r->coeffs[i+3] = (((a[1] >> 4) * KYBER_Q) + 8) >> 4;
    r->coeffs[i+4] = (((a[2] & 15) * KYBER_Q) + 8) >> 4;
    r->coeffs[i+5] = (((a[2] >> 4) * KYBER_Q) + 8) >> 4;
    r->coeffs[i+6] = (((a[3] & 15) * KYBER_Q) + 8) >> 4;
    r->coeffs[i+7] = (((a[3] >> 4) * KYBER_Q) + 8) >> 4;
    a += 4;
  }
#elif (KYBER_POLYCOMPRESSEDBYTES == 160)
  for(i=0;i<KYBER_N;i+=8)
  {
    r->coeffs[i+0] =  (((a[0] & 31) * KYBER_Q) + 16) >> 5;
    r->coeffs[i+1] = ((((a[0] >> 5) | ((a[1] & 3) << 3)) * KYBER_Q) + 16) >> 5;
    r->coeffs[i+2] = ((((a[1] >> 2) & 31) * KYBER_Q) + 16) >> 5;
    r->coeffs[i+3] = ((((a[1] >> 7) | ((a[2] & 15) << 1)) * KYBER_Q) + 16) >> 5;
    r->coeffs[i+4] = ((((a[2] >> 4) | ((a[3] &  1) << 4)) * KYBER_Q) + 16) >> 5;
    r->coeffs[i+5] = ((((a[3] >> 1) & 31) * KYBER_Q) + 16) >> 5;
    r->coeffs[i+6] = ((((a[3] >> 6) | ((a[4] &  7) << 2)) * KYBER_Q) + 16) >> 5;
    r->coeffs[i+7] =  (((a[4] >> 3) * KYBER_Q) + 16) >> 5;
    a += 5;
  }
#else
#error "KYBER_POLYCOMPRESSEDBYTES needs to be in {96, 128, 160}"
#endif
}

/*************************************************
* Name:        poly_tobytes
*
* Description: Serialization of a polynomial
*
* Arguments:   - unsigned char *r: pointer to output byte array
*              - const poly *a:    pointer to input polynomial
**************************************************/
void poly_tobytes(unsigned char *r, poly *a)
{
  ntttobytes_avx(r, a->coeffs);
  ntttobytes_avx(r + 192, a->coeffs + 128);
}

/*************************************************
* Name:        poly_frombytes
*
* Description: De-serialization of a polynomial;
*              inverse of poly_tobytes
*
* Arguments:   - poly *r:                pointer to output polynomial
*              - const unsigned char *a: pointer to input byte array
**************************************************/
void poly_frombytes(poly *r, const unsigned char *a)
{
  nttfrombytes_avx(r->coeffs, a);
  nttfrombytes_avx(r->coeffs + 128, a + 192);
}

/*************************************************
* Name:        poly_getnoise
*
* Description: Sample a polynomial deterministically from a seed and a nonce,
*              with output polynomial close to centered binomial distribution
*              with parameter KYBER_ETA
*
* Arguments:   - poly *r:                   pointer to output polynomial
*              - const unsigned char *seed: pointer to input seed
*              - unsigned char nonce:       one-byte input nonce
**************************************************/
void poly_getnoise(poly *r, const unsigned char *seed, unsigned char nonce)
{
  unsigned char buf[KYBER_ETA*KYBER_N/4];

  prf(buf, KYBER_ETA*KYBER_N/4, seed, nonce);
  cbd(r, buf);
}

#ifndef KYBER_90S
// FIXME
void poly_getnoise4x(poly *r0,
                     poly *r1,
                     poly *r2,
                     poly *r3,
                     const unsigned char *seed,
                     unsigned char nonce0,
                     unsigned char nonce1,
                     unsigned char nonce2,
                     unsigned char nonce3)
{
  unsigned char buf[4][SHAKE256_RATE];

  shake256x4_prf(buf[0], buf[1], buf[2], buf[3], SHAKE256_RATE, seed, nonce0, nonce1, nonce2, nonce3);

  cbd(r0, buf[0]);
  cbd(r1, buf[1]);
  cbd(r2, buf[2]);
  cbd(r3, buf[3]);
}
#endif

/*************************************************
* Name:        poly_ntt
*
* Description: Computes negacyclic number-theoretic transform (NTT) of
*              a polynomial in place;
*              inputs assumed to be in normal order, output in bitreversed order
*
* Arguments:   - uint16_t *r: pointer to in/output polynomial
**************************************************/
void poly_ntt(poly *r)
{
  ntt_level0_avx(r->coeffs, zetas_exp);
  ntt_level0_avx(r->coeffs + 64, zetas_exp);
  ntt_levels1t6_avx(r->coeffs, zetas_exp + 4);
  ntt_levels1t6_avx(r->coeffs + 128, zetas_exp + 200);
}

/*************************************************
* Name:        poly_invntt
*
* Description: Computes inverse of negacyclic number-theoretic transform (NTT) of
*              a polynomial in place;
*              inputs assumed to be in bitreversed order, output in normal order
*
* Arguments:   - uint16_t *a: pointer to in/output polynomial
**************************************************/
void poly_invntt(poly *r)
{
  invntt_levels0t5_avx(r->coeffs, zetas_inv_exp);
  invntt_levels0t5_avx(r->coeffs + 128, zetas_inv_exp + 196);
  invntt_level6_avx(r->coeffs, zetas_inv_exp + 392);
}

// FIXME
void poly_nttunpack(poly *r)
{
  nttunpack_avx(r->coeffs);
  nttunpack_avx(r->coeffs + 128);
}

//XXX Add comment
void poly_basemul(poly *r, const poly *a, const poly *b)
{
  basemul_avx(r->coeffs,
              a->coeffs,
              b->coeffs,
              zetas_exp + 152);
  basemul_avx(r->coeffs + 64,
              a->coeffs + 64,
              b->coeffs + 64,
              zetas_exp + 184);
  basemul_avx(r->coeffs + 128,
              a->coeffs + 128,
              b->coeffs + 128,
              zetas_exp + 348);
  basemul_avx(r->coeffs + 192,
              a->coeffs + 192,
              b->coeffs + 192,
              zetas_exp + 380);
}

// FIXME
void poly_frommont(poly *r)
{
  frommont_avx(r->coeffs);
  frommont_avx(r->coeffs + 128);
}

// FIXME
void poly_reduce(poly *r)
{
  reduce_avx(r->coeffs);
  reduce_avx(r->coeffs + 128);
}

// FIXME
void poly_csubq(poly *r)
{
  csubq_avx(r->coeffs);
  csubq_avx(r->coeffs + 128);
}

/*************************************************
* Name:        poly_add
*
* Description: Add two polynomials
*
* Arguments: - poly *r:       pointer to output polynomial
*            - const poly *a: pointer to first input polynomial
*            - const poly *b: pointer to second input polynomial
**************************************************/
void poly_add(poly * restrict r, const poly * restrict a, const poly * restrict b)
{
  int i;
  __m256i vec0, vec1;

  for(i=0;i<KYBER_N;i+=16) {
    vec0 = _mm256_load_si256((__m256i *)&a->coeffs[i]);
    vec1 = _mm256_load_si256((__m256i *)&b->coeffs[i]);
    vec0 = _mm256_add_epi16(vec0, vec1);
    _mm256_store_si256((__m256i *)&r->coeffs[i], vec0);
  }
}

/*************************************************
* Name:        poly_sub
*
* Description: Subtract two polynomials
*
* Arguments: - poly *r:       pointer to output polynomial
*            - const poly *a: pointer to first input polynomial
*            - const poly *b: pointer to second input polynomial
**************************************************/
void poly_sub(poly * restrict r, const poly * restrict a, const poly * restrict b)
{
  int i;
  __m256i vec0, vec1;

  for(i=0;i<KYBER_N;i+=16) {
    vec0 = _mm256_load_si256((__m256i *)&a->coeffs[i]);
    vec1 = _mm256_load_si256((__m256i *)&b->coeffs[i]);
    vec0 = _mm256_sub_epi16(vec0, vec1);
    _mm256_store_si256((__m256i *)&r->coeffs[i], vec0);
  }
}

/*************************************************
* Name:        poly_frommsg
*
* Description: Convert 32-byte message to polynomial
*
* Arguments:   - poly *r:                  pointer to output polynomial
*              - const unsigned char *msg: pointer to input message
**************************************************/
void poly_frommsg(poly * restrict r, const unsigned char msg[KYBER_SYMBYTES])
{
  int i;
  __m128i tmp;
  __m256i a[4], d0, d1, d2, d3;
  const __m256i shift = _mm256_set_epi32(7, 6, 5, 4, 3, 2, 1, 0);
  const __m256i zeros = _mm256_setzero_si256();
  const __m256i ones = _mm256_set1_epi32(1);
  const __m256i hqs = _mm256_set1_epi32((KYBER_Q+1)/2);

  tmp = _mm_loadu_si128((__m128i *)msg);
  for(i = 0; i < 4; i++)
  {
    a[i] = _mm256_broadcastd_epi32(tmp);
    tmp = _mm_srli_si128(tmp, 4);
  }

  for(i = 0; i < 4; i++)
  {
    d0 = _mm256_srlv_epi32(a[i], shift);
    d1 = _mm256_srli_epi32(d0, 8);
    d2 = _mm256_srli_epi32(d0, 16);
    d3 = _mm256_srli_epi32(d0, 24);

    d0 = _mm256_and_si256(d0, ones);
    d1 = _mm256_and_si256(d1, ones);
    d2 = _mm256_and_si256(d2, ones);
    d3 = _mm256_and_si256(d3, ones);

    d0 = _mm256_sub_epi32(zeros, d0);
    d1 = _mm256_sub_epi32(zeros, d1);
    d2 = _mm256_sub_epi32(zeros, d2);
    d3 = _mm256_sub_epi32(zeros, d3);

    d0 = _mm256_and_si256(hqs, d0);
    d1 = _mm256_and_si256(hqs, d1);
    d2 = _mm256_and_si256(hqs, d2);
    d3 = _mm256_and_si256(hqs, d3);

    d0 = _mm256_packus_epi32(d0, d1);
    d2 = _mm256_packus_epi32(d2, d3);
    d0 = _mm256_permute4x64_epi64(d0, 0xD8);
    d2 = _mm256_permute4x64_epi64(d2, 0xD8);
    _mm256_store_si256((__m256i *)&r->coeffs[32*i+0], d0);
    _mm256_store_si256((__m256i *)&r->coeffs[32*i+16], d2);
  }

  tmp = _mm_loadu_si128((__m128i *)&msg[16]);
  for(i = 0; i < 4; i++)
  {
    a[i] = _mm256_broadcastd_epi32(tmp);
    tmp = _mm_srli_si128(tmp, 4);
  }

  for(i = 0; i < 4; i++)
  {
    d0 = _mm256_srlv_epi32(a[i], shift);
    d1 = _mm256_srli_epi32(d0, 8);
    d2 = _mm256_srli_epi32(d0, 16);
    d3 = _mm256_srli_epi32(d0, 24);

    d0 = _mm256_and_si256(d0, ones);
    d1 = _mm256_and_si256(d1, ones);
    d2 = _mm256_and_si256(d2, ones);
    d3 = _mm256_and_si256(d3, ones);

    d0 = _mm256_sub_epi32(zeros, d0);
    d1 = _mm256_sub_epi32(zeros, d1);
    d2 = _mm256_sub_epi32(zeros, d2);
    d3 = _mm256_sub_epi32(zeros, d3);

    d0 = _mm256_and_si256(hqs, d0);
    d1 = _mm256_and_si256(hqs, d1);
    d2 = _mm256_and_si256(hqs, d2);
    d3 = _mm256_and_si256(hqs, d3);

    d0 = _mm256_packus_epi32(d0, d1);
    d2 = _mm256_packus_epi32(d2, d3);
    d0 = _mm256_permute4x64_epi64(d0, 0xD8);
    d2 = _mm256_permute4x64_epi64(d2, 0xD8);
    _mm256_store_si256((__m256i *)&r->coeffs[128+32*i+0], d0);
    _mm256_store_si256((__m256i *)&r->coeffs[128+32*i+16], d2);
  }
}

/*************************************************
* Name:        poly_tomsg
*
* Description: Convert polynomial to 32-byte message
*
* Arguments:   - unsigned char *msg: pointer to output message
*              - const poly *a:      pointer to input polynomial
**************************************************/
void poly_tomsg(unsigned char msg[KYBER_SYMBYTES], poly * restrict a)
{
  int i, small;
  __m256i vec, tmp;
  const __m256i hqs = _mm256_set1_epi16((KYBER_Q - 1)/2);
  const __m256i hhqs = _mm256_set1_epi16((KYBER_Q - 5)/4);

  for(i = 0; i < KYBER_N/16; i++)
  {
    vec = _mm256_load_si256((__m256i *)&a->coeffs[16*i]);
    vec = _mm256_sub_epi16(hqs, vec);
    tmp = _mm256_srai_epi16(vec, 15);
    vec = _mm256_xor_si256(vec, tmp);
    vec = _mm256_sub_epi16(hhqs, vec);
    small = _mm256_movemask_epi8(vec);
    small = _pext_u32(small, 0xAAAAAAAA);
    small = ~small;
    msg[2*i+0] = small;
    msg[2*i+1] = small >> 8;
  }
}
