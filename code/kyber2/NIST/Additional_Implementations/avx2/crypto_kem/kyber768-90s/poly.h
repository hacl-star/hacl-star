#ifndef POLY_H
#define POLY_H

#include <stdint.h>
#include "params.h"

/*
 * Elements of R_q = Z_q[X]/(X^n + 1). Represents polynomial
 * coeffs[0] + X*coeffs[1] + X^2*xoeffs[2] + ... + X^{n-1}*coeffs[n-1]
 */
typedef struct{
  int16_t __attribute__((aligned(32))) coeffs[KYBER_N];
} poly;

void poly_compress(unsigned char *r, poly *a);
void poly_decompress(poly *r, const unsigned char *a);

void poly_tobytes(unsigned char *r, poly *a);
void poly_frombytes(poly *r, const unsigned char *a);

void poly_frommsg(poly *r, const unsigned char msg[KYBER_SYMBYTES]);
void poly_tomsg(unsigned char msg[KYBER_SYMBYTES], poly *r);

void poly_getnoise(poly *r, const unsigned char *seed, unsigned char nonce);
#ifndef KYBER_90S
void poly_getnoise4x(poly *r0,
                     poly *r1,
                     poly *r2,
                     poly *r3,
                     const unsigned char *seed,
                     unsigned char nonce0,
                     unsigned char nonce1,
                     unsigned char nonce2,
                     unsigned char nonce3);
#endif


void poly_ntt(poly *r);
void poly_invntt(poly *r);
void poly_nttunpack(poly *r);
void poly_basemul(poly *r, const poly *a, const poly *b);
void poly_frommont(poly *r);

void poly_reduce(poly *r);
void poly_csubq(poly *r);

void poly_add(poly *r, const poly *a, const poly *b);
void poly_sub(poly *r, const poly *a, const poly *b);

#endif
