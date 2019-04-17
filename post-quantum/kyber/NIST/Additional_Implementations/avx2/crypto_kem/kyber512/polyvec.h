#ifndef POLYVEC_H
#define POLYVEC_H

#include "params.h"
#include "poly.h"

typedef struct{
  poly vec[KYBER_K];
} polyvec;

void polyvec_compress(unsigned char *r, const polyvec *a);
void polyvec_decompress(polyvec *r, const unsigned char *a);

void polyvec_tobytes(unsigned char *r, const polyvec *a);
void polyvec_frombytes(polyvec *r, const unsigned char *a);

void polyvec_ntt(polyvec *r);
void polyvec_invntt(polyvec *r);

void polyvec_pointwise_acc(poly *r, const polyvec *a, const polyvec *b);
void polyvec_pointwise_acc_k2(poly *r, const polyvec *a, const polyvec *b) asm("polyvec_pointwise_acc_k2");
void polyvec_pointwise_acc_k3(poly *r, const polyvec *a, const polyvec *b) asm("polyvec_pointwise_acc_k3");
void polyvec_pointwise_acc_k4(poly *r, const polyvec *a, const polyvec *b) asm("polyvec_pointwise_acc_k4");

void polyvec_add(polyvec *r, const polyvec *a, const polyvec *b);

#endif
