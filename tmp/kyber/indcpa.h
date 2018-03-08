#ifndef INDCPA_H
#define INDCPA_H

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

#endif
