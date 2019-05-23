#ifndef FIPS202X4_H
#define FIPS202X4_H

#include <stdint.h>
#include <immintrin.h>

typedef struct {
  __m256i s[25];
} keccak4x_state;

void kyber_shake128x4_absorb(keccak4x_state *state,
                             const unsigned char *seed,
                             uint16_t nonce0,
                             uint16_t nonce1,
                             uint16_t nonce2,
                             uint16_t nonce3);

void shake128x4_squeezeblocks(unsigned char *out0,
                              unsigned char *out1,
                              unsigned char *out2,
                              unsigned char *out3,
                              unsigned long long nblocks,
                              keccak4x_state *state);

void shake256x4_prf(unsigned char *out0,
                    unsigned char *out1,
                    unsigned char *out2,
                    unsigned char *out3,
                    unsigned long long outlen,
                    const unsigned char *key,
                    unsigned char nonce0,
                    unsigned char nonce1,
                    unsigned char nonce2,
                    unsigned char nonce3);

#endif
