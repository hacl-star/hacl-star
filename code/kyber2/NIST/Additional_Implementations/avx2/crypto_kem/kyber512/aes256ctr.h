#ifndef AES256CTR_H
#define AES256CTR_H

#include <stdint.h>
#include <immintrin.h>

typedef struct {
  __m128i rkeys[16];
  __m128i n;
} aes256ctr_ctx;

void aes256ctr_init(aes256ctr_ctx *state,
                    const unsigned char *key,
                    uint16_t nonce);
void aes256ctr_select(aes256ctr_ctx *state, uint16_t nonce);
void aes256ctr_squeezeblocks(unsigned char *out,
                             unsigned long long nblocks,
                             aes256ctr_ctx *state);

void aes256ctr_prf(unsigned char *out,
                   unsigned long long outlen,
                   const unsigned char *seed,
                   unsigned char nonce);

#endif
