#ifndef SYMMETRIC_H
#define SYMMETRIC_H

#include "params.h"

#ifdef KYBER_90S

#include "aes256ctr.h"
#include "sha2.h"

#if (KYBER_SSBYTES != 32)
#error "90s variant of Kyber can only generate keys of length 256 bits"
#endif

#define hash_h(OUT, IN, INBYTES) sha256(OUT, IN, INBYTES)
#define hash_g(OUT, IN, INBYTES) sha512(OUT, IN, INBYTES)
#define xof_absorb(STATE, IN, X, Y) aes256xof_absorb(STATE, IN, X, Y)
#define xof_squeezeblocks(OUT, OUTBLOCKS, STATE) aes256xof_squeezeblocks(OUT, OUTBLOCKS, STATE)
#define prf(OUT, OUTBYTES, KEY, NONCE) aes256_prf(OUT, OUTBYTES, KEY, NONCE)
#define kdf(OUT, IN, INBYTES) sha256(OUT, IN, INBYTES)

#define XOF_BLOCKBYTES 64

typedef aes256xof_ctx xof_state;

#else

#include "fips202.h"

typedef struct {
  uint64_t s[25];
} keccak_state;

void kyber_shake128_absorb(keccak_state *s, const unsigned char *input, unsigned char x, unsigned char y);
void kyber_shake128_squeezeblocks(unsigned char *output, unsigned long long nblocks, keccak_state *s);
void shake256_prf(unsigned char *output, unsigned long long outlen, const unsigned char *key, const unsigned char nonce);

#define hash_h(OUT, IN, INBYTES) sha3_256(OUT, IN, INBYTES)
#define hash_g(OUT, IN, INBYTES) sha3_512(OUT, IN, INBYTES)
#define xof_absorb(STATE, IN, X, Y) kyber_shake128_absorb(STATE, IN, X, Y)
#define xof_squeezeblocks(OUT, OUTBLOCKS, STATE) kyber_shake128_squeezeblocks(OUT, OUTBLOCKS, STATE)
#define prf(OUT, OUTBYTES, KEY, NONCE) shake256_prf(OUT, OUTBYTES, KEY, NONCE)
#define kdf(OUT, IN, INBYTES) shake256(OUT, KYBER_SSBYTES, IN, INBYTES)

#define XOF_BLOCKBYTES 168

typedef keccak_state xof_state;

#endif /* KYBER_90S */

#endif /* SYMMETRIC_H */
