/* WARNING: This file was copied from Specific/CurveParameters/X25519_C64/scalarmult.c.
 If you edit it here, changes will be erased the next time remake_curves.sh is run. */
// The synthesized parts are from fiat-crypto, copyright MIT 2017.
// The synthesis framework is released under the MIT license.
// The non-synthesized parts are from curve25519-donna by Adam Langley (Google):
/* Copyright 2008, Google Inc.
 * All rights reserved.
 *
 * Code released into the public domain.
 *
 * curve25519-donna: Curve25519 elliptic curve, public key function
 *
 * http://code.google.com/p/curve25519-donna/
 *
 * (modified by Andres Erbsen and Jason Gross)
 * Adam Langley <agl@imperialviolet.org>
 * Parts optimised by floodyberry
 * Derived from public domain C code by Daniel J. Bernstein <djb@cr.yp.to>
 *
 * More information about curve25519 can be found here
 *   http://cr.yp.to/ecdh.html
 *
 * djb's sample implementation of curve25519 is written in a special assembly
 * language called qhasm and uses the floating point registers.
 *
 * This is, almost, a clean room reimplementation from the curve25519 paper. It
 * uses many of the tricks described therein. Only the crecip function is taken
 * from the sample implementation.
 */

#include <string.h>
#include <stdint.h>

#include "femul.h"
#include "fesquare.h"
#include "ladderstep.h"

typedef unsigned int uint128_t __attribute__((mode(TI)));

#undef force_inline
#define force_inline __attribute__((always_inline))

typedef uint8_t u8;
typedef uint64_t limb;
typedef limb felem[5];

static void force_inline
fmul(felem output, const felem in2, const felem in) {
  uint64_t out[5];
  femul(out,
      in2[4], in2[3], in2[2], in2[1], in2[0],
      in[4], in[3], in[2], in[1], in[0]);
  output[4] = out[0];
  output[3] = out[1];
  output[2] = out[2];
  output[1] = out[3];
  output[0] = out[4];
}

static void force_inline
fsquare_times(felem output, const felem in, limb count) {
  uint64_t r0 = in[0];
  uint64_t r1 = in[1];
  uint64_t r2 = in[2];
  uint64_t r3 = in[3];
  uint64_t r4 = in[4];

  do {
    uint64_t out[5];
    fesquare(out, r4, r3, r2, r1, r0);
    r4 = out[0];
    r3 = out[1];
    r2 = out[2];
    r1 = out[3];
    r0 = out[4];
  } while(--count);

  output[0] = r0;
  output[1] = r1;
  output[2] = r2;
  output[3] = r3;
  output[4] = r4;
}

/* Take a little-endian, 32-byte number and expand it into polynomial form */
static void
fexpand(limb *output, const u8 *in) {
  output[0] = *((const uint64_t *)(in)) & 0x7ffffffffffff;
  output[1] = (*((const uint64_t *)(in+6)) >> 3) & 0x7ffffffffffff;
  output[2] = (*((const uint64_t *)(in+12)) >> 6) & 0x7ffffffffffff;
  output[3] = (*((const uint64_t *)(in+19)) >> 1) & 0x7ffffffffffff;
  output[4] = (*((const uint64_t *)(in+25)) >> 4) & 0x7ffffffffffff;
}

/* Take a fully reduced polynomial form number and contract it into a
 * little-endian, 32-byte array
 */
static void
fcontract(u8 *output, const felem input) {
  uint128_t t[5];

  t[0] = input[0];
  t[1] = input[1];
  t[2] = input[2];
  t[3] = input[3];
  t[4] = input[4];

  t[1] += t[0] >> 51; t[0] &= 0x7ffffffffffff;
  t[2] += t[1] >> 51; t[1] &= 0x7ffffffffffff;
  t[3] += t[2] >> 51; t[2] &= 0x7ffffffffffff;
  t[4] += t[3] >> 51; t[3] &= 0x7ffffffffffff;
  t[0] += 19 * (t[4] >> 51); t[4] &= 0x7ffffffffffff;

  t[1] += t[0] >> 51; t[0] &= 0x7ffffffffffff;
  t[2] += t[1] >> 51; t[1] &= 0x7ffffffffffff;
  t[3] += t[2] >> 51; t[2] &= 0x7ffffffffffff;
  t[4] += t[3] >> 51; t[3] &= 0x7ffffffffffff;
  t[0] += 19 * (t[4] >> 51); t[4] &= 0x7ffffffffffff;

  /* now t is between 0 and 2^255-1, properly carried. */
  /* case 1: between 0 and 2^255-20. case 2: between 2^255-19 and 2^255-1. */

  t[0] += 19;

  t[1] += t[0] >> 51; t[0] &= 0x7ffffffffffff;
  t[2] += t[1] >> 51; t[1] &= 0x7ffffffffffff;
  t[3] += t[2] >> 51; t[2] &= 0x7ffffffffffff;
  t[4] += t[3] >> 51; t[3] &= 0x7ffffffffffff;
  t[0] += 19 * (t[4] >> 51); t[4] &= 0x7ffffffffffff;

  /* now between 19 and 2^255-1 in both cases, and offset by 19. */

  t[0] += 0x8000000000000 - 19;
  t[1] += 0x8000000000000 - 1;
  t[2] += 0x8000000000000 - 1;
  t[3] += 0x8000000000000 - 1;
  t[4] += 0x8000000000000 - 1;

  /* now between 2^255 and 2^256-20, and offset by 2^255. */

  t[1] += t[0] >> 51; t[0] &= 0x7ffffffffffff;
  t[2] += t[1] >> 51; t[1] &= 0x7ffffffffffff;
  t[3] += t[2] >> 51; t[2] &= 0x7ffffffffffff;
  t[4] += t[3] >> 51; t[3] &= 0x7ffffffffffff;
  t[4] &= 0x7ffffffffffff;

  *((uint64_t *)(output)) = t[0] | (t[1] << 51);
  *((uint64_t *)(output+8)) = (t[1] >> 13) | (t[2] << 38);
  *((uint64_t *)(output+16)) = (t[2] >> 26) | (t[3] << 25);
  *((uint64_t *)(output+24)) = (t[3] >> 39) | (t[4] << 12);
}

/* Input: Q, Q', Q-Q'
 * Output: 2Q, Q+Q'
 */
static void
fmonty(limb *x2, limb *z2, /* output 2Q */
       limb *x3, limb *z3, /* output Q + Q' */
       limb *x, limb *z,   /* input Q */
       limb *xprime, limb *zprime, /* input Q' */
       const limb *qmqp /* input Q - Q' */) {
  uint64_t out[20];
  ladderstep(out, qmqp[4], qmqp[3], qmqp[2], qmqp[1], qmqp[0], x[4], x[3], x[2], x[1], x[0], z[4], z[3], z[2], z[1], z[0], xprime[4], xprime[3], xprime[2], xprime[1], xprime[0], zprime[4], zprime[3], zprime[2], zprime[1], zprime[0]);
  x2[4] = out[ 0];
  x2[3] = out[ 1];
  x2[2] = out[ 2];
  x2[1] = out[ 3];
  x2[0] = out[ 4];
  z2[4] = out[ 5];
  z2[3] = out[ 6];
  z2[2] = out[ 7];
  z2[1] = out[ 8];
  z2[0] = out[ 9];
  x3[4] = out[10];
  x3[3] = out[11];
  x3[2] = out[12];
  x3[1] = out[13];
  x3[0] = out[14];
  z3[4] = out[15];
  z3[3] = out[16];
  z3[2] = out[17];
  z3[1] = out[18];
  z3[0] = out[19];
}

// -----------------------------------------------------------------------------
// Maybe swap the contents of two limb arrays (@a and @b), each @len elements
// long. Perform the swap iff @swap is non-zero.
//
// This function performs the swap without leaking any side-channel
// information.
// -----------------------------------------------------------------------------
static void
swap_conditional(limb a[5], limb b[5], limb iswap) {
  unsigned i;
  const limb swap = -iswap;

  for (i = 0; i < 5; ++i) {
    const limb x = swap & (a[i] ^ b[i]);
    a[i] ^= x;
    b[i] ^= x;
  }
}

/* Calculates nQ where Q is the x-coordinate of a point on the curve
 *
 *   resultx/resultz: the x coordinate of the resulting curve point (short form)
 *   n: a little endian, 32-byte number
 *   q: a point of the curve (short form)
 */
static void
cmult(limb *resultx, limb *resultz, const u8 *n, const limb *q) {
  limb a[5] = {0}, b[5] = {1}, c[5] = {1}, d[5] = {0};
  limb *nqpqx = a, *nqpqz = b, *nqx = c, *nqz = d, *t;
  limb e[5] = {0}, f[5] = {1}, g[5] = {0}, h[5] = {1};
  limb *nqpqx2 = e, *nqpqz2 = f, *nqx2 = g, *nqz2 = h;

  unsigned i, j;

  memcpy(nqpqx, q, sizeof(limb) * 5);

  for (i = 0; i < 32; ++i) {
    u8 byte = n[31 - i];
    for (j = 0; j < 8; ++j) {
      const limb bit = byte >> 7;

      swap_conditional(nqx, nqpqx, bit);
      swap_conditional(nqz, nqpqz, bit);
      fmonty(nqx2, nqz2,
             nqpqx2, nqpqz2,
             nqx, nqz,
             nqpqx, nqpqz,
             q);
      swap_conditional(nqx2, nqpqx2, bit);
      swap_conditional(nqz2, nqpqz2, bit);

      t = nqx;
      nqx = nqx2;
      nqx2 = t;
      t = nqz;
      nqz = nqz2;
      nqz2 = t;
      t = nqpqx;
      nqpqx = nqpqx2;
      nqpqx2 = t;
      t = nqpqz;
      nqpqz = nqpqz2;
      nqpqz2 = t;

      byte <<= 1;
    }
  }

  memcpy(resultx, nqx, sizeof(limb) * 5);
  memcpy(resultz, nqz, sizeof(limb) * 5);
}


// -----------------------------------------------------------------------------
// Shamelessly copied from djb's code, tightened a little
// -----------------------------------------------------------------------------
static void
crecip(felem out, const felem z) {
  felem a,t0,b,c;

  /* 2 */ fsquare_times(a, z, 1); // a = 2
  /* 8 */ fsquare_times(t0, a, 2);
  /* 9 */ fmul(b, t0, z); // b = 9
  /* 11 */ fmul(a, b, a); // a = 11
  /* 22 */ fsquare_times(t0, a, 1);
  /* 2^5 - 2^0 = 31 */ fmul(b, t0, b);
  /* 2^10 - 2^5 */ fsquare_times(t0, b, 5);
  /* 2^10 - 2^0 */ fmul(b, t0, b);
  /* 2^20 - 2^10 */ fsquare_times(t0, b, 10);
  /* 2^20 - 2^0 */ fmul(c, t0, b);
  /* 2^40 - 2^20 */ fsquare_times(t0, c, 20);
  /* 2^40 - 2^0 */ fmul(t0, t0, c);
  /* 2^50 - 2^10 */ fsquare_times(t0, t0, 10);
  /* 2^50 - 2^0 */ fmul(b, t0, b);
  /* 2^100 - 2^50 */ fsquare_times(t0, b, 50);
  /* 2^100 - 2^0 */ fmul(c, t0, b);
  /* 2^200 - 2^100 */ fsquare_times(t0, c, 100);
  /* 2^200 - 2^0 */ fmul(t0, t0, c);
  /* 2^250 - 2^50 */ fsquare_times(t0, t0, 50);
  /* 2^250 - 2^0 */ fmul(t0, t0, b);
  /* 2^255 - 2^5 */ fsquare_times(t0, t0, 5);
  /* 2^255 - 21 */ fmul(out, t0, a);
}

int
crypto_scalarmult(u8 *mypublic, const u8 *secret, const u8 *basepoint) {
  limb bp[5], x[5], z[5], zmone[5];
  uint8_t e[32];
  int i;

  for (i = 0;i < 32;++i) e[i] = secret[i];
  e[0] &= 248;
  e[31] &= 127;
  e[31] |= 64;

  fexpand(bp, basepoint);
  cmult(x, z, e, bp);
  crecip(zmone, z);
  fmul(z, x, zmone);
  fcontract(mypublic, z);
  return 0;
}

void crypto_scalarmult_bench(unsigned char* buf) {
  crypto_scalarmult(buf, buf+32, buf+64);
}
