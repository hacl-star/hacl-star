/*
version 20110505
D. J. Bernstein
Public domain.
*/

#define ROUNDS 20
#include <arm_neon.h>
#include "crypto_core.h"

int crypto_core(
        unsigned char *out,
  const unsigned char *in,
  const unsigned char *k,
  const unsigned char *c
)
{
  int i;

  const uint32x4_t abab = {-1,0,-1,0};

  uint32x4_t k0k1k2k3 = (uint32x4_t) vld1q_u8((uint8_t *) k);
  uint32x4_t k4k5k6k7 = (uint32x4_t) vld1q_u8((uint8_t *) (k + 16));
  uint32x4_t c0c1c2c3 = (uint32x4_t) vld1q_u8((uint8_t *) c);
  uint32x4_t n0n1n2n3 = (uint32x4_t) vld1q_u8((uint8_t *) in);

  uint32x4_t n1n2n3n0 = vextq_u32(n0n1n2n3,n0n1n2n3,1);
  uint32x2_t n1n2 = vget_low_u32(n1n2n3n0);
  uint32x2_t n3n0 = vget_high_u32(n1n2n3n0);
  uint32x2_t k0k1 = vget_low_u32(k0k1k2k3);
  uint32x2_t k2k3 = vget_high_u32(k0k1k2k3);
  uint32x2_t k4k5 = vget_low_u32(k4k5k6k7);
  uint32x2_t k6k7 = vget_high_u32(k4k5k6k7);

  uint32x2_t n0k0 = vext_u32(n3n0,k0k1,1);
  uint32x2_t k0n0 = vext_u32(n0k0,n0k0,1);
  uint32x4_t k4k5k0n0 = vcombine_u32(k4k5,k0n0);

  uint32x2_t k1k6 = vext_u32(k0k1,k6k7,1);
  uint32x2_t k6k1 = vext_u32(k1k6,k1k6,1);
  uint32x4_t n1n2k6k1 = vcombine_u32(n1n2,k6k1);

  uint32x2_t k7n3 = vext_u32(k6k7,n3n0,1);
  uint32x2_t n3k7 = vext_u32(k7n3,k7n3,1);
  uint32x4_t k2k3n3k7 = vcombine_u32(k2k3,n3k7);

  uint32x4_t start0 = c0c1c2c3;
  uint32x4_t start1 = vextq_u32(k4k5k0n0,k4k5k0n0,1);
  uint32x4_t start2 = vextq_u32(n1n2k6k1,n1n2k6k1,1);
  uint32x4_t start3 = vextq_u32(k2k3n3k7,k2k3n3k7,1);

  uint32x4_t diag0 = start0;
  uint32x4_t diag1 = start1;
  uint32x4_t diag2 = start2;
  uint32x4_t diag3 = start3;

  uint32x4_t x0x5x10x15;
  uint32x4_t x12x1x6x11;
  uint32x4_t x8x13x2x7;
  uint32x4_t x4x9x14x3;

  uint32x4_t x0x1x10x11;
  uint32x4_t x12x13x6x7;
  uint32x4_t x8x9x2x3;
  uint32x4_t x4x5x14x15;

  uint32x4_t x0x1x2x3;
  uint32x4_t x4x5x6x7;
  uint32x4_t x8x9x10x11;
  uint32x4_t x12x13x14x15;

  uint32x4_t a0;
  uint32x4_t a1;
  uint32x4_t a2;
  uint32x4_t a3;

  for (i = ROUNDS;i > 0;i -= 2) {
    a0 = diag1 + diag0;
    diag3 ^= vsriq_n_u32(vshlq_n_u32(a0,7),a0,25);
    a1 = diag0 + diag3;
    diag2 ^= vsriq_n_u32(vshlq_n_u32(a1,9),a1,23);
    a2 = diag3 + diag2;
    diag1 ^= vsriq_n_u32(vshlq_n_u32(a2,13),a2,19);
    a3 = diag2 + diag1;
    diag0 ^= vsriq_n_u32(vshlq_n_u32(a3,18),a3,14);

    diag3 = vextq_u32(diag3,diag3,3);
    diag2 = vextq_u32(diag2,diag2,2);
    diag1 = vextq_u32(diag1,diag1,1);

    a0 = diag3 + diag0;
    diag1 ^= vsriq_n_u32(vshlq_n_u32(a0,7),a0,25);
    a1 = diag0 + diag1;
    diag2 ^= vsriq_n_u32(vshlq_n_u32(a1,9),a1,23);
    a2 = diag1 + diag2;
    diag3 ^= vsriq_n_u32(vshlq_n_u32(a2,13),a2,19);
    a3 = diag2 + diag3;
    diag0 ^= vsriq_n_u32(vshlq_n_u32(a3,18),a3,14);

    diag1 = vextq_u32(diag1,diag1,3);
    diag2 = vextq_u32(diag2,diag2,2);
    diag3 = vextq_u32(diag3,diag3,1);
  }

  x0x5x10x15 = diag0 + start0;
  x12x1x6x11 = diag1 + start1;
  x8x13x2x7 = diag2 + start2;
  x4x9x14x3 = diag3 + start3;

  x0x1x10x11 = vbslq_u32(abab,x0x5x10x15,x12x1x6x11);
  x12x13x6x7 = vbslq_u32(abab,x12x1x6x11,x8x13x2x7);
  x8x9x2x3 = vbslq_u32(abab,x8x13x2x7,x4x9x14x3);
  x4x5x14x15 = vbslq_u32(abab,x4x9x14x3,x0x5x10x15);

  x0x1x2x3 = vcombine_u32(vget_low_u32(x0x1x10x11),vget_high_u32(x8x9x2x3));
  x4x5x6x7 = vcombine_u32(vget_low_u32(x4x5x14x15),vget_high_u32(x12x13x6x7));
  x8x9x10x11 = vcombine_u32(vget_low_u32(x8x9x2x3),vget_high_u32(x0x1x10x11));
  x12x13x14x15 = vcombine_u32(vget_low_u32(x12x13x6x7),vget_high_u32(x4x5x14x15));

  vst1q_u8((uint8_t *) out,(uint8x16_t) x0x1x2x3);
  vst1q_u8(16 + (uint8_t *) out,(uint8x16_t) x4x5x6x7);
  vst1q_u8(32 + (uint8_t *) out,(uint8x16_t) x8x9x10x11);
  vst1q_u8(48 + (uint8_t *) out,(uint8x16_t) x12x13x14x15);

  return 0;
}
