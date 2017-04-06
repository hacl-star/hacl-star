#ifndef __U128_CC_H
#define __U128_CC_H

#include "kremlib.h"

typedef uint64_t uint128_t[2];

#define CONSTANT_TIME_CARRY(a, b)                                              \
  ((a ^ ((a ^ b) | ((a - b) ^ b))) >> (sizeof(a) * 8 - 1))

static inline void load128_64(uint128_t r, uint64_t x, uint64_t y) {
  r[0] = x;
  r[1] = y;
}

static inline void uint128_copy(uint128_t r, uint128_t x) {
  r[0] = x[0];
  r[1] = x[1];
}

static inline void load128_le(uint128_t r, uint8_t *b) {
  r[0] = load64_le(b);
  r[1] = load64_le(b + 8);
}

static inline void store128_le(uint8_t *b, uint128_t n) {
  store64_le(b, n[0]);
  store64_le(b + 8, n[1]);
}

static inline void load128_be(uint128_t r, uint8_t *b) {
  r[1] = load64_le(b);
  r[0] = load64_le(b + 8);
}

static inline void store128_be(uint8_t *b, uint128_t n) {
  store64_le(b, n[1]);
  store64_le(b + 8, n[0]);
}

static inline void uint128_add(uint128_t r, uint128_t x, uint128_t y) {
#if defined(__GNUC__) || defined(__clang__)
   asm("movq %[y0], %%rax; movq %[y1], %%rdx; addq %[x0], %%rax; adcq %[x1], %%rdx; movq %%rax, %[r0]; movq %%rdx, %[r1];":
       [r0] "=r" (r[0]),
       [r1] "=r" (r[1]):
       [x0] "r" (x[0]),
       [x1] "r" (x[1]),
       [y0] "r" (y[0]),
       [y1] "r" (y[1]):"rax","rdx");
#elif 0
   //defined(__COMPCERT__)
   asm("movq %[y0], %%rax; movq %[y1], %%rdx; addq %[x0], %%rax; adcq %[x1], %%rdx; movq %%rax, %[r];":
       [r] "=r" (r[0]):
       [x0] "r" (x[0]),
       [x1] "r" (x[1]),
       [y0] "r" (y[0]),
       [y1] "r" (y[1]):"rax","rdx");
   asm("movq %%rdx, %[r];": [r] "=r" (r[1]): );
#else
  uint64_t x0 = x[0];
  r[0] = x0 + y[0];
  r[1] = x[1] + y[1] + CONSTANT_TIME_CARRY(r[0],x0);
#endif
}

static inline void uint128_add64(uint128_t r, uint128_t x, uint64_t y) {
#if defined(__GNUC__) || defined(__clang__)
   asm("movq %[x0], %%rax; movq %[x1], %%rdx; addq %[y0], %%rax; adcq %[y1], %%rdx; movq %%rax, %[r0]; movq %%rdx, %[r1];":
       [r0] "=r" (r[0]),
       [r1] "=r" (r[1]):
       [x0] "r" (x[0]),
       [x1] "r" (x[1]),
       [y0] "r" (y),
       [y1] "i" (0): "rax","rdx");
#else
   //   uint128_t yy;
   //load128_64(yy,y,0);
   //uint128_add(r,x,yy);
   r[0] = x[0] + y;
   r[1] = x[1] + CONSTANT_TIME_CARRY(r[0],y);
#endif
}

static inline void uint128_add_mod(uint128_t r, uint128_t x, uint128_t y) {
  uint128_add(r, x, y);
}


static inline void uint128_split(uint128_t fst, uint128_t snd, uint128_t src, uint32_t idx) {
  if (idx < 64) {
    uint64_t m = (((uint64_t)1) << idx) - 1;
    uint64_t src0 = src[0];
    uint64_t src1 = src[1];
    snd[0] = src0 & m;
    snd[1] = 0;
    fst[0] = (src0 >> idx) ^ (src1 << (64-idx));
    fst[1] = src1 >> idx;
  } else if (idx < 128) {
    idx = idx-64;
    uint64_t m = (((uint64_t)1) << idx) - 1;
    uint64_t src0 = src[0];
    uint64_t src1 = src[1];
    snd[0] = src0;
    snd[1] = src1 & m;
    fst[0] = (src1 >> idx);
    fst[1] = 0;
  }
}

static inline void uint128_split_low(uint128_t snd, uint128_t src, uint32_t idx) {
  if (idx < 64) {
    uint64_t m = (((uint64_t)1) << idx) - 1;
    uint64_t src0 = src[0];
    snd[0] = src0 & m;
    snd[1] = 0;
  } else if (idx < 128) {
    idx = idx-64;
    uint64_t m = (((uint64_t)1) << idx) - 1;
    uint64_t src0 = src[0];
    uint64_t src1 = src[1];
    snd[0] = src0;
    snd[1] = src1 & m;
  }
}

static inline void uint128_split_high(uint128_t fst, uint128_t src, uint32_t idx) {
  if (idx < 64) {
    uint64_t src0 = src[0];
    uint64_t src1 = src[1];
    fst[0] = (src0 >> idx) ^ (src1 << (64-idx));
    fst[1] = src1 >> idx;
  } else if (idx < 128) {
    idx = idx-64;
    uint64_t src1 = src[1];
    fst[0] = (src1 >> idx);
    fst[1] = 0;
  }
}

static inline uint64_t uint128_split_low64(uint128_t src, uint32_t idx) {
  if (idx < 64) {
    uint64_t m = (((uint64_t)1) << idx) - 1;
    uint64_t src0 = src[0];
    return (src0 & m);
  } else if (idx < 128) {
    uint64_t src0 = src[0];
    return (src0);
  }
}

static inline uint64_t uint128_split_high64(uint128_t src, uint32_t idx) {
  if (idx < 64) {
    uint64_t src0 = src[0];
    uint64_t src1 = src[1];
    return ((src0 >> idx) ^ (src1 << (64-idx)));
  } else if (idx < 128) {
    idx = idx-64;
    uint64_t src1 = src[1];
    return (src1 >> idx);
  }
}

static inline void uint128_sub(uint128_t r, uint128_t x, uint128_t y) {
  uint64_t x0 = x[0];
  r[0] = x0 - y[0];
  r[1] = x[1] - y[1] - CONSTANT_TIME_CARRY(x0,r[0]);
}

static inline void uint128_sub_mod(uint128_t r, uint128_t x, uint128_t y) {
  uint128_sub(r,x, y);
}

static inline void uint128_logand(uint128_t r, uint128_t x, uint128_t y) {
  r[0] = x[0] & y[0];
  r[1] = x[1] & y[1];
}

static inline void uint128_logor(uint128_t r, uint128_t x, uint128_t y) {
  r[0] = x[0] | y[0];
  r[1] = x[1] | y[1];
}

static inline void uint128_logxor(uint128_t r, uint128_t x, uint128_t y) {
  r[0] = x[0] ^ y[0];
  r[1] = x[1] ^ y[1];
}

static inline void uint128_lognot(uint128_t r, uint128_t x) {
  r[0] = ~x[0];
  r[1] = ~x[1];
}

static inline void FStar_Int_Cast_uint64_to_uint128(uint128_t r, uint64_t x) {
  r[0] = x;
  r[1] = 0;
}

static inline uint64_t FStar_Int_Cast_uint128_to_uint64(uint128_t x) {
  return x[0];
}

static inline void uint128_mul_wide(uint128_t r, uint64_t x, uint64_t y) {
  uint64_t lo;
  uint64_t hi;
#if defined(__GNUC__) || defined(__clang__)
  unsigned __int128 z = ((unsigned __int128) x) * y;
  lo = (uint64_t) z;
  hi = (uint64_t) (z >> 64);
#elif defined(__COMPCERT__)
  lo = x * y; 
  asm("movq %[inp1], %%rax;"
      "mulq %[inp2];"
      "movq %%rdx, %[output];"
      : [output] "=r" (hi)
      : [inp1] "r" (x), [inp2] "r" (y)
      :"rax", "rdx");
#else
  uint64_t u1, v1, t, w3, k, w1;
  u1 = (x & 0xffffffff);
  v1 = (y & 0xffffffff);
  t = (u1 * v1);
  w3 = (t & 0xffffffff);
  k = (t >> 32);
  x >>= 32;
  t = (x * v1) + k;
  k = (t & 0xffffffff);
  w1 = (t >> 32);
  y >>= 32;
  t = (u1 * y) + k;
  k = (t >> 32);
  hi = (x * y) + w1 + k;
  lo = (t << 32) + w3;
#endif
  r[0] = lo;
  r[1] = hi;
}


static inline uint64_t uint128_mul_wide_64(uint64_t* lo, uint64_t x, uint64_t y) {
#if defined(__GNUC__) || defined(__clang__)
  uint64_t hi;
  unsigned __int128 z = ((unsigned __int128) x) * y;
  *lo = (uint64_t) z;
  hi = (uint64_t) (z >> 64);
  return hi;
#elif defined(__COMPCERT__)
  uint64_t hi;
   asm("movq %[inp1], %%rax;"
       "imulq %[inp2];"
       "movq %%rdx, %[output];"
      : [output] "=r" (hi)
      : [inp1] "r" (x), [inp2] "r" (y)
      :"rax", "rdx");
  *lo = x * y; 
  return hi;
#endif
}

#endif
