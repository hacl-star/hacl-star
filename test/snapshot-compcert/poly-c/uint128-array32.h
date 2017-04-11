#ifndef __U128_CC_H
#define __U128_CC_H

#include "kremlib.h"
#if defined(__GNUC__) || defined(__clang__)
#include "x86intrin.h"
#endif 
#define inline __attribute__((always_inline))
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
  uint32_t x0 = (uint32_t) x[0];
  uint32_t x1 = (uint32_t) (x[0]>>32);
  uint32_t x2 = (uint32_t) (x[1]);
  uint32_t x3 = (uint32_t) (x[1]>>32);
  uint32_t y0 = (uint32_t) y[0];
  uint32_t y1 = (uint32_t) (y[0]>>32);
  uint32_t y2 = (uint32_t) (y[1]);
  uint32_t y3 = (uint32_t) (y[1]>>32);
  uint32_t r0,r1,r2,r3;
  char c = 0;
  c = _addcarry_u32(c,x0,y0,&r0);
  c = _addcarry_u32(c,x1,y1,&r1);
  c = _addcarry_u32(c,x2,y2,&r2);
  c = _addcarry_u32(c,x3,y3,&r3);
  r[0] = (((uint64_t)r1) << 32) ^ r0;
  r[1] = (((uint64_t)r3) << 32) ^ r2;
  /*
  asm("addl %[x0], %[y0]; adcl %[x1], %[y1]; adcl %[x2], %[y2]; adcl %[x3], %[y3];":
       [y0] "r" (y0),
       [y1] "r" (y1),
       [y2] "r" (y2),
       [y3] "r" (y3),
       [x0] "r" (x0),
       [x1] "r" (x1),
       [x2] "r" (x2),
      [x3] "r" (x3));
  r[0] = (((uint64_t)y1) << 32) + y0;
  r[1] = (((uint64_t)y3) << 32) + y2;
  */
  

#else
  uint64_t x0 = x[0];
  r[0] = x0 + y[0];
  r[1] = x[1] + y[1] + CONSTANT_TIME_CARRY(r[0],x0);//(r[0] < x0);
#endif
}

static inline void uint128_add64(uint128_t r, uint128_t x, uint64_t y) {
#if defined(__GNUC__) || defined(__clang__)
  uint32_t x0 = (uint32_t) x[0];
  uint32_t x1 = (uint32_t) (x[0]>>32);
  uint32_t x2 = (uint32_t) (x[1]);
  uint32_t x3 = (uint32_t) (x[1]>>32);
  uint32_t y0 = (uint32_t) y;
  uint32_t y1 = (uint32_t) (y>>32);
  uint32_t r0,r1,r2,r3;
  char c = 0;
  c = _addcarry_u32(c,x0,y0,&r0);
  c = _addcarry_u32(c,x1,y1,&r1);
  c = _addcarry_u32(c,x2,0,&r2);
  c = _addcarry_u32(c,x3,0,&r3);
  r[0] = (((uint64_t)r1) << 32) ^ r0;
  r[1] = (((uint64_t)r3) << 32) ^ r2;

  /*
   asm("movl %[y0], %%eax; movl %[y1], %%ebx; xor %%ecx, %%ecx; xor %%edx, %%edx;"
       "addl %[x0], %%eax; adcl %[x1], %%ebx; adcl %[x2], %%ecx; adcl %[x3], %%edx;"
       "movl %%eax, %[r0]; movl %%ebx, %[r1]; movl %%ecx, %[r2]; movl %%edx, %[r3];":
       [r0] "=r" (r0),
       [r1] "=r" (r1),
       [r2] "=r" (r2),
       [r3] "=r" (r3):
       [x0] "r" (x0),
       [x1] "r" (x1),
       [x2] "r" (x2),
       [x3] "r" (x3),
       [y0] "r" (y0),
       [y1] "r" (y1):
       "eax","ebx", "ecx","edx");
  */
#else
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
#if defined(__GNUC__) || defined(__clang__)
  uint32_t x0 = (uint32_t) x[0];
  uint32_t x1 = (uint32_t) (x[0]>>32);
  uint32_t x2 = (uint32_t) (x[1]);
  uint32_t x3 = (uint32_t) (x[1]>>32);
  uint32_t y0 = (uint32_t) y[0];
  uint32_t y1 = (uint32_t) (y[0]>>32);
  uint32_t y2 = (uint32_t) (y[1]);
  uint32_t y3 = (uint32_t) (y[1]>>32);
  uint32_t r0,r1,r2,r3;
  char c = 0;
  c = _subborrow_u32(c,x0,y0,&r0);
  c = _subborrow_u32(c,x1,y1,&r1);
  c = _subborrow_u32(c,x2,y2,&r2);
  c = _subborrow_u32(c,x3,y3,&r3);
  r[0] = (((uint64_t)r1) << 32) + r0;
  r[1] = (((uint64_t)r3) << 32) + r2;

  /*
  asm("movl %[y0], %%eax; movl %[y1], %%ebx; movl %[y2], %%ecx; movl %[y3], %%edx;"
       "subl %[x0], %%eax; sbbl %[x1], %%ebx; sbbl %[x2], %%ecx; sbbl %[x3], %%edx;"
       "movl %%eax, %[r0]; movl %%ebx, %[r1]; movl %%ecx, %[r2]; movl %%edx, %[r3];":
       [r0] "=r" (r0),
       [r1] "=r" (r1),
       [r2] "=r" (r2),
       [r3] "=r" (r3):
       [x0] "r" (x0),
       [x1] "r" (x1),
       [x2] "r" (x2),
       [x3] "r" (x3),
       [y0] "r" (y0),
       [y1] "r" (y1),
       [y2] "r" (y2),
       [y3] "r" (y3):
       "eax","ebx", "ecx","edx");
  */
#else
  uint64_t x0 = x[0];
  r[0] = x0 - y[0];
  r[1] = x[1] - y[1] + CONSTANT_TIME_CARRY(x0,r[0]);
#endif
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
  uint64_t u1, v1, t, w3, k, w1, lo, hi;
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
  r[0] = lo;
  r[1] = hi;
  
  /*
  uint32_t x0 = (uint32_t) x;
  uint32_t x1 = (uint32_t) (x>>32);
  uint32_t y0 = (uint32_t) y;
  uint32_t y1 = (uint32_t) (y>>32);

  uint64_t x0y0 = x0 * y0;
  uint64_t x0y1 = x0 * y1;
  uint64_t x1y0 = x1 * y0;
  uint64_t x1y1 = x1 * y1;

  uint32_t r0,r1,r2,r3;
  r0 = (uint32_t) x0y0;
  uint32_t r1_0 = x0y0 >> 32;
  uint32_t r1_1 = x0y1;
  uint32_t r1_2 = x1y0;

  uint32_t r2_0 = x1y1; 
  uint32_t r2_1 = x0y1 >> 32;
  uint32_t r2_2 = x1y0 >> 32;

  r3 = x1y1 >> 32;

  char c1 = 0;
  char c2 = 0;
  c1 = _addcarry_u32(0,r1_0,r1_1,&r1);
  c2 = _addcarry_u32(0,r1,r1_2,&r1);
  c1 = _addcarry_u32(c1,r2_0,r2_1,&r2);
  c2 = _addcarry_u32(c2,r2,r2_2,&r2);
  c1 = _addcarry_u32(c1,r3,0,&r3);
  c2 = _addcarry_u32(c2,r3,0,&r3);

  r[0] = (((uint64_t)r1) << 32) + r0;
  r[1] = (((uint64_t)r3) << 32) + r2;

  */

}


#endif
