#ifndef __Vec_H
#define __Vec_H
#include <immintrin.h>
#include "kremlib.h"
#define VEC256
const int vec_size = 32;
typedef unsigned int vec __attribute__ ((vector_size (32)));

static inline vec vec_rotate_left(vec v, unsigned int n) {
  return ((vec)((v << n) ^ (v >> (32-n))));
}

static inline vec vec_shuffle_right(vec x, unsigned int n) {
  return ((vec)_mm256_shuffle_epi32((__m256i)x,_MM_SHUFFLE((3+n)%4,(2+n)%4,(1+n)%4,n%4)));
}

static inline vec vec_load(const unsigned char* in) {
  vec r = (vec)_mm256_loadu_si256((__m256i*)(in));
  return r;
}

static inline void vec_store(unsigned char* out, vec v) {
  _mm256_storeu_si256((__m256i*)(out), (__m256i) v);
}

static inline vec vec256_choose_128(vec v1, vec v2, unsigned int first, unsigned int second) {
  unsigned char control = (second * 16) + first;
  vec r1 = (vec)_mm256_permute2x128_si256((__m256i)v1, (__m256i)v2, control);
  return r1;
}

static inline vec vec_add(vec v1, vec v2) {
  return ((vec) v1 + v2);
}

static inline vec vec_xor(vec v1, vec v2) {
  return ((vec) v1 ^ v2);
}

#endif
