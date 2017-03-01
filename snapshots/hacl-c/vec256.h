#ifndef __Vec_H
#define __Vec_H
#include <immintrin.h>
#include "kremlib.h"
#define VEC256
const int vec_size = 32;
typedef unsigned int vec __attribute__ ((vector_size (32)));
#define ONE (vec){1,0,0,0,1,0,0,0}
#define RORV(x,n) (vec)_mm256_shuffle_epi32((__m256i)x,_MM_SHUFFLE((3+n)%4,(2+n)%4,(1+n)%4,n%4))

static inline vec vec256_set_128_low(vec v1, vec v2) {
  vec r1 = (vec)_mm256_permute2x128_si256((__m256i)v1, (__m256i)v2, 0x20);
  return r1;
}

static inline vec vec256_set_128_high(vec v1, vec v2) {
  vec r1 = (vec)_mm256_permute2x128_si256((__m256i)v1, (__m256i)v2, 0x31);
  return r1;
}

static inline vec vec_load(const unsigned char* in) {
  vec r = (vec)_mm256_loadu_si256((__m256i*)(in));
  return r;
}

static inline void vec_store(unsigned char* out, vec v) {
  _mm256_storeu_si256((__m256i*)(out), (__m256i) v);
}
#endif
