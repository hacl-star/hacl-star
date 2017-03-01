#ifndef __Vec_H
#define __Vec_H

#include <emmintrin.h>

#define VEC128
const int vec_size = 16;
typedef unsigned int vec __attribute__ ((vector_size (16)));
#define ONE (vec){1,0,0,0}
#define RORV(x,n) (vec)_mm_shuffle_epi32((__m128i)x,_MM_SHUFFLE((3+n)%4,(2+n)%4,(1+n)%4,n%4))

static inline vec vec_load(const unsigned char* in) {
  vec r = (vec)_mm_loadu_si128((__m128i*)(in));
  return r;
}

static inline void vec_store(unsigned char* out, vec v) {
  _mm_storeu_si128((__m128i*)(out), (__m128i) (v));
}

#endif
