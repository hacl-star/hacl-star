#ifndef __Vec_H
#define __Vec_H

#include <emmintrin.h>

#define VEC128
static const int vec_size = 16;

typedef unsigned int vec128 __attribute__ ((vector_size (16)));

typedef struct {
  vec128 v;
} vec;

static inline vec vec_rotate_left(vec v, unsigned int n) {
  vec r;
  r.v = (vec128)((v.v << n) ^ (v.v >> (32-n)));
  return r;
}

static inline vec vec_rotate_right(vec v, unsigned int n) {
  return (vec_rotate_left(v,32-n));
}

static inline vec vec_shuffle_right(vec x, unsigned int n) {
  vec r;
  r.v = ((vec128)_mm_shuffle_epi32((__m128i)x.v,_MM_SHUFFLE((3+n)%4,(2+n)%4,(1+n)%4,n%4)));
  return r;
}

static inline vec vec_shuffle_left(vec x, unsigned int n) {
  return (vec_shuffle_right(x,4-n));
}

static inline vec vec_load(const unsigned char* in) {
  vec r;
  r.v = (vec128)_mm_loadu_si128((__m128i*)(in));
  return r;
}

static inline void vec_store(unsigned char* out, vec v) {
  _mm_storeu_si128((__m128i*)(out), (__m128i) (v.v));
}

static inline vec vec_add(vec v1, vec v2) {
  vec r;
  r.v = (vec128) v1.v + v2.v;
  return r;
}

static inline vec vec_xor(vec v1, vec v2) {
  vec r;
  r.v = (vec128)v1.v ^ v2.v;
  return r;
}

static const vec128 ONE = {1,0,0,0};

static inline vec one_128_le() {
  vec r;
  r.v = ONE;
  return r;
}


#endif
