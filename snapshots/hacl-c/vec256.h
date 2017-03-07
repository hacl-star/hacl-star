#ifndef __Vec256_H
#define __Vec256_H

#include <immintrin.h>
#include "kremlib.h"
#define VEC256
static const int vec_size = 32;
typedef unsigned int vec256 __attribute__ ((vector_size (32)));

typedef struct {
  vec256 v;
} vec;

static inline vec vec_copy(vec v) {
  vec v1;
  v1.v = v.v;
  return v1;
}

/*
static inline vec vec_create(unsigned int c) {
  vec v;
  v.v = (vec256) {c,c,c,c,c,c,c,c};
  return v;
}
*/

static inline vec vec_rotate_left(vec v, unsigned int n) {
  vec r;
  r.v = (vec256)((v.v << n) ^ (v.v >> (32-n)));
  return r;
}

static inline vec vec_rotate_right(vec v, unsigned int n) {
  return (vec_rotate_left(v,32-n));
}

static inline vec vec_shuffle_right(vec v, unsigned int n) {
  vec r;
  r.v = (vec256) _mm256_shuffle_epi32((__m256i)v.v,_MM_SHUFFLE((3+n)%4,(2+n)%4,(1+n)%4,n%4));
  return r;
}

static inline vec vec_shuffle_left(vec x, unsigned int n) {
  vec_shuffle_right(x,4-n);
}

static inline vec vec_load(const unsigned char* in) {
  vec r;
  r.v = (vec256)_mm256_loadu_si256((__m256i*)(in));
  return r;
}

static inline void vec_store(unsigned char* out, vec v) {
  _mm256_storeu_si256((__m256i*)(out), (__m256i) v.v);
}

static inline vec vec256_choose_128(vec v1, vec v2, unsigned int first, unsigned int second) {
  vec r;
  unsigned char control = (second * 16) + first;
  r.v = (vec256)_mm256_permute2x128_si256((__m256i)v1.v, (__m256i)v2.v, control);
  return r;
}

static inline vec vec_add(vec v1, vec v2) {
  vec r;
  r.v = (vec256)v1.v + v2.v;
  return r;
}
//#define vec_add(v1,v2) (vec256)(v1).v + (v2).v

static inline vec vec_xor(vec v1, vec v2) {
  vec r;
  r.v = (vec256)v1.v ^ v2.v;
  return r;
}
//#define vec_xor(v1,v2) (vec256)(v1).v ^ (v2).v

static const vec256 ONE = {1,0,0,0,1,0,0,0};

static inline vec one_128_le() {
  vec r;
  r.v = ONE;
  return r;
}


#endif
