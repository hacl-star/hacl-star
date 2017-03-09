#ifndef __Vec_H
#define __Vec_H

#include <emmintrin.h>

#define VEC128
static const int vec_size = 4;

typedef unsigned int vec128 __attribute__ ((vector_size (16)));

typedef struct {
  vec128 v;
} vec;

static inline vec vec_load_32x4(uint32_t x1, uint32_t x2, uint32_t x3, uint32_t x4){
  vec v;
  v.v = (vec128) {x1,x2,x3,x4};
  return v;
}


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

static inline vec vec_load_le_old(const unsigned char* in) {
  vec r;
  __m128i x = (__m128i)_mm_loadu_si128((__m128i*)(in));
  r.v = (vec128)_mm_shuffle_epi32(x, _MM_SHUFFLE(0,1,2,3));
  return r;
}

static inline vec vec_load_le(const unsigned char* in) {
  vec r;
  r.v = (vec128) _mm_loadu_si128((__m128i*)(in));
  return r;
}

static inline void vec_store_le_old(unsigned char* out, vec v) {
  __m128i x = _mm_shuffle_epi32((__m128i)v.v, _MM_SHUFFLE(0,1,2,3));
  _mm_storeu_si128((__m128i*)(out), x);
}

static inline void vec_store_le(unsigned char* out, vec v) {
  _mm_storeu_si128((__m128i*)(out), (__m128i) v.v);
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

static const vec two_le = {.v = {2,0,0,0}};
static const vec one_le = {.v = {1,0,0,0}};
static const vec zero = {.v = {0,0,0,0}};

static inline vec vec_choose_128(vec v1, vec v2, unsigned int first, unsigned int second) {
  return v1;
}

#endif
