#ifndef __Vec_H
#define __Vec_H

#include <immintrin.h>

#define VEC256
static const int vec_size = 8;

typedef unsigned int vec256 __attribute__ ((vector_size (32)));

typedef struct {
  vec256 v;
} vec;

static inline vec vec_load_32x4(uint32_t x1, uint32_t x2, uint32_t x3, uint32_t x4){
  vec v;
  v.v = (vec256) {x1,x2,x3,x4,x1,x2,x3,x4};
  return v;
}


static inline vec vec_load_32x8(uint32_t x1, uint32_t x2, uint32_t x3, uint32_t x4, uint32_t x5, uint32_t x6, uint32_t x7, uint32_t x8){
  vec v;
  v.v = (vec256) {x1,x2,x3,x4,x5,x6,x7,x8};
  return v;
}


static inline vec vec_rotate_left(vec v, unsigned int n) {
  vec r;
  r.v = (vec256)((v.v << n) ^ (v.v >> (32-n)));
  return r;
}

static inline vec vec_rotate_right(vec v, unsigned int n) {
  return (vec_rotate_left(v,32-n));
}

static inline vec vec_shuffle_right(vec x, unsigned int n) {
  vec r;
  r.v = ((vec256)_mm256_shuffle_epi32((__m256i)x.v,_MM_SHUFFLE((3+n)%4,(2+n)%4,(1+n)%4,n%4)));
  return r;
}

static inline vec vec_shuffle_left(vec x, unsigned int n) {
  return (vec_shuffle_right(x,4-n));
}

static inline vec vec_load_le(const unsigned char* in) {
  vec r;
  r.v = (vec256) _mm256_loadu_si256((__m256i*)(in));
  return r;
}

static inline void vec_store_le(unsigned char* out, vec v) {
  _mm256_storeu_si256((__m256i*)(out), (__m256i) v.v);
}


static inline vec vec_load128_le(const unsigned char* in) {
  vec r;
  __m128i x = _mm_loadu_si128((__m128i*)(in));
  r.v = (vec256) _mm256_broadcastsi128_si256 (x);
  return r;
}


static inline vec vec_add(vec v1, vec v2) {
  vec r;
  r.v = (vec256) v1.v + v2.v;
  return r;
}

static inline vec vec_xor(vec v1, vec v2) {
  vec r;
  r.v = (vec256)v1.v ^ v2.v;
  return r;
}

static const vec two_le = {.v = {2,0,0,0,2,0,0,0}};
static const vec one_le = {.v = {1,0,0,0,1,0,0,0}};
static const vec zero = {.v = {0,0,0,0,0,0,0}};

static inline vec vec_choose_128(vec v1, vec v2, unsigned int first, unsigned int second) {
  vec r;
  unsigned char control = (second * 16) + first;
  r.v = (vec256)_mm256_permute2x128_si256((__m256i)v1.v, (__m256i)v2.v, control);
  return r;
}

#endif
