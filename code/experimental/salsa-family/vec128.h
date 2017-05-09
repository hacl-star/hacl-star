#ifndef __Vec_H
#define __Vec_H

#include <emmintrin.h>
#include <tmmintrin.h>

#define VEC128
#define vec_size 4
/* static const int vec_size = 4; */

typedef unsigned int vec128 __attribute__ ((vector_size (16)));

typedef struct {
  vec128 v;
} vec;

static inline vec mk_vec(vec128 v) {
  vec r;
  r.v = v;
  return r;
}


static inline vec vec_rotate_left_8(vec v) {
  vec r;
  __m128i x = _mm_set_epi8(14, 13, 12, 15, 10, 9, 8, 11, 6, 5, 4, 7, 2, 1, 0, 3);
  r.v = (vec128)_mm_shuffle_epi8((__m128i)v.v,x);				    
  return r;
}

static inline vec vec_rotate_left_16(vec v) {
  vec r;
  __m128i x = _mm_set_epi8(13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2);
  r.v = (vec128)_mm_shuffle_epi8((__m128i)v.v,x);				    
  return r;
}

static inline vec vec_rotate_left(vec v, unsigned int n) {
  if (n == 8) return vec_rotate_left_8(v);
  if (n == 16) return vec_rotate_left_16(v);
  vec r;
  r.v = (vec128)_mm_xor_si128(_mm_slli_epi32((__m128i)v.v,n),
				 _mm_srli_epi32((__m128i)v.v,32-n));
  return r;
}

static inline vec vec_rotate_right(vec v, unsigned int n) {
  return (vec_rotate_left(v,32-n));
}

#if __clang__
#define vec_shuffle_right(x,n) \
  mk_vec((vec128)_mm_shuffle_epi32((__m128i)x.v,_MM_SHUFFLE((3+n)%4,(2+n)%4,(1+n)%4,n%4)))
#else
static inline vec vec_shuffle_right(vec x, unsigned int n) {
  vec r;
  r.v = ((vec128)_mm_shuffle_epi32((__m128i)x.v,_MM_SHUFFLE((3+n)%4,(2+n)%4,(1+n)%4,n%4)));
  return r;
}
#endif

#if __clang__
#define vec_shuffle_left(x,n) vec_shuffle_right(x,4-n)
#else
static inline vec vec_shuffle_left(vec x, unsigned int n) {
  return (vec_shuffle_right(x,4-n));
}
#endif

static inline vec vec_load_32x4(uint32_t x1, uint32_t x2, uint32_t x3, uint32_t x4){
  vec v;
  v.v = (vec128) _mm_set_epi32(x4,x3,x2,x1);
  return v;
}


static inline vec vec_load_32x8(uint32_t x1, uint32_t x2, uint32_t x3, uint32_t x4, uint32_t x5, uint32_t x6, uint32_t x7, uint32_t x8){
  vec v;
  v.v = (vec128) _mm_set_epi32(x4,x3,x2,x1);
  return v;
}

static inline vec vec_load_le(const unsigned char* in) {
  vec r;
  r.v = (vec128)_mm_loadu_si128((__m128i*)(in));
  return r;
}

static inline vec vec_load128_le(const unsigned char* in) {
  return vec_load_le(in);
}

static inline void vec_store_le(unsigned char* out, vec v) {
  _mm_storeu_si128((__m128i*)(out), (__m128i) (v.v));
}


static inline vec vec_add(vec v1, vec v2) {
  vec r;
  r.v = (vec128) _mm_add_epi32((__m128i)v1.v,(__m128i)v2.v);
  return r;
}

static inline vec vec_xor(vec v1, vec v2) {
  vec r;
  r.v = (vec128) _mm_xor_si128((__m128i)v1.v,(__m128i)v2.v);
  return r;
}

static const vec two_le = {.v = {2,0,0,0}};
static const vec one_le = {.v = {1,0,0,0}};
static const vec zero = {.v = {0,0,0,0}};

#if __clang__
#define vec_choose_128(v1,v2,first,second) v1
#else
static inline vec vec_choose_128(vec v1, vec v2, unsigned int first, unsigned int second) {
  return v1; 
}
#endif

#endif
