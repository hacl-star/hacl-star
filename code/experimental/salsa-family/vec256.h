#ifndef __Vec_H
#define __Vec_H

#include <immintrin.h>

#define VEC256
static const int vec_size = 8;

typedef unsigned int vec256 __attribute__ ((vector_size (32)));


typedef struct {
  vec256 v;
} vec;

typedef vec Spec_Chacha20_vec256_vec;

static inline vec mk_vec(vec256 v) {
  vec r;
  r.v = v;
  return r;
}

static inline vec vec_load_32x4(uint32_t x1, uint32_t x2, uint32_t x3, uint32_t x4){
  vec v;
  v.v = (vec256) _mm256_set_epi32(x4,x3,x2,x1,x4,x3,x2,x1);
  return v;
}

static inline vec vec_load_32(uint32_t x){
  vec v;
  v.v = (vec256) _mm256_set1_epi32(x);
  return v;
}


static inline vec vec_load_32x8(uint32_t x1, uint32_t x2, uint32_t x3, uint32_t x4, uint32_t x5, uint32_t x6, uint32_t x7, uint32_t x8){
  vec v;
  v.v = (vec256) _mm256_set_epi32(x8,x7,x6,x5,x4,x3,x2,x1);
  return v;
}



static inline vec vec_rotate_left_8(vec v) {
  vec r;
  __m256i x = _mm256_set_epi8(14, 13, 12, 15, 10, 9, 8, 11, 6, 5, 4, 7, 2, 1, 0, 3, 14, 13, 12, 15, 10, 9, 8, 11, 6, 5, 4, 7, 2, 1, 0, 3);
  r.v = (vec256)_mm256_shuffle_epi8((__m256i)v.v,x);				    
  return r;
}

static inline vec vec_rotate_left_16(vec v) {
  vec r;
  __m256i x = _mm256_set_epi8(13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2);
  r.v = (vec256)_mm256_shuffle_epi8((__m256i)v.v,x);				    
  return r;
}

static inline vec vec_rotate_left(vec v, unsigned int n) {
  if (n == 8) return vec_rotate_left_8(v);
  if (n == 16) return vec_rotate_left_16(v);
  vec r;
  r.v = (vec256)_mm256_xor_si256(_mm256_slli_epi32((__m256i)v.v,n),
				 _mm256_srli_epi32((__m256i)v.v,32-n));
  return r;
}

static inline vec vec_rotate_right(vec v, unsigned int n) {
  return (vec_rotate_left(v,32-n));
}

#if __clang__
#define vec_shuffle_right(x,n) \
  mk_vec((vec256) _mm256_shuffle_epi32((__m256i)x.v,_MM_SHUFFLE((3+n)%4,(2+n)%4,(1+n)%4,n%4)))
#else
static inline vec vec_shuffle_right(vec x, unsigned int n) {
  vec r;
  r.v = (vec256) _mm256_shuffle_epi32((__m256i)x.v,_MM_SHUFFLE((3+n)%4,(2+n)%4,(1+n)%4,n%4));
  return r;
}
#endif

#if __clang__
#define vec_shuffle_left(x,n) vec_shuffle_right(x,4-n)
#else
static inline vec vec_shuffle_left(vec x, unsigned int n) {
  return vec_shuffle_right(x,4-n);
}
#endif

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
  r.v = (vec256) _mm256_add_epi32((__m256i)v1.v,(__m256i)v2.v);
  return r;
}

static inline vec vec_xor(vec v1, vec v2) {
  vec r;
  r.v = (vec256) _mm256_xor_si256((__m256i)v1.v,(__m256i)v2.v);
  return r;
}

static const vec two_le = {.v = {2,0,0,0,2,0,0,0}};
static const vec one_le = {.v = {1,0,0,0,1,0,0,0}};
static const vec zero = {.v = {0,0,0,0,0,0,0}};
static const vec ones = {.v = {1,1,1,1,1,1,1,1}};
static const vec eights = {.v = {8,8,8,8,8,8,8,8}};

#if __clang__
#define vec_choose_128(v1,v2,first,second) \
  mk_vec((vec256)_mm256_permute2x128_si256((__m256i)v1.v, (__m256i)v2.v, (second*16)+first))
#else
static inline vec vec_choose_128(vec v1, vec v2, unsigned int first, unsigned int second) {
  vec r;
  unsigned char control = (second * 16) + first;
  r.v = (vec256)_mm256_permute2x128_si256((__m256i)v1.v, (__m256i)v2.v, control);
  return r;
}

static inline vec vec_interleave32_high(vec v1, vec v2) {
  vec r;
  r.v = (vec256)_mm256_unpackhi_epi32((__m256i)v1.v,(__m256i)v2.v);
  return r;
}

static inline vec vec_interleave32_low(vec v1, vec v2) {
  vec r;
  r.v = (vec256)_mm256_unpacklo_epi32((__m256i)v1.v,(__m256i)v2.v);
  return r;
}
static inline vec vec_interleave64_high(vec v1, vec v2) {
  vec r;
  r.v = (vec256)_mm256_unpackhi_epi64((__m256i)v1.v,(__m256i)v2.v);
  return r;
}

static inline vec vec_interleave64_low(vec v1, vec v2) {
  vec r;
  r.v = (vec256)_mm256_unpacklo_epi64((__m256i)v1.v,(__m256i)v2.v);
  return r;
}
#endif
#endif
