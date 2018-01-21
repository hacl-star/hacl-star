/* MIT License
 *
 * Copyright (c) 2016-2017 INRIA and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
#ifndef __Vec_H
#define __Vec_H

#if defined(__SSSE3__)

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
  mk_vec((vec128)_mm_shuffle_epi32((__m128i)(x).v,_MM_SHUFFLE((3+(n))%4,(2+(n))%4,(1+(n))%4,(n)%4)))
#else
#define vec_shuffle_right(x,n) \
  mk_vec((vec128)_mm_shuffle_epi32((__m128i)(x).v,_MM_SHUFFLE((3+(n))%4,(2+(n))%4,(1+(n))%4,(n)%4)))
#endif

#if __clang__
#define vec_shuffle_left(x,n) vec_shuffle_right((x),4-(n))
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

#elif defined(__ARM_NEON__) || defined(__ARM_NEON)
#include <arm_neon.h>

#define VEC128
#define vec_size 4

typedef uint32x4_t vec128;

typedef struct {
  vec128 v;
} vec;

static inline vec mk_vec(vec128 v) {
  vec r;
  r.v = v;
  return r;
}

static inline vec vec_xor(vec v1, vec v2) {
  vec r;
  r.v = (vec128) veorq_u32(v1.v,v2.v);
  return r;
}


#if 1
#define vec_rotate_left(v,n) \
  mk_vec((vec128)vsriq_n_u32(vshlq_n_u32((uint32x4_t)(v).v,(n)),(uint32x4_t)(v).v,32-(n)))
#else
static inline vec vec_rotate_left(vec v, unsigned int n) {
  vec r;
  r.v = (vec128)vsriq_n_u32(vshlq_n_u32((uint32x4_t)v.v,n),(uint32x4_t)v.v,32-n);
  return r;
}
#endif

static inline vec vec_rotate_right(vec v, unsigned int n) {
  return (vec_rotate_left(v,32-n));
}

#if 1
#define vec_shuffle_right(x,n) \
  mk_vec((vec128)vextq_u32((uint32x4_t)(x).v,(uint32x4_t)(x).v,(n)))
#else 
static inline vec vec_shuffle_right(vec x, unsigned int n) {
  vec r;
  r.v = (vec128)vextq_u32((uint32x4_t)x.v,(uint32x4_t)x.v,n);
  return r;
}
#endif

static inline vec vec_shuffle_left(vec x, unsigned int n) {
  return (vec_shuffle_right(x,4-n));
}

static inline vec vec_load_32x4(uint32_t x1, uint32_t x2, uint32_t x3, uint32_t x4){
  vec v;
  v.v = (vec128) {x4,x3,x2,x1};
  return v;
}


static inline vec vec_load_32(uint32_t x1) {
  vec v;
  v.v = (vec128) {x1,x1,x1,x1};
  return v;
}


static inline vec vec_load_32x8(uint32_t x1, uint32_t x2, uint32_t x3, uint32_t x4, uint32_t x5, uint32_t x6, uint32_t x7, uint32_t x8){
  vec v;
  v.v = (vec128) {x4,x3,x2,x1};
  return v;
}

static inline vec vec_load_le(const unsigned char* in) {
  vec r;
  r.v = (vec128) vld1q_u32((uint32_t*) in);
  return r;
}

static inline vec vec_load128_le(const unsigned char* in) {
  return vec_load_le(in);
}

static inline void vec_store_le(unsigned char* out, vec v) {
  vst1q_u32((uint32_t*)out,v.v);
}


static inline vec vec_add(vec v1, vec v2) {
  vec r;
  r.v = (vec128) vaddq_u32(v1.v,v2.v);
  return r;
}

static const vec two_le = {.v = {2,0,0,0}};
static const vec one_le = {.v = {1,0,0,0}};
static const vec zero = {.v = {0,0,0,0}};

static inline vec vec_choose_128(vec v1, vec v2, unsigned int first, unsigned int second) {
  return v1; 
}

static inline vec vec_interleave32_high(vec v1, vec v2) {
  vec r;
  uint32x2_t h0 = vget_high_u32(v1.v);
  uint32x2_t h1 = vget_high_u32(v2.v);
  r.v = (vec128) vcombine_u32(h0,h1);
  return r;
}

static inline vec vec_interleave32_low(vec v1, vec v2) {
  vec r;
  uint32x2_t h0 = vget_low_u32(v1.v);
  uint32x2_t h1 = vget_low_u32(v2.v);
  r.v = (vec128) vcombine_u32(h0,h1);
  return r;
}
static inline vec vec_interleave64_high(vec v1, vec v2) {
  vec r;
  uint64x1_t h0 = vget_high_u64((uint64x2_t)v1.v);
  uint64x1_t h1 = vget_high_u64((uint64x2_t)v2.v);
  r.v = (vec128) vcombine_u64(h0,h1);
  return r;
}

static inline vec vec_interleave64_low(vec v1, vec v2) {
  vec r;
  uint64x1_t h0 = vget_low_u64((uint64x2_t)v1.v);
  uint64x1_t h1 = vget_low_u64((uint64x2_t)v2.v);
  r.v = (vec128) vcombine_u64(h0,h1);
  return r;
}

#else
#error "SSSE3 or ARM_NEON needed"
#endif

#endif
