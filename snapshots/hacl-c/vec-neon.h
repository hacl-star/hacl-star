#ifndef __Vec_H
#define __Vec_H

#include <arm_neon.h>

#define VEC128
static const int vec_size = 4;

typedef uint32x4_t vec128

typedef struct {
  vec128 v;
} vec;

static inline vec mk_vec(vec128 v) {
  vec r;
  r.v = v;
  return r;
}


static inline vec vec_rotate_left(vec v, unsigned int n) {
  vec r;
  r.v = (vec128)vsriq_n_u32(vshlq_n_u32((uint32x4_t)x,n),(uint32x4_t)x,32-n);
  return r;
}

static inline vec vec_rotate_right(vec v, unsigned int n) {
  return (vec_rotate_left(v,32-n));
}

static inline vec vec_shuffle_right(vec x, unsigned int n) {
  vec r;
  r.v = (vec128)vextq_u32((uint32x4_t)x,(uint32x4_t)x,n);
  return r;
}
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
  r.v = (vec128) vld1q_u32(in);
  return r;
}

static inline vec vec_load128_le(const unsigned char* in) {
  return vec_load_le(in);
}

static inline void vec_store_le(unsigned char* out, vec v) {
  vst1q_u32(out,v.v);
}


static inline vec vec_add(vec v1, vec v2) {
  vec r;
  r.v = (vec128) vaddq_u32(v1.v,v2.v);
  return r;
}

static inline vec vec_xor(vec v1, vec v2) {
  vec r;
  r.v = (vec128) veorq_u32(v1.v,v2.v);
  return r;
}

static const vec two_le = {.v = {2,0,0,0}};
static const vec one_le = {.v = {1,0,0,0}};
static const vec zero = {.v = {0,0,0,0}};

static inline vec vec_choose_128(vec v1, vec v2, unsigned int first, unsigned int second) {
  return v1; 
}


#endif
