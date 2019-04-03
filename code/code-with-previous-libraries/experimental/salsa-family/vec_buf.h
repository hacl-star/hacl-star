#ifndef __Scalar32x4_H
#define __Scalar32x4_H

#include "kremlib.h"

static const int vec_size = 4;

typedef struct {
  uint32_t v[4];
} vec;

static inline vec vec_load_32x4(uint32_t x0, uint32_t x1, uint32_t x2, uint32_t x3){
  vec v;
  for (int i = 0; i < vec_size; i = i + 4) {
    v.v[i] = x0;
    v.v[i+1] = x1;
    v.v[i+2] = x2;
    v.v[i+3] = x3;
  }
  return v;
}


static inline vec vec_load_32x8(uint32_t x0, uint32_t x1, uint32_t x2, uint32_t x3, uint32_t x4, uint32_t x5, uint32_t x6, uint32_t x7){
  vec v;
  if (vec_size < 8) return vec_load_32x4(x0,x1,x2,x3);
  else 
  for (int i = 0; i < vec_size; i = i + 8) {
    v.v[i] = x0;
    v.v[i+1] = x1;
    v.v[i+2] = x2;
    v.v[i+3] = x3;
    v.v[i+4] = x4;
    v.v[i+5] = x5;
    v.v[i+6] = x6;
    v.v[i+7] = x7;
  }
  return v;
}



static inline vec vec_rotate_left(vec v, unsigned int n) {
  vec r;
  for (int i = 0; i < vec_size; i++) 
    r.v[i] = (v.v[i] << n) ^ (v.v[i] >> (32-n));
  return r;
}

static inline vec vec_rotate_right(vec v, unsigned int n) {
  return (vec_rotate_left(v,32-n));
}

static inline vec vec_shuffle_right(vec v, unsigned int n) {
  vec r;
  for (int i = 0; i < vec_size; i = i +4) 
    for (int j = i; j < i + 4; j++) 
      r.v[j] = v.v[(j+n)%4];
  return r;
}


static inline vec vec_shuffle_left(vec x, unsigned int n) {
  return vec_shuffle_right(x,4-n);
}

static inline vec vec_load_le(const unsigned char* in) {
  vec r;
  for (int i = 0; i < vec_size; i++) 
    r.v[i] = load32_le(in+(4*i));
  return r;
}

static inline void vec_store_le(unsigned char* out, vec r) {
  for (int i = 0; i < vec_size; i++) 
    store32_le(out + (4*i), r.v[i]);
}


static inline vec vec_load128_le(const unsigned char* in) {
  return vec_load_le(in);
}


static inline vec vec_add(vec v1, vec v2) {
  vec r;
  for (int i = 0; i < vec_size; i++) 
    r.v[i] = v1.v[i] + v2.v[i];
  return r;
}

static inline vec vec_xor(vec v1, vec v2) {
  vec r;
  for (int i = 0; i < vec_size; i++) 
    r.v[i] = v1.v[i] ^ v2.v[i];
  return r;
}

static const vec two_le = {.v = {2,0,0,0}};
static const vec one_le = {.v = {1,0,0,0}};
static const vec zero = {.v = {0,0,0,0}};

static inline vec vec_choose_128(vec v1, vec v2, unsigned int first, unsigned int second) {
  return v1;
}

#endif
