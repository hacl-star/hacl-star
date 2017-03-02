#include "inttypes.h"

const unsigned int vec_size = 16;

typedef struct{
  unsigned int x0;
  unsigned int x1;
  unsigned int x2;
  unsigned int x3;
} vec;

static inline vec vec_rotate_left(vec v, unsigned int n) {
  vec r;
  r.x0 = (v.x0 << n) ^ (v.x0 >> (32-n));
  r.x1 = (v.x1 << n) ^ (v.x1 >> (32-n));
  r.x2 = (v.x2 << n) ^ (v.x2 >> (32-n));
  r.x3 = (v.x3 << n) ^ (v.x3 >> (32-n));
  return r;
}

static inline vec vec_rotate_right(vec v, unsigned int n) {
  return (vec_rotate_left(v,32-n));
}

static inline vec vec_shuffle_right(vec v, unsigned int n) {
  unsigned int t[4] = {v.x0,v.x1,v.x2,v.x3};
  vec r;
  r.x0 = t[(4-n)%4];
  r.x1 = t[(5-n)%4];
  r.x2 = t[(6-n)%4];
  r.x3 = t[(7-n)%4];
  return r;
}

static inline vec vec_shuffle_left(vec x, unsigned int n) {
  return vec_shuffle_right(x,4-n);
}

static inline vec vec_load(const unsigned char* in) {
  unsigned int* t = (unsigned int*) in;
  vec r;
  r.x0 = t[0];
  r.x1 = t[1];
  r.x2 = t[2];
  r.x3 = t[3];
  return r;
}

static inline void vec_store(unsigned char* out, vec v) {
  unsigned int* t = (unsigned int*) out;
  t[0] = v.x0;
  t[1] = v.x1;
  t[2] = v.x2;
  t[3] = v.x3;
}

static inline vec vec_add(vec v1, vec v2) {
  vec r;
  r.x0 = v1.x0 + v2.x0;
  r.x1 = v1.x1 + v2.x1;
  r.x2 = v1.x2 + v2.x2;
  r.x3 = v1.x3 + v2.x3;
  return r;
}

static inline vec vec_xor(vec v1, vec v2) {
  vec r;
  r.x0 = v1.x0 ^ v2.x0;
  r.x1 = v1.x1 ^ v2.x1;
  r.x2 = v1.x2 ^ v2.x2;
  r.x3 = v1.x3 ^ v2.x3;
  return r;
}

const vec ONE = {1,0,0,0};

static inline vec one_128_le() {
  return ONE;
}





  
