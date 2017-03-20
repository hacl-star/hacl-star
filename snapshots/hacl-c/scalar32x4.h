#ifndef __Scalar32x4_H
#define __Scalar32x4_H

static const int vec_size = 4;

typedef struct {
  uint32_t x0;
  uint32_t x1;
  uint32_t x2;
  uint32_t x3;
} vec;

static inline vec vec_load_32x4(uint32_t x0, uint32_t x1, uint32_t x2, uint32_t x3){
  vec v = {.x0 = x0, .x1 = x1, .x2 = x2, .x3 = x3};
  return v;
}


static inline vec vec_load_32x8(uint32_t x0, uint32_t x1, uint32_t x2, uint32_t x3, uint32_t x4, uint32_t x5, uint32_t x6, uint32_t x7){
  vec v = {.x0 = x0, .x1 = x1, .x2 = x2, .x3 = x3};
  return v;
}



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
  int32_t xs[4];
  xs[0] = v.x0;
  xs[1] = v.x1;
  xs[2] = v.x2;
  xs[3] = v.x3;
  vec r;
  r.x3 = xs[(3+n)%4];
  r.x2 = xs[(2+n)%4];
  r.x1 = xs[(1+n)%4];
  r.x0 = xs[(n)%4];
  return r;
}


static inline vec vec_shuffle_left(vec x, unsigned int n) {
  return vec_shuffle_right(x,4-n);
}

static inline vec vec_load_le(const unsigned char* in) {
  vec r;
  r.x0 = load32_le(in);
  r.x1 = load32_le(in+4);
  r.x2 = load32_le(in+8);
  r.x3 = load32_le(in+12);
  return r;
}

static inline void vec_store_le(unsigned char* out, vec r) {
  store32_le(out,r.x0);
  store32_le(out+4,r.x1);
  store32_le(out+8,r.x2);
  store32_le(out+12,r.x3);
}


static inline vec vec_load128_le(const unsigned char* in) {
  return vec_load_le(in);
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

static const vec two_le = {.x0 = 2, .x1 = 0, .x2 = 0, .x3 = 0};
static const vec one_le = {.x0 = 1, .x1 = 0, .x2 = 0, .x3 = 0};
static const vec zero = {.x0 = 0, .x1 = 0, .x2 = 0, .x3 = 0};

static inline vec vec_choose_128(vec v1, vec v2, unsigned int first, unsigned int second) {
  return v1;
}

#endif
