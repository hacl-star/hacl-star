#include <inttypes.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include "endianness.h"

typedef uint8_t* block_t;
typedef uint64_t* precomp_t;
typedef uint64_t* elem_t;

static inline uint64_t mask(const elem_t e, int i) {
  if (i < 64) {
    return - ((e[0] >> i) & 1);
  }
  else {
    return - ((e[1] >> (i-64)) & 1);;
  }
}

static inline uint64_t mask_old(const elem_t e, int i) {
  if (i < 64) {
    return (uint64_t) (((int64_t)(e[0] << (63 - i))) >> 63);
  }
  else {
    return (uint64_t) (((int64_t)(e[1] << (127 - i))) >> 63);
  }
}

static void prepare(precomp_t pre, const elem_t r) {
  uint64_t sh[2] = {0};
  sh[0] = r[0];
  sh[1] = r[1];
  for (int i = 0; i < 128; i++) {
    pre[2*i] = sh[0];
    pre[2*i+1] = sh[1];
    uint64_t m = -(sh[0] & 1);
    sh[0] = (sh[0] >> 1) | (sh[1] << 63);
    sh[1] = (sh[1] >> 1) ^ (m & 0xE100000000000000LL);
  }
}

static inline void fadd(elem_t e1, const elem_t e2) {
  e1[0] ^= e2[0];
  e1[1] ^= e2[1];
}

static inline void fmul(elem_t e, const precomp_t pre) {
  uint64_t tmp0 = 0;
  uint64_t tmp1 = 0;
  for (int i = 0; i < 64; i++) {
    uint64_t m = -( (e[1] >> (63-i)) & 1);
    tmp0 ^= (m & pre[2*i]);
    tmp1 ^= (m & pre[2*i+1]);
  }
  for (int i = 64; i < 128; i++) {
    uint64_t m = -( (e[0] >> (127-i)) & 1);
    tmp0 ^= (m & pre[2*i]);
    tmp1 ^= (m & pre[2*i+1]);
  }
  e[0] = tmp0;
  e[1] = tmp1;
}

static inline void encode(elem_t e, const block_t b) {
  e[1] = load64_be(b);
  e[0] = load64_be(b+8);
}

static inline void encode_last(elem_t e, const block_t b, int blen) {
  uint8_t block[16] = {0};
  memcpy(block,b,blen);
  e[1] = load64_be(block);
  e[0] = load64_be(block+8);
}

static inline void decode(block_t b, const elem_t e) {
  store64_be(b,e[1]);
  store64_be(b+8,e[0]);
}

static inline void update(elem_t acc, const block_t b, const precomp_t pre) {
  uint64_t tmp[2] = {0};
  encode(tmp,b);
  fadd(acc,tmp);
  fmul(acc,pre);
}

static inline void update_last(elem_t acc, const block_t b, int blen, const precomp_t pre) {
  uint64_t tmp[2];
  encode_last(tmp,b,blen);
  fadd(acc,tmp);
  fmul(acc,pre);
}

static inline void poly(elem_t acc, uint8_t* text, int tlen, const precomp_t pre) {
  acc[0] = 0;
  acc[1] = 0;
  int blocks = tlen / 16;
  for (int i = 0; i < blocks; i++) {
    update(acc,text + 16*i, pre);
  }
  if (tlen % 16 > 0) {
    update_last(acc,text + 16*blocks, tlen % 16, pre);
  }
}

void ghash(uint8_t* tag, uint8_t* text, int tlen, uint8_t* key) {
  uint64_t acc[2] = {0};
  uint64_t pre[256] = {0};
  encode(acc,key);
  prepare(pre,acc);
  poly(acc,text,tlen,pre);
  decode(tag,acc);
}
	  
