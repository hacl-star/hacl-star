#include <inttypes.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include "endianness.h"

typedef uint8_t* block_t;
typedef unsigned __int128 uint128_t;
typedef __int128 int128_t;
typedef uint128_t* precomp_t;
typedef uint128_t elem_t;

static void prepare(precomp_t pre, const elem_t r) {
  uint128_t sh = r;
  uint128_t R = ((uint128_t)0xE100000000000000LL) << 64;
  for (int i = 0; i < 128; i++) {
    uint128_t m = -(sh & 1);
    pre[i] = sh;
    sh = (sh >> 1) ^ (m & R);
  }
}

static inline elem_t fadd(elem_t e1, const elem_t e2) {
  return e1 ^ e2;
}

static inline elem_t fmul_(elem_t b, const precomp_t pre) {
  uint128_t tmp = 0;
  int128_t sh = b;
  for (int i = 0; i < 128; i++) {
    uint128_t m = sh >> 127;
    tmp ^= (m & pre[i]);
    sh = sh << 1;
  }
  return tmp;
}

static inline elem_t fmul(elem_t b, const precomp_t pre) {
  uint128_t tmp = 0;
  uint64_t sh = b >> 64;
  for (int i = 0; i < 64; i++){
    uint128_t m = -((sh >> (63 - i)) & 1);
    tmp ^= ((m | m << 64) & pre[i]);
  }
  sh = b;
  for (int i = 64; i < 128; i++) {
    uint128_t m = -((sh >> (127 - i)) & 1);
    tmp ^= ((m | m << 64) & pre[i]);
  }
  return tmp;
}

static inline elem_t encode(const block_t b) {
  uint64_t b1 = load64_be(b);
  uint64_t b0 = load64_be(b+8);
  return ((((uint128_t)b1) << 64) ^ b0);
}

static inline elem_t encode_last(const block_t b, int blen) {
  uint8_t block[16] = {0};
  memcpy(block,b,blen);
  return encode(b);
}

static inline void decode(block_t b, const elem_t e) {
  uint64_t b1 = e >> 64;
  uint64_t b0 = e;
  store64_be(b,b1);
  store64_be(b+8,b0);
}

static inline elem_t update(elem_t acc, const block_t b, const precomp_t pre) {
  uint128_t tmp = encode(b);
  tmp = fadd(acc,tmp);
  tmp = fmul(tmp,pre);
  return tmp;
}

static inline elem_t update_last(elem_t acc, const block_t b, int blen, const precomp_t pre) {
  uint128_t tmp = encode_last(b,blen);
  tmp = fadd(acc,tmp);
  tmp = fmul(tmp,pre);
  return tmp;
}

static inline elem_t poly(uint8_t* text, int tlen, const precomp_t pre) {
  uint128_t acc = 0;
  int blocks = tlen / 16;
  for (int i = 0; i < blocks; i++) {
    acc = update(acc,text + 16*i, pre);
  }
  if (tlen % 16 > 0) {
    acc = update_last(acc,text + 16*blocks, tlen % 16, pre);
  }
  return acc;
}

void ghash(uint8_t* tag, uint8_t* text, int tlen, uint8_t* key) {
  uint128_t k = encode(key);
  uint64_t pre[256] = {0};
  prepare(pre,k);
  uint128_t acc = poly(text,tlen,pre);
  decode(tag,acc);
}
	  
