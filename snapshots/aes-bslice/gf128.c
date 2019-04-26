#include <inttypes.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include "endianness.h"

typedef uint8_t* block_t;
typedef uint64_t* precomp_t;
typedef uint64_t* elem_t;
typedef unsigned __int128 uint128_t;


static inline uint64_t mask(const elem_t e, int i) {
  if (i < 64) {
    return - ((e[0] >> i) & 1);
  }
  else {
    return - ((e[1] >> (i-64)) & 1);;
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

static inline void fmul_pre(elem_t e, const precomp_t pre) {
  uint64_t tmp0 = 0;
  uint64_t tmp1 = 0;
  //int64_t tmp = e[1];
  for (int i = 0; i < 64; i++) {
    uint64_t m = -( (e[1] >> (63-i)) & 1);
    //uint64_t m = tmp >> 63;
    //uint64_t m = ((int64_t)(e[1] << i)) >> 63;
    tmp0 ^= (m & pre[2*i]);
    tmp1 ^= (m & pre[2*i+1]);
    //tmp = tmp << 1;
  }
  //tmp = e[0];
  for (int i = 64; i < 128; i++) {
    uint64_t m = -( (e[0] >> (127-i)) & 1);
    //uint64_t m = tmp >> 63;
    //    uint64_t m = ((int64_t)(e[0] << (i - 64))) >> 63;
    tmp0 ^= (m & pre[2*i]);
    tmp1 ^= (m & pre[2*i+1]);
    //tmp = tmp << 1;
  }
  e[0] = tmp0;
  e[1] = tmp1;
}

static inline void fmul_reduce(elem_t e, const elem_t r) {
  uint64_t tmp0 = 0;
  uint64_t tmp1 = 0;
  
  uint64_t sh0 = r[0];
  uint64_t sh1 = r[1];  
  for (int i = 0; i < 64; i++) {
    uint64_t m = -( (e[1] >> (63-i)) & 1);
    tmp0 ^= (m & sh0);
    tmp1 ^= (m & sh1);
    uint64_t s = -(sh0 & 1);
    sh0 = (sh0 >> 1) | (sh1 << 63);
    sh1 = (sh1 >> 1) ^ (s & 0xE100000000000000LL);
  }
  for (int i = 64; i < 128; i++) {
    uint64_t m = -( (e[0] >> (127-i)) & 1);
    tmp0 ^= (m & sh0);
    tmp1 ^= (m & sh1);
    uint64_t s = -(sh0 & 1);
    sh0 = (sh0 >> 1) | (sh1 << 63);
    sh1 = (sh1 >> 1) ^ (s & 0xE100000000000000LL);
  }
  e[0] = tmp0;
  e[1] = tmp1;
}

static inline void bmul64(elem_t e, uint64_t a) {
  uint64_t sh0 = a;
  uint64_t sh1 = 0;
  uint64_t r0 = 0;
  uint64_t r1 = 0;
  for (int i = 0; i < 64; i++) {
    uint64_t m = -( (e[0] >> i) & 1);
    r0 ^= (m & sh0);
    r1 ^= (m & sh1);
    sh1 = (sh1 << 1) | (sh0 >> 63);
    sh0 = (sh0 << 1); 
   }
  e[0] = r0;
  e[1] = r1;
}

static inline void fmul_classic(elem_t e, const elem_t r) {
  uint64_t tmp0[2] = {0};
  uint64_t tmp1[2] = {0};
  uint64_t tmp2[2] = {0};
  uint64_t lo[2] = {0};
  uint64_t hi[2] = {0};

  lo[0] = r[0];
  tmp1[0] = r[1];
  tmp2[0] = r[0];
  hi[0] = r[1];
  bmul64(lo,e[0]);
  bmul64(tmp1,e[0]);
  bmul64(tmp2,e[1]);
  bmul64(hi,e[1]);

  lo[1] ^= tmp1[0] ^ tmp2[0];
  hi[0] ^= tmp1[1] ^ tmp2[1];

  hi[1] = hi[1] << 1 | hi[0] >> 63; 
  hi[0] = hi[0] << 1 | lo[1] >> 63; 
  lo[1] = lo[1] << 1 | lo[0] >> 63; 
  lo[0] = lo[0] << 1; 
 
  tmp0[1] = lo[1] << 63;
  tmp0[0] = lo[0] << 63;
  tmp1[1] = lo[1] << 62;
  tmp1[0] = lo[0] << 62;
  tmp2[1] = lo[1] << 57;
  tmp2[0] = lo[0] << 57;

  tmp0[1] ^= tmp1[1];
  tmp0[1] ^= tmp2[1];
  tmp0[0] ^= tmp1[0];
  tmp0[0] ^= tmp2[0];

  uint64_t tmp8 = tmp0[1];
  lo[1]  ^= tmp0[0];
  
  tmp0[1] = lo[1] >> 1;
  tmp0[0] = lo[0] >> 1;
  tmp1[1] = lo[1] >> 2;
  tmp1[0] = lo[0] >> 2;
  tmp2[1] = lo[1] >> 7;
  tmp2[0] = lo[0] >> 7;
  tmp0[1] ^= tmp1[1];
  tmp0[0] ^= tmp1[0];
  tmp0[1] ^= tmp2[1];
  tmp0[0] ^= tmp2[0];
  tmp0[0] ^= tmp8;
  lo[1] ^= tmp0[1];
  lo[0] ^= tmp0[0];

  e[1] = lo[1] ^ hi[1];
  e[0] = lo[0] ^ hi[0];

}

static inline uint128_t bmul64_u128(uint64_t a, uint64_t b) {
  uint128_t sh = a;
  uint128_t r = 0;
  for (int i = 0; i < 64; i++) {
    uint128_t m = - ((uint128_t)( (b >> i) & 1));
    r ^= (m & sh);
    sh = sh << 1;
  }
  return r;
}

static inline void fmul_u128(elem_t e, const elem_t r) {
  uint128_t lo = bmul64_u128(e[0],r[0]);
  uint128_t tmp1 = bmul64_u128(e[0],r[1]);
  uint128_t tmp2 = bmul64_u128(e[1],r[0]);
  uint128_t hi = bmul64_u128(e[1],r[1]);

  tmp1 ^= tmp2;
  lo ^= tmp1 << 64;
  hi ^= tmp1 >> 64;
  hi = (hi << 1) | (lo >> 127);
  lo = lo << 1;

  uint64_t t0 = (uint64_t) lo;
  uint64_t t1 = t0 << 63;
  uint64_t t2 = t0 << 62;
  uint64_t t3 = t0 << 57;
  t1 ^= t2;
  t1 ^= t3;
  lo ^= ((uint128_t)t1) << 64;

  lo ^= (lo >> 1) ^ (lo >> 2) ^ (lo >> 7);
  lo ^= hi;
  
  e[1] = lo >> 64;
  e[0] = (uint64_t) lo;

}


static inline void encode(elem_t e, const block_t b) {
  e[1] = load64_be(b);
  e[0] = load64_be(b+8);
}

static inline void encode4(elem_t e, const block_t b) {
  e[1] = load64_be(b);
  e[0] = load64_be(b+8);
  e[3] = load64_be(b+16);
  e[2] = load64_be(b+24);
  e[5] = load64_be(b+32);
  e[4] = load64_be(b+40);
  e[7] = load64_be(b+48);
  e[6] = load64_be(b+56);
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
  fmul_pre(acc,pre);
}

static inline void update4(elem_t acc, const block_t b, const precomp_t pre) {
  uint64_t tmp[8] = {0};
  encode4(tmp,b);
  fadd(acc,tmp);
  fmul_pre(acc,pre);
  fadd(acc,tmp+2);
  fmul_pre(acc,pre);
  fadd(acc,tmp+4);
  fmul_pre(acc,pre);
  fadd(acc,tmp+6);
  fmul_pre(acc,pre);
}

static inline void update_last(elem_t acc, const block_t b, int blen, const precomp_t pre) {
  uint64_t tmp[2];
  encode_last(tmp,b,blen);
  fadd(acc,tmp);
  fmul_pre(acc,pre);
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

static inline void poly4(elem_t acc, uint8_t* text, int tlen, const precomp_t pre) {
  acc[0] = 0;
  acc[1] = 0;
  int blocks = tlen / 64;
  for (int i = 0; i < blocks; i++) {
    update4(acc,text + 64*i, pre);
  }
  if (tlen % 64 > 0) {
    poly(acc,text + 64*blocks, tlen % 64, pre);
  }
}

void ghash(uint8_t* tag, uint8_t* text, int tlen, uint8_t* key) {
  uint64_t acc[2] = {0};
  uint64_t pre[256] = {0};
  encode(acc,key);
  prepare(pre,acc);
  //pre[0] = acc[0];
  //pre[1] = acc[1];
  poly4(acc,text,tlen,pre);
  decode(tag,acc);
}
	  
