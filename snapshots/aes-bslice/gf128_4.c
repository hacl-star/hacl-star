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

static inline void fmul4(elem_t e1, elem_t e2, elem_t e3, elem_t e4,  const precomp_t pre) {
  uint64_t tmp10 = 0;
  uint64_t tmp11 = 0;
  uint64_t tmp20 = 0;
  uint64_t tmp21 = 0;
  uint64_t tmp30 = 0;
  uint64_t tmp31 = 0;
  uint64_t tmp40 = 0;
  uint64_t tmp41 = 0;
  for (int i = 0; i < 64; i++) {
    uint64_t m1 = -( (e1[1] >> (63-i)) & 1);
    uint64_t m2 = -( (e2[1] >> (63-i)) & 1);
    uint64_t m3 = -( (e3[1] >> (63-i)) & 1);
    uint64_t m4 = -( (e4[1] >> (63-i)) & 1);
    tmp10 ^= (m1 & pre[2*i]);
    tmp11 ^= (m1 & pre[2*i+1]);
    tmp20 ^= (m2 & pre[2*i]);
    tmp21 ^= (m2 & pre[2*i+1]);
    tmp30 ^= (m3 & pre[2*i]);
    tmp31 ^= (m3 & pre[2*i+1]);
    tmp40 ^= (m4 & pre[2*i]);
    tmp41 ^= (m4 & pre[2*i+1]);
  }
  for (int i = 64; i < 128; i++) {
    uint64_t m1 = -( (e1[1] >> (127-i)) & 1);
    uint64_t m2 = -( (e2[1] >> (127-i)) & 1);
    uint64_t m3 = -( (e3[1] >> (127-i)) & 1);
    uint64_t m4 = -( (e4[1] >> (127-i)) & 1);
    tmp10 ^= (m1 & pre[2*i]);
    tmp11 ^= (m1 & pre[2*i+1]);
    tmp20 ^= (m2 & pre[2*i]);
    tmp21 ^= (m2 & pre[2*i+1]);
    tmp30 ^= (m3 & pre[2*i]);
    tmp31 ^= (m3 & pre[2*i+1]);
    tmp40 ^= (m4 & pre[2*i]);
    tmp41 ^= (m4 & pre[2*i+1]);
  }
  e1[0] = tmp10;
  e1[1] = tmp11;
  e2[0] = tmp20;
  e2[1] = tmp21;
  e3[0] = tmp30;
  e3[1] = tmp31;
  e4[0] = tmp40;
  e4[1] = tmp41;
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
  fmul_pre(acc,pre);
}

static inline void update_last(elem_t acc, const block_t b, int blen, const precomp_t pre) {
  uint64_t tmp[2];
  encode_last(tmp,b,blen);
  fadd(acc,tmp);
  fmul_pre(acc,pre);
}

static inline void poly(elem_t acc, uint8_t* text, int tlen, const precomp_t pre) {
  int blocks = tlen / 16;
  for (int i = 0; i < blocks; i++) {
    update(acc,text + 16*i, pre);
  }
  if (tlen % 16 > 0) {
    update_last(acc,text + 16*blocks, tlen % 16, pre);
  }
}


static inline void poly4(elem_t acc0, elem_t acc1, elem_t acc2, elem_t acc3,
			 elem_t k, elem_t k2, elem_t k3, elem_t k4,
			 uint8_t* text, int tlen, const precomp_t pre) {
  uint64_t tmp0[2] = {0};
  uint64_t tmp1[2] = {0};
  uint64_t tmp2[2] = {0};
  uint64_t tmp3[2] = {0};
  int blocks = tlen / 64;
  if (blocks > 0) {
    encode(tmp0,text);
    encode(tmp1,text+16);
    encode(tmp2,text+32);
    encode(tmp3,text+48);
    acc0[0] = tmp0[0];
    acc0[1] = tmp0[1];
    acc1[0] = tmp1[0];
    acc1[1] = tmp1[1];
    acc2[0] = tmp2[0];
    acc2[1] = tmp2[1];
    acc3[0] = tmp3[0];
    acc3[1] = tmp3[1];
  for (int i = 1; i < blocks; i++) {
    encode(tmp0,text+64*i);
    encode(tmp1,text+64*i+16);
    encode(tmp2,text+64*i+32);
    encode(tmp3,text+64*i+48);
    fmul_pre(acc0,pre);
    fmul_pre(acc1,pre);
    fmul_pre(acc2,pre);
    fmul_pre(acc3,pre);
//    fmul4(acc0,acc1,acc2,acc3,pre);
    fadd(acc0,tmp0);
    fadd(acc1,tmp1);
    fadd(acc2,tmp2);
    fadd(acc3,tmp3);
  }
  fmul_reduce(acc0,k4);
  fmul_reduce(acc1,k3);
  fmul_reduce(acc2,k2);
  fmul_reduce(acc3,k);
  fadd(acc0,acc1);
  fadd(acc0,acc2);
  fadd(acc0,acc3);
  }
  if (tlen % 64 > 0) {
    int blocks16 = (tlen % 64) / 16;
    for (int j = 0; j < blocks16; j++) {
      encode(tmp0,text + 64*blocks + 16*j);
      fadd(acc0,tmp0);
      fmul_reduce(acc0,k);
    }
    if (tlen % 16 > 0) {
      uint8_t tmp[16] = {0};
      memcpy(tmp,text + 64*blocks + 16*blocks16,tlen % 16);
      encode(tmp0,tmp);
      fadd(acc0,tmp0);
      fmul_reduce(acc0,k);
    }
  }
}


void ghash(uint8_t* tag, uint8_t* text, int tlen, uint8_t* key) {
  uint64_t k[2] = {0};
  encode(k,key);
  uint64_t k2[2] = {0};
  uint64_t k3[2] = {0};
  uint64_t k4[2] = {0};
  k2[0] = k[0];
  k2[1] = k[1];
  k3[0] = k[0];
  k3[1] = k[1];
  fmul_reduce(k2,k);
  fmul_reduce(k3,k2);
  k4[0] = k2[0];
  k4[1] = k2[1];
  fmul_reduce(k4,k2);
  
  uint64_t pre[256] = {0};
  prepare(pre,k4);

  uint64_t acc0[2] = {0};
  uint64_t acc1[2] = {0};
  uint64_t acc2[2] = {0};
  uint64_t acc3[2] = {0};
  poly4(acc0,acc1,acc2,acc3,k,k2,k3,k4,text,tlen,pre);
  decode(tag,acc0);
}
	  
