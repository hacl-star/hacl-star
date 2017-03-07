#ifndef __Chacha20_state_H
#define __Chacha20_state_H

//#include "vec256.h"
#include "vec128.h"
//#include "vec_buf.h"

typedef vec chacha20_state[4];

static inline void chacha20_state_init(chacha20_state st, const unsigned char* k, const unsigned char* n, unsigned int ctr) {
  unsigned * kp = (unsigned *)k;
  unsigned * np = (unsigned *)n;
#if defined(VEC256)
  st[0] = (vec) {0x61707865,0x3320646E,0x79622D32,0x6B206574,0x61707865,0x3320646E,0x79622D32,0x6B206574}; 
  st[1] = (vec) {kp[0], kp[1], kp[2], kp[3],kp[0], kp[1], kp[2], kp[3]};
  st[2] = (vec) {kp[4], kp[5], kp[6], kp[7],kp[4], kp[5], kp[6], kp[7]};
  st[3] = (vec) {ctr,   np[0], np[1], np[2],ctr+1, np[0], np[1], np[2]};
#elif defined(VEC128)
  st[0] = (vec) {0x61707865,0x3320646E,0x79622D32,0x6B206574};
  st[1] = (vec) {kp[0], kp[1], kp[2], kp[3]};
  st[2] = (vec) {kp[4], kp[5], kp[6], kp[7]};
  st[3] = (vec) {ctr,   np[0], np[1], np[2]};
#else
  vec v1 = {.x0=0x61707865,.x1=0x3320646E,.x2=0x79622D32,.x3=0x6B206574};
  vec v2 = {.x0=kp[0],     .x1=kp[1],     .x2=kp[2],     .x3=kp[3]};
  vec v3 = {.x0=kp[4],     .x1=kp[5],     .x2=kp[6],     .x3=kp[7]};
  vec v4 = {.x0=ctr,       .x1=np[0],     .x2=np[1],     .x3=np[2]};
  st[0] = v1;
  st[1] = v2;
  st[2] = v3;
  st[3] = v4;
#endif
}

static inline void chacha20_state_to_key(chacha20_state k, chacha20_state st) {
#if defined(VEC256)
  k[0] = vec256_choose_128(st[0], st[1], 0, 2);
  k[1] = vec256_choose_128(st[2], st[3], 0, 2);
  k[2] = vec256_choose_128(st[0], st[1], 1, 3);
  k[3] = vec256_choose_128(st[2], st[3], 1, 3);
#else
  k[0] = st[0];
  k[1] = st[1];
  k[2] = st[2];
  k[3] = st[3];
#endif
}


#endif
