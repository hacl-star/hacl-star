#include <inttypes.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include "endianness.h"

#include <wmmintrin.h>
#include <emmintrin.h>
#include <smmintrin.h>
#include "vec128.h"

#define inline __attribute((always_inline))
typedef uint8_t* block_t;
typedef uint64_t* precomp_t;
typedef __m128i* elem_t;

static inline void fadd(elem_t e1, const elem_t e2) {
  *e1 = Lib_Vec128_vec128_xor(*e1, *e2);
}



static inline void fmul(elem_t e1, elem_t e2) {
  __m128i lo, hi, tmp0, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;

  lo = Lib_Vec128_ni_clmul(*e1, *e2, 0x00);
  tmp0 = Lib_Vec128_ni_clmul(*e1, *e2, 0x10);
  tmp1 = Lib_Vec128_ni_clmul(*e1, *e2, 0x01);
  hi = Lib_Vec128_ni_clmul(*e1, *e2, 0x11);

  tmp0 = Lib_Vec128_vec128_xor(tmp0, tmp1);
  tmp1 = Lib_Vec128_vec128_shift_right(tmp0, 64);
  tmp0 = Lib_Vec128_vec128_shift_left(tmp0, 64);
  lo = Lib_Vec128_vec128_xor(lo, tmp0);
  hi = Lib_Vec128_vec128_xor(hi, tmp1);

  
  tmp7 = Lib_Vec128_vec128_shift_right64(lo, 63);
  tmp9 = Lib_Vec128_vec128_shift_left(tmp7, 64);
  tmp3 = Lib_Vec128_vec128_shift_left64(lo, 1);
  tmp3 = Lib_Vec128_vec128_xor(tmp3, tmp9);

  tmp8 = Lib_Vec128_vec128_shift_right64(hi, 63);
  tmp8 = Lib_Vec128_vec128_shift_left(tmp8, 64);
  tmp6 = Lib_Vec128_vec128_shift_left64(hi, 1);
  tmp6 = Lib_Vec128_vec128_xor(tmp6, tmp8);
  
  tmp7 = Lib_Vec128_vec128_shift_right64(lo, 63); // we can save this shift
  tmp7 = Lib_Vec128_vec128_shift_right(tmp7, 64);
  tmp6 = Lib_Vec128_vec128_xor(tmp6, tmp7);


  /* LEFT SHIFT [x0:0] BY 63,62,57 and xor with [x1:x0] */
  tmp7 = Lib_Vec128_vec128_shift_left64(tmp3, 63);
  tmp8 = Lib_Vec128_vec128_shift_left64(tmp3, 62);
  tmp9 = Lib_Vec128_vec128_shift_left64(tmp3, 57);
  tmp7 = Lib_Vec128_vec128_xor(tmp7, tmp8);
  tmp7 = Lib_Vec128_vec128_xor(tmp7, tmp9);
  tmp8 = Lib_Vec128_vec128_shift_right(tmp7, 64);
  tmp7 = Lib_Vec128_vec128_shift_left(tmp7, 64);
  tmp3 = Lib_Vec128_vec128_xor(tmp3, tmp7);

  /* RIGHT SHIFT [x1:x0] BY 1,2,7 and xor with [x1:x0] */
  tmp2 = Lib_Vec128_vec128_shift_right64(tmp3, 1);
  tmp4 = Lib_Vec128_vec128_shift_right64(tmp3, 2);
  tmp5 = Lib_Vec128_vec128_shift_right64(tmp3, 7);
  tmp2 = Lib_Vec128_vec128_xor(tmp2, tmp4);
  tmp2 = Lib_Vec128_vec128_xor(tmp2, tmp5);
  
  tmp2 = Lib_Vec128_vec128_xor(tmp2, tmp8);
  tmp3 = Lib_Vec128_vec128_xor(tmp3, tmp2);

  /* XOR [x1:x0] with [x3:x2] */
  tmp6 = Lib_Vec128_vec128_xor(tmp6, tmp3);
  *e1 = tmp6;

}


static inline void encode(elem_t e, const block_t b) {
  *e = Lib_Vec128_vec128_load_be(b);
}

static inline void encode_last(elem_t e, const block_t b, int blen) {
  uint8_t block[16] = {0};
  memcpy(block,b,blen);
  encode(e,block);
}

static inline void decode(block_t b, const elem_t e) {
  Lib_Vec128_vec128_store_be(b,*e);
}

static inline void update(elem_t acc, elem_t b, const elem_t r) {
  fadd(acc,b);
  fmul(acc,r);
}

static inline void poly(elem_t acc, uint8_t* text, int tlen, const elem_t r) {
  int blocks = tlen / 16;
  __m128i elem = Lib_Vec128_vec128_zero;
  for (int i = 0; i < blocks; i++) {
    encode(&elem,text + 16*i);
    update(acc,&elem, r);
  }
  if (tlen % 16 > 0) {
    encode_last(&elem,text + 16*blocks,tlen % 16);
    update(acc,&elem, r);
  }
}

void ghash(uint8_t* tag, uint8_t* text, int tlen, uint8_t* key) {
  __m128i r = Lib_Vec128_vec128_zero;
  __m128i acc = Lib_Vec128_vec128_zero;
  encode(&r,key);
  poly(&acc,text,tlen,&r);
  decode(tag,&acc);
}
	  
