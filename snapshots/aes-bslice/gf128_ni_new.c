#include <inttypes.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include "endianness.h"

#include <wmmintrin.h>
#include <emmintrin.h>
#include <smmintrin.h>

#define inline __attribute((always_inline))
typedef uint8_t* block_t;
typedef uint64_t* precomp_t;
typedef __m128i* elem_t;

static inline void fadd(elem_t e1, const elem_t e2) {
  *e1 = _mm_xor_si128(*e1, *e2);
}


static inline void fmul(elem_t e1, elem_t e2) {
  __m128i lo, hi, tmp0, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;

#ifdef KARATSUBA
  lo = _mm_clmulepi64_si128(*e1, *e2, 0x00);
  hi = _mm_clmulepi64_si128(*e1, *e2, 0x11);

  tmp0 = _mm_shuffle_epi32(*e1, 78);
  tmp0 = _mm_xor_si128(tmp0, *e1);
  tmp1 = _mm_shuffle_epi32(*e2, 78);
  tmp1 = _mm_xor_si128(tmp1, *e2);
  tmp2 = _mm_clmulepi64_si128(tmp0, tmp1, 0x00);

  tmp2 = _mm_xor_si128(tmp2, lo);
  tmp2 = _mm_xor_si128(tmp2, hi);
  tmp3 = _mm_slli_si128(tmp2, 8);
  tmp2 = _mm_srli_si128(tmp2, 8);
  lo = _mm_xor_si128(tmp3, lo);
  hi = _mm_xor_si128(tmp2, hi);
#else
  lo = _mm_clmulepi64_si128(*e1, *e2, 0x00);
  tmp0 = _mm_clmulepi64_si128(*e1, *e2, 0x10);
  tmp1 = _mm_clmulepi64_si128(*e1, *e2, 0x01);
  hi = _mm_clmulepi64_si128(*e1, *e2, 0x11);

  tmp0 = _mm_xor_si128(tmp0, tmp1);
  tmp1 = _mm_srli_si128(tmp0, 8);
  tmp0 = _mm_slli_si128(tmp0, 8);
  lo = _mm_xor_si128(lo, tmp0);
  hi = _mm_xor_si128(hi, tmp1);
#endif
  
  tmp7 = _mm_srli_epi32(lo, 31);
  tmp8 = _mm_srli_epi32(hi, 31);
  tmp3 = _mm_slli_epi32(lo, 1);
  tmp6 = _mm_slli_epi32(hi, 1);

  tmp9 = _mm_srli_si128(tmp7, 12);
  tmp8 = _mm_slli_si128(tmp8, 4);
  tmp7 = _mm_slli_si128(tmp7, 4);
  tmp3 = _mm_or_si128(tmp3, tmp7);
  tmp6 = _mm_or_si128(tmp6, tmp8);
  tmp6 = _mm_or_si128(tmp6, tmp9);

  tmp7 = _mm_slli_epi32(tmp3, 31);
  tmp8 = _mm_slli_epi32(tmp3, 30);
  tmp9 = _mm_slli_epi32(tmp3, 25);

  tmp7 = _mm_xor_si128(tmp7, tmp8);
  tmp7 = _mm_xor_si128(tmp7, tmp9);
  tmp8 = _mm_srli_si128(tmp7, 4);
  tmp7 = _mm_slli_si128(tmp7, 12);
  tmp3 = _mm_xor_si128(tmp3, tmp7);

  tmp2 = _mm_srli_epi32(tmp3, 1);
  tmp4 = _mm_srli_epi32(tmp3, 2);
  tmp5 = _mm_srli_epi32(tmp3, 7);
  tmp2 = _mm_xor_si128(tmp2, tmp4);
  tmp2 = _mm_xor_si128(tmp2, tmp5);
  tmp2 = _mm_xor_si128(tmp2, tmp8);
  tmp3 = _mm_xor_si128(tmp3, tmp2);
  tmp6 = _mm_xor_si128(tmp6, tmp3);

  *e1 = tmp6;
}


static inline void encode(elem_t e, const block_t b) {
  __m128i BSWAP_MASK = _mm_set_epi8(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13,
14, 15);
  __m128i inp = _mm_loadu_si128((__m128i*)b);
  *e = _mm_shuffle_epi8(inp, BSWAP_MASK);
}

static inline void encode_last(elem_t e, const block_t b, int blen) {
  uint8_t block[16] = {0};
  memcpy(block,b,blen);
  encode(e,block);
}

static inline void decode(block_t b, const elem_t e) {
  __m128i BSWAP_MASK = _mm_set_epi8(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13,
14, 15);
  __m128i out = _mm_shuffle_epi8(*e, BSWAP_MASK);
  _mm_storeu_si128((__m128i*)b, out);
}

static inline void update(elem_t acc, const block_t b, const elem_t r) {
  __m128i tmp;
  encode(&tmp,b);
  fadd(acc,&tmp);
  fmul(acc,r);
}

static inline void update_last(elem_t acc, const block_t b, int blen, const elem_t r) {
  __m128i tmp;
  encode_last(&tmp,b,blen);
  fadd(acc,&tmp);
  fmul(acc,r);
}

static inline void poly(elem_t acc, uint8_t* text, int tlen, const elem_t r) {
  int blocks = tlen / 16;
  for (int i = 0; i < blocks; i++) {
    update(acc,text + 16*i, r);
  }
  if (tlen % 16 > 0) {
    update_last(acc,text + 16*blocks, tlen % 16, r);
  }
}

void ghash(uint8_t* tag, uint8_t* text, int tlen, uint8_t* key) {
  __m128i r = {0};
  __m128i acc = {0};
  encode(&r,key);
  poly(&acc,text,tlen,&r);
  decode(tag,&acc);
}
	  
