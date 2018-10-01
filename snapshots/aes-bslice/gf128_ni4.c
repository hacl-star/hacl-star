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
  e1[0] = _mm_xor_si128(e1[0], e2[0]);
}

void reduce4 (elem_t acc, elem_t r4, elem_t b4)
{

  /*algorithm by Krzysztof Jankowski, Pierre Laurent - Intel*/
  __m128i H1_X1_lo, H1_X1_hi,
    H2_X2_lo, H2_X2_hi, H3_X3_lo, H3_X3_hi, H4_X4_lo, H4_X4_hi, lo, hi;
  __m128i tmp0, tmp1, tmp2, tmp3;
  __m128i tmp4, tmp5, tmp6, tmp7;
  __m128i tmp8, tmp9;

#ifdef KARATSUBA
  H1_X1_lo = _mm_clmulepi64_si128(r4[0], b4[0], 0x00);
  H2_X2_lo = _mm_clmulepi64_si128(r4[1], b4[1], 0x00);
  H3_X3_lo = _mm_clmulepi64_si128(r4[2], b4[2], 0x00);
  H4_X4_lo = _mm_clmulepi64_si128(r4[3], b4[3], 0x00);
  lo = _mm_xor_si128(H1_X1_lo, H2_X2_lo);
  lo = _mm_xor_si128(lo, H3_X3_lo);
  lo = _mm_xor_si128(lo, H4_X4_lo);
  H1_X1_hi = _mm_clmulepi64_si128(r4[0], b4[0], 0x11);
  H2_X2_hi = _mm_clmulepi64_si128(r4[1], b4[1], 0x11);
  H3_X3_hi = _mm_clmulepi64_si128(r4[2], b4[2], 0x11);
  H4_X4_hi = _mm_clmulepi64_si128(r4[3], b4[3], 0x11);
  hi = _mm_xor_si128(H1_X1_hi, H2_X2_hi);
  hi = _mm_xor_si128(hi, H3_X3_hi);
  hi = _mm_xor_si128(hi, H4_X4_hi);

  tmp0 = _mm_shuffle_epi32(r4[0], 78);
  tmp4 = _mm_shuffle_epi32(b4[0], 78);
  tmp0 = _mm_xor_si128(tmp0, r4[0]);
  tmp4 = _mm_xor_si128(tmp4, b4[0]);
  tmp1 = _mm_shuffle_epi32(r4[1], 78);
  tmp5 = _mm_shuffle_epi32(b4[1], 78);
  tmp1 = _mm_xor_si128(tmp1, r4[1]);
  tmp5 = _mm_xor_si128(tmp5, b4[1]);
  tmp2 = _mm_shuffle_epi32(r4[2], 78);
  tmp6 = _mm_shuffle_epi32(b4[2], 78);
  tmp2 = _mm_xor_si128(tmp2, r4[2]);
  tmp6 = _mm_xor_si128(tmp6, b4[2]);
  tmp3 = _mm_shuffle_epi32(r4[3], 78);
  tmp7 = _mm_shuffle_epi32(b4[3], 78);
  tmp3 = _mm_xor_si128(tmp3, r4[3]);
  tmp7 = _mm_xor_si128(tmp7, b4[3]);

  tmp0 = _mm_clmulepi64_si128(tmp0, tmp4, 0x00);
  tmp1 = _mm_clmulepi64_si128(tmp1, tmp5, 0x00);
  tmp2 = _mm_clmulepi64_si128(tmp2, tmp6, 0x00);
  tmp3 = _mm_clmulepi64_si128(tmp3, tmp7, 0x00);

  tmp0 = _mm_xor_si128(tmp0, lo);
  tmp0 = _mm_xor_si128(tmp0, hi);
  tmp0 = _mm_xor_si128(tmp1, tmp0);
  tmp0 = _mm_xor_si128(tmp2, tmp0);
  tmp0 = _mm_xor_si128(tmp3, tmp0);
  tmp4 = _mm_slli_si128(tmp0, 8);
  tmp0 = _mm_srli_si128(tmp0, 8);
  lo = _mm_xor_si128(tmp4, lo);
  hi = _mm_xor_si128(tmp0, hi);

#else
  H1_X1_lo = _mm_clmulepi64_si128(r4[0], b4[0], 0x00);
  H2_X2_lo = _mm_clmulepi64_si128(r4[1], b4[1], 0x00);
  H3_X3_lo = _mm_clmulepi64_si128(r4[2], b4[2], 0x00);
  H4_X4_lo = _mm_clmulepi64_si128(r4[3], b4[3], 0x00);
  lo = _mm_xor_si128(H1_X1_lo, H2_X2_lo);
  lo = _mm_xor_si128(lo, H3_X3_lo);
  lo = _mm_xor_si128(lo, H4_X4_lo);
  H1_X1_hi = _mm_clmulepi64_si128(r4[0], b4[0], 0x11);
  H2_X2_hi = _mm_clmulepi64_si128(r4[1], b4[1], 0x11);
  H3_X3_hi = _mm_clmulepi64_si128(r4[2], b4[2], 0x11);
  H4_X4_hi = _mm_clmulepi64_si128(r4[3], b4[3], 0x11);
  hi = _mm_xor_si128(H1_X1_hi, H2_X2_hi);
  hi = _mm_xor_si128(hi, H3_X3_hi);
  hi = _mm_xor_si128(hi, H4_X4_hi);

  H1_X1_lo = _mm_clmulepi64_si128(r4[0], b4[0], 0x01);
  H2_X2_lo = _mm_clmulepi64_si128(r4[1], b4[1], 0x01);
  H3_X3_lo = _mm_clmulepi64_si128(r4[2], b4[2], 0x01);
  H4_X4_lo = _mm_clmulepi64_si128(r4[3], b4[3], 0x01);
  tmp0 = _mm_xor_si128(H1_X1_lo, H2_X2_lo);
  tmp0 = _mm_xor_si128(tmp0, H3_X3_lo);
  tmp0 = _mm_xor_si128(tmp0, H4_X4_lo);
  H1_X1_hi = _mm_clmulepi64_si128(r4[0], b4[0], 0x10);
  H2_X2_hi = _mm_clmulepi64_si128(r4[1], b4[1], 0x10);
  H3_X3_hi = _mm_clmulepi64_si128(r4[2], b4[2], 0x10);
  H4_X4_hi = _mm_clmulepi64_si128(r4[3], b4[3], 0x10);
  tmp1 = _mm_xor_si128(H1_X1_hi, H2_X2_hi);
  tmp1 = _mm_xor_si128(tmp1, H3_X3_hi);
  tmp1 = _mm_xor_si128(tmp1, H4_X4_hi);

  tmp0 = _mm_xor_si128(tmp0, tmp1);
  tmp1 = _mm_srli_si128(tmp0, 8);
  tmp0 = _mm_slli_si128(tmp0, 8);
  lo = _mm_xor_si128(tmp0, lo);
  hi = _mm_xor_si128(tmp1, hi);
#endif

  /* LEFT SHIFT BY [x3:x2:x1:x0] by 1 */
  /* tmp7 = _mm_srli_epi32(lo, 31); */
  /* tmp8 = _mm_srli_epi32(hi, 31); */
  /* tmp3 = _mm_slli_epi32(lo, 1); */
  /* tmp6 = _mm_slli_epi32(hi, 1); */
  /* tmp9 = _mm_srli_si128(tmp7, 12); */
  /* tmp8 = _mm_slli_si128(tmp8, 4); */
  /* tmp7 = _mm_slli_si128(tmp7, 4); */
  /* tmp3 = _mm_or_si128(tmp3, tmp7); */
  /* tmp6 = _mm_or_si128(tmp6, tmp8); */
  /* tmp6 = _mm_or_si128(tmp6, tmp9); */

  /* /\* LEFT SHIFT [x0:0] BY 63,62,57 and xor with [x1:x0] *\/ */
  /* tmp7 = _mm_slli_epi32(tmp3, 31); */
  /* tmp8 = _mm_slli_epi32(tmp3, 30); */
  /* tmp9 = _mm_slli_epi32(tmp3, 25); */
  /* tmp7 = _mm_xor_si128(tmp7, tmp8); */
  /* tmp7 = _mm_xor_si128(tmp7, tmp9); */
  /* tmp8 = _mm_srli_si128(tmp7, 4); */
  /* tmp7 = _mm_slli_si128(tmp7, 12); */
  /* tmp3 = _mm_xor_si128(tmp3, tmp7); */

  /* /\* RIGHT SHIFT [x1:x0] BY 1,2,7 and xor with [x1:x0] *\/ */
  /* tmp2 = _mm_srli_epi32(tmp3, 1); */
  /* tmp4 = _mm_srli_epi32(tmp3, 2); */
  /* tmp5 = _mm_srli_epi32(tmp3, 7); */
  /* tmp2 = _mm_xor_si128(tmp2, tmp4); */
  /* tmp2 = _mm_xor_si128(tmp2, tmp5); */
  /* tmp2 = _mm_xor_si128(tmp2, tmp8); */
  /* tmp3 = _mm_xor_si128(tmp3, tmp2); */

 /* LEFT SHIFT BY [x3:x2:x1:x0] by 1 */
  tmp7 = _mm_srli_epi64(lo, 63);
  tmp9 = _mm_slli_si128(tmp7, 8);
  tmp3 = _mm_slli_epi64(lo, 1);
  tmp3 = _mm_or_si128(tmp3, tmp9);

  tmp8 = _mm_srli_epi64(hi, 63);
  tmp8 = _mm_slli_si128(tmp8, 8);
  tmp6 = _mm_slli_epi64(hi, 1);
  tmp6 = _mm_or_si128(tmp6, tmp8);
  
  tmp7 = _mm_srli_epi64(lo, 63); // we can save this shift
  tmp7 = _mm_srli_si128(tmp7, 8);
  tmp6 = _mm_or_si128(tmp6, tmp7);


  /* LEFT SHIFT [x0:0] BY 63,62,57 and xor with [x1:x0] */
  tmp7 = _mm_slli_epi64(tmp3, 63);
  tmp8 = _mm_slli_epi64(tmp3, 62);
  tmp9 = _mm_slli_epi64(tmp3, 57);
  tmp7 = _mm_xor_si128(tmp7, tmp8);
  tmp7 = _mm_xor_si128(tmp7, tmp9);
  tmp8 = _mm_srli_si128(tmp7, 8);
  tmp7 = _mm_slli_si128(tmp7, 8);
  tmp3 = _mm_xor_si128(tmp3, tmp7);

  /* RIGHT SHIFT [x1:x0] BY 1,2,7 and xor with [x1:x0] */
  tmp2 = _mm_srli_epi64(tmp3, 1);
  tmp4 = _mm_srli_epi64(tmp3, 2);
  tmp5 = _mm_srli_epi64(tmp3, 7);
  tmp2 = _mm_xor_si128(tmp2, tmp4);
  tmp2 = _mm_xor_si128(tmp2, tmp5);
  
  tmp2 = _mm_xor_si128(tmp2, tmp8);
  tmp3 = _mm_xor_si128(tmp3, tmp2);

  /* XOR [x1:x0] with [x3:x2] */
  tmp6 = _mm_xor_si128(tmp6, tmp3);
  *acc = tmp6;
}

static inline void fmul(elem_t e1, elem_t e2) {
  __m128i tmp0, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
  
  tmp3 = _mm_clmulepi64_si128(*e1, *e2, 0x00);
  tmp4 = _mm_clmulepi64_si128(*e1, *e2, 0x10);
  tmp5 = _mm_clmulepi64_si128(*e1, *e2, 0x01);
  tmp6 = _mm_clmulepi64_si128(*e1, *e2, 0x11);

  tmp4 = _mm_xor_si128(tmp4, tmp5);
  tmp5 = _mm_slli_si128(tmp4, 8);
  tmp4 = _mm_srli_si128(tmp4, 8);
  tmp3 = _mm_xor_si128(tmp3, tmp5);
  tmp6 = _mm_xor_si128(tmp6, tmp4);

  tmp7 = _mm_srli_epi32(tmp3, 31);
  tmp8 = _mm_srli_epi32(tmp6, 31);
  tmp3 = _mm_slli_epi32(tmp3, 1);
  tmp6 = _mm_slli_epi32(tmp6, 1);

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

static inline void update4(elem_t acc, const block_t b, const elem_t r4) {
  __m128i tmp[4];
  __m128i BSWAP_MASK = _mm_set_epi8(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13,
14, 15);
  __m128i inp0 = _mm_loadu_si128((__m128i*)b);
  __m128i inp1 = _mm_loadu_si128((__m128i*)(b+16));
  __m128i inp2 = _mm_loadu_si128((__m128i*)(b+32));
  __m128i inp3 = _mm_loadu_si128((__m128i*)(b+48));
  inp0 = _mm_shuffle_epi8(inp0, BSWAP_MASK);
  inp1 = _mm_shuffle_epi8(inp1, BSWAP_MASK);
  inp2 = _mm_shuffle_epi8(inp2, BSWAP_MASK);
  inp3 = _mm_shuffle_epi8(inp3, BSWAP_MASK);
  inp0 = _mm_xor_si128(acc[0], inp0);
  tmp[0] = inp0;
  tmp[1] = inp1;
  tmp[2] = inp2;
  tmp[3] = inp3;
  reduce4(acc,r4,tmp);
}

static inline void update_last(elem_t acc, const block_t b, int blen, const elem_t r) {
  __m128i tmp;
  encode_last(&tmp,b,blen);
  fadd(acc,&tmp);
  fmul(acc,r);
}

static inline void poly(elem_t acc, uint8_t* text, int tlen, const elem_t r) {
  __m128i r2,r3,r22;
  __m128i r4[4];
  r2 = *r;
  fmul(&r2,r);
  r3 = r2;
  r22 = r2;
  fmul(&r3,r);
  fmul(&r22,&r2);
  r4[0] = r22;
  r4[1] = r3;
  r4[2] = r2;
  r4[3] = *r;
  
  int blocks = tlen / 64;
  for (int i = 0; i < blocks; i++) {
    update4(acc,text + 64*i, r4);
  }
  text = text + 64*blocks;
  blocks = (tlen % 64) / 16;
  //int blocks = tlen / 16;
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
	  
