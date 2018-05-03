#include <inttypes.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <wmmintrin.h>
#include <smmintrin.h>
#include "endianness.h"

typedef __m128i* state_t;


static inline void aes_enc(state_t st, state_t k) {
  *st = _mm_aesenc_si128(*st,*k);
}

static inline void aes_enc_last(state_t st, state_t k) {
  *st = _mm_aesenclast_si128(*st,*k);
}

#define INTERLEAVE 8
static void rounds(state_t st, state_t key) {
  for (int i = 0; i < 9; i++) 
    for (int j = 0; j < INTERLEAVE; j++) 
      aes_enc(st+j,key+i);
}

static void block_cipher(state_t out, state_t key) {
  state_t k0 = key;
  state_t k = key + 1;
  state_t kn = key + 10;
  for (int j = 0; j < INTERLEAVE; j++)
    out[j] = _mm_xor_si128(out[j], *k0); 
  rounds(out,k);
  for (int j = 0; j < INTERLEAVE; j++)
    aes_enc_last(out+j,kn);
}

static inline void key_expansion_step(state_t next, state_t prev){
  *next = _mm_shuffle_epi32(*next, _MM_SHUFFLE(3,3,3,3));
  __m128i key = *prev;
  key = _mm_xor_si128(key, _mm_slli_si128(key, 4));
  key = _mm_xor_si128(key, _mm_slli_si128(key, 4));
  key = _mm_xor_si128(key, _mm_slli_si128(key, 4));
  *next = _mm_xor_si128(*next,key);
}

static void key_expansion(state_t out, uint8_t* key) {
  out[0] = _mm_loadu_si128((const __m128i*) key);
  out[1] = _mm_aeskeygenassist_si128(out[0], 0x01);
  key_expansion_step(out+1,out);
  out[2] = _mm_aeskeygenassist_si128(out[1], 0x02);
  key_expansion_step(out+2,out+1);
  out[3] = _mm_aeskeygenassist_si128(out[2], 0x04);
  key_expansion_step(out+3,out+2);
  out[4] = _mm_aeskeygenassist_si128(out[3], 0x08);
  key_expansion_step(out+4,out+3);
  out[5] = _mm_aeskeygenassist_si128(out[4], 0x10);
  key_expansion_step(out+5,out+4);
  out[6] = _mm_aeskeygenassist_si128(out[5], 0x20);
  key_expansion_step(out+6,out+5);
  out[7] = _mm_aeskeygenassist_si128(out[6], 0x40);
  key_expansion_step(out+7,out+6);
  out[8] = _mm_aeskeygenassist_si128(out[7], 0x80);
  key_expansion_step(out+8,out+7);
  out[9] = _mm_aeskeygenassist_si128(out[8], 0x1b);
  key_expansion_step(out+9,out+8);
  out[10] = _mm_aeskeygenassist_si128(out[9], 0x36);
  key_expansion_step(out+10,out+9);
}

static void aes128_block(state_t out,state_t kex, uint8_t* n, uint32_t c) {
  uint8_t tmp[16];
  memcpy(tmp,n,12);
  for (int i = 0; i < INTERLEAVE; i++) {
    store32_be(tmp+12,c+i);
    out[i] = _mm_loadu_si128((__m128i*) tmp);
  }
  block_cipher(out,kex);
}

static void aes128_ctr(uint8_t* out, uint8_t* in, int len, uint8_t* k, uint8_t* n, uint32_t cc) {
  __m128i sk[11] = {0};
  key_expansion(sk,k);


  unsigned char ivbuf[16];
  unsigned char *buf;
  buf = in;
  memcpy(ivbuf, n, 12);
  __m128i ivx = _mm_loadu_si128((void *)ivbuf);
  while (len > 0) {
    __m128i x0, x1, x2, x3;
    
    x0 = _mm_insert_epi32(ivx, __builtin_bswap32(cc + 0), 3);
    x1 = _mm_insert_epi32(ivx, __builtin_bswap32(cc + 1), 3);
    x2 = _mm_insert_epi32(ivx, __builtin_bswap32(cc + 2), 3);
    x3 = _mm_insert_epi32(ivx, __builtin_bswap32(cc + 3), 3);
    x0 = _mm_xor_si128(x0, sk[0]);
    x1 = _mm_xor_si128(x1, sk[0]);
    x2 = _mm_xor_si128(x2, sk[0]);
    x3 = _mm_xor_si128(x3, sk[0]);
    x0 = _mm_aesenc_si128(x0, sk[1]);
    x1 = _mm_aesenc_si128(x1, sk[1]);
    x2 = _mm_aesenc_si128(x2, sk[1]);
    x3 = _mm_aesenc_si128(x3, sk[1]);
    x0 = _mm_aesenc_si128(x0, sk[2]);
    x1 = _mm_aesenc_si128(x1, sk[2]);
    x2 = _mm_aesenc_si128(x2, sk[2]);
    x3 = _mm_aesenc_si128(x3, sk[2]);
    x0 = _mm_aesenc_si128(x0, sk[3]);
    x1 = _mm_aesenc_si128(x1, sk[3]);
    x2 = _mm_aesenc_si128(x2, sk[3]);
    x3 = _mm_aesenc_si128(x3, sk[3]);
    x0 = _mm_aesenc_si128(x0, sk[4]);
    x1 = _mm_aesenc_si128(x1, sk[4]);
    x2 = _mm_aesenc_si128(x2, sk[4]);
    x3 = _mm_aesenc_si128(x3, sk[4]);
    x0 = _mm_aesenc_si128(x0, sk[5]);
    x1 = _mm_aesenc_si128(x1, sk[5]);
    x2 = _mm_aesenc_si128(x2, sk[5]);
    x3 = _mm_aesenc_si128(x3, sk[5]);
    x0 = _mm_aesenc_si128(x0, sk[6]);
    x1 = _mm_aesenc_si128(x1, sk[6]);
    x2 = _mm_aesenc_si128(x2, sk[6]);
    x3 = _mm_aesenc_si128(x3, sk[6]);
    x0 = _mm_aesenc_si128(x0, sk[7]);
    x1 = _mm_aesenc_si128(x1, sk[7]);
    x2 = _mm_aesenc_si128(x2, sk[7]);
    x3 = _mm_aesenc_si128(x3, sk[7]);
    x0 = _mm_aesenc_si128(x0, sk[8]);
    x1 = _mm_aesenc_si128(x1, sk[8]);
    x2 = _mm_aesenc_si128(x2, sk[8]);
    x3 = _mm_aesenc_si128(x3, sk[8]);
    x0 = _mm_aesenc_si128(x0, sk[9]);
    x1 = _mm_aesenc_si128(x1, sk[9]);
    x2 = _mm_aesenc_si128(x2, sk[9]);
    x3 = _mm_aesenc_si128(x3, sk[9]);
    x0 = _mm_aesenclast_si128(x0, sk[10]);
    x1 = _mm_aesenclast_si128(x1, sk[10]);
    x2 = _mm_aesenclast_si128(x2, sk[10]);
    x3 = _mm_aesenclast_si128(x3, sk[10]);
    if (len >= 64) {
      x0 = _mm_xor_si128(x0,
			 _mm_loadu_si128((void *)(buf +  0)));
      x1 = _mm_xor_si128(x1,
			 _mm_loadu_si128((void *)(buf + 16)));
      x2 = _mm_xor_si128(x2,
			 _mm_loadu_si128((void *)(buf + 32)));
      x3 = _mm_xor_si128(x3,
			 _mm_loadu_si128((void *)(buf + 48)));
      _mm_storeu_si128((void *)(out +  0), x0);
      _mm_storeu_si128((void *)(out + 16), x1);
      _mm_storeu_si128((void *)(out + 32), x2);
      _mm_storeu_si128((void *)(out + 48), x3);
      buf += 64;
      out += 64;
      len -= 64;
      cc += 4;
    } else {
      unsigned char tmp[64];
      
      _mm_storeu_si128((void *)(tmp +  0), x0);
      _mm_storeu_si128((void *)(tmp + 16), x1);
      _mm_storeu_si128((void *)(tmp + 32), x2);
      _mm_storeu_si128((void *)(tmp + 48), x3);
      for (int u = 0; u < len; u ++) {
	out[u] = buf[u] ^ tmp[u];
      }
      cc += (uint32_t)len >> 4;
      break;
    }
  }
}

void aes128_encrypt(uint8_t* out, uint8_t* in, int in_len, uint8_t* k, uint8_t* n, uint32_t c) {
  aes128_ctr(out,in,in_len,k,n,c);
}

void aes128_decrypt(uint8_t* out, uint8_t* in, int in_len, uint8_t* k, uint8_t* n, uint32_t c) {
  aes128_ctr(out,in,in_len,k,n,c);
}
