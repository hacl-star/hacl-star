#include <inttypes.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <wmmintrin.h>

typedef __m128i* state_t;

#define static static inline __attribute((always_inline))

static void aes_enc(state_t st, state_t k) {
  *st = _mm_aesenc_si128(*st,*k);
}

static void aes_enc_last(state_t st, state_t k) {
  *st = _mm_aesenclast_si128(*st,*k);
}

static void rounds(state_t st, state_t key) {
  for (int i = 0; i < 9; i++)
    aes_enc(st,key+i);
}

static void block_cipher(state_t out, state_t key) {
  state_t k0 = key;
  state_t k = key + 1;
  state_t kn = key + 10;
  *out = _mm_xor_si128(*out, *k0); 
  rounds(out,k);
  aes_enc_last(out,kn);
}

static void key_expansion_step(state_t next, state_t prev){
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

static void aes128_block(uint8_t* out,state_t kex, uint8_t* n, uint32_t c) {
  memcpy(out,n,12);
  out[12] = (uint8_t)(c >> 24);
  out[13] = (uint8_t)(c >> 16);
  out[14] = (uint8_t)(c >> 8);
  out[15] = (uint8_t)(c);
  __m128i st = _mm_loadu_si128((__m128i*) out);
  block_cipher(&st,kex);
  _mm_storeu_si128((__m128i*) out,st);
}

static void aes128_ctr(uint8_t* out, uint8_t* in, int in_len, uint8_t* k, uint8_t* n, uint32_t c) {
  __m128i kex[11] = {0};
  key_expansion(kex,k);
  uint8_t kb[16] = {0};
  int blocks = in_len / 16;
  for (int i = 0; i < blocks; i++) {
    aes128_block(kb,kex,n,c+i);
    for (int j = 0; j < 16; j++)
      out[(16*i)+j] = in[(16*i)+j] ^ kb[j];
  }
  int rem = in_len % 16;
  if (rem > 0) {
      aes128_block(kb,kex,n,c+blocks);
      for (int j = 0; j < rem; j++)
	out[(16*blocks)+j] = in[(16*blocks)+j] ^ kb[j];
    }
}

void aes128_encrypt(uint8_t* out, uint8_t* in, int in_len, uint8_t* k, uint8_t* n, uint32_t c) {
  aes128_ctr(out,in,in_len,k,n,c);
}

void aes128_decrypt(uint8_t* out, uint8_t* in, int in_len, uint8_t* k, uint8_t* n, uint32_t c) {
  aes128_ctr(out,in,in_len,k,n,c);
}
