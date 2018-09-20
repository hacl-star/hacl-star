
#define INTERLEAVE 4
typedef __m128i* state_t;
typedef __m128i key1_t;
typedef __m128i* keyex_t;

static inline void aes_enc(state_t st, key1_t k) {
#pragma unroll
  for (int j = 0; j < INTERLEAVE; j++) 
    st[j] = _mm_aesenc_si128(st[j],k);
}

static inline void aes_enc_last(state_t st, key1_t k) {
#pragma unroll
  for (int j = 0; j < INTERLEAVE; j++)
    st[j] = _mm_aesenclast_si128(st[j],k);
}

static void rounds(state_t st, keyex_t key) {
#pragma unroll
  for (int i = 0; i < 9; i++) 
      aes_enc(st,key[i]);
}

inline static  void addRoundKey(state_t st, key1_t k) {
#pragma unroll
  for (int j = 0; j < INTERLEAVE; j++)
    st[j] = _mm_xor_si128(st[j], k); 
}


static inline void block_cipher(state_t out, keyex_t key) {
  state_t k1 = key + 1;
  addRoundKey(out,key[0]);  
  rounds(out,k1);
  aes_enc_last(out,key[10]);
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

static inline void aes128_block(state_t out,state_t kex, __m128i nvec, uint32_t c) {
#pragma unroll
  for (int i = 0; i < INTERLEAVE; i++)
    out[i] = _mm_insert_epi32(nvec, __builtin_bswap32(c + i), 3);
  block_cipher(out,kex);
}

static void aes128_ctr(uint8_t* out, uint8_t* in, int in_len, uint8_t* k, uint8_t* n, uint32_t c) {
  __m128i kex[11] = {0};
  key_expansion(kex,k);
  int blocksize = 16 * INTERLEAVE;
  __m128i kb[INTERLEAVE] = {0};

  uint8_t tmp_n[16];
  memcpy(tmp_n,n,12);
  __m128i nvec = _mm_loadu_si128((__m128i*) tmp_n);

  int blocks = in_len / blocksize;
  for (int i = 0; i < blocks; i++) {
    aes128_block(kb,kex,nvec,c+(INTERLEAVE*i));
    for (int j = 0; j < INTERLEAVE; j++) {
      _mm_storeu_si128((__m128i*)&out[blocksize*i + 16*j],_mm_xor_si128(kb[j],_mm_loadu_si128((__m128i*)&in[blocksize*i + 16*j])));
    }
  }

  int rem = in_len % blocksize;
  if (rem > 0) {
    in = in + (blocksize * blocks);
    out = out + (blocksize * blocks);
    c = c + (INTERLEAVE * blocks);
    aes128_block(kb,kex,nvec,c);
    uint8_t tmp[blocksize];
    for (int i = 0; i < INTERLEAVE; i++)
      _mm_storeu_si128((__m128i*)&tmp[16*i],kb[i]);
    for (int j = 0; j < rem; j++) {
      out[j] = in[j] ^ tmp[j];
    }
  }
      
}

void aes128_encrypt(uint8_t* out, uint8_t* in, int in_len, uint8_t* k, uint8_t* n, uint32_t c) {
  aes128_ctr(out,in,in_len,k,n,c);
}

void aes128_decrypt(uint8_t* out, uint8_t* in, int in_len, uint8_t* k, uint8_t* n, uint32_t c) {
  aes128_ctr(out,in,in_len,k,n,c);
}
